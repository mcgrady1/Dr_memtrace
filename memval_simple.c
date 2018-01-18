/* ******************************************************************************
 * Copyright (c) 2017 Google, Inc.  All rights reserved.
 * ******************************************************************************/

/*
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * * Neither the name of VMware, Inc. nor the names of its contributors may be
 *   used to endorse or promote products derived from this software without
 *   specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL VMWARE, INC. OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
 * DAMAGE.
 */

/* Code Manipulation API Sample:
 * memval_simple.c
 *
 * Records and dumps app write addresses, and their corresponding written values.
 *
 * (1) It fills two per-thread-buffers with inlined instrumentation.
 * (2) Once the buffers have been filled up, a fault handler will redirect execution
 *     to our trace buffer handler, where we dump the memrefs to disk.
 *
 * This sample illustrates
 * - inserting instrumentation after the current instruction to read the value
 *   written by it,
 * - the use of drutil_expand_rep_string() to expand string loops to obtain
 *   every memory reference,
 * - the use of drutil_opnd_mem_size_in_bytes() to obtain the size of OP_enter
 *   memory references,
 * - the use of drutil_insert_get_mem_addr() to insert instructions to compute
 *   the address of each memory reference,
 * - the use of the drx_buf extension to fill buffers in a platform-independent
 *   manner
 *
 * This client is a simple implementation of a memory reference tracing tool
 * without instrumentation optimization.
 */

#include <stddef.h> /* for offsetof */
#include "dr_api.h"
#include "drmgr.h"
#include "drutil.h"
#include "drreg.h"
#include "utils.h"
#include "drx.h"
#include <string.h>

/* We opt to use two buffers -- one to hold only mem_ref_t structs, and another to hold
 * the raw bytes written. This is done for simplicity, as we will never get a partial
 * write to the trace buffer (holding mem_ref_t's), which simplifies the handler logic.
 */
typedef struct _mem_ref_t {
    ushort write; /* mem write or read */
    ushort size;  /* mem ref size */
    ushort type;  /* instr opcode */
    ushort instr_size; /* size of instr */
    app_pc pc  ;
    app_pc addr;  /* mem ref addr */
} mem_ref_t;

/* Max number of mem_ref a buffer can have. */
#define MAX_NUM_MEM_REFS 4096
/* The maximum size of buffer for holding mem_refs. */
#define MEM_BUF_SIZE (sizeof(mem_ref_t) * MAX_NUM_MEM_REFS)
/* The maximum size of buffer for holding writes. Writes on average don't get too large,
 * but we give ourselves some leeway and say chains of consecutive writes are on average
 * less than 32 bytes each.
 */
#define WRT_BUF_SIZE (MAX_NUM_MEM_REFS * 32)

#define MINSERT instrlist_meta_preinsert

/* thread private log file and across-app-inst register */
typedef struct {
    file_t     log;
    FILE      *logf;
    reg_id_t   reg_addr;
} per_thread_t;

static client_id_t client_id;
static int         tls_idx;
static drx_buf_t  *write_buffer;
static drx_buf_t  *trace_buffer;

static unsigned int ms = 0;
static unsigned int me = 0;

/* filter rep instruction */
// static bool
// opc_is_stringop_loop(uint opc)
// {
//     return (opc == OP_rep_ins || opc == OP_rep_outs || opc == OP_rep_movs ||
//             opc == OP_rep_stos || opc == OP_rep_lods || opc == OP_rep_cmps ||
//             opc == OP_repne_cmps || opc == OP_rep_scas || opc == OP_repne_scas);
// }

/* Get baseaddress of module */
static void
event_module_load(void *drcontext, const module_data_t *info, bool loaded) {

    const char *module_name = dr_module_preferred_name(info);
    per_thread_t *data = drmgr_get_tls_field(drcontext, tls_idx);

    if (module_name == NULL) {
        fprintf(data->logf, "[MODUL] Module_Loaded_Fault \n");
        return;
    }

    // dr_printf("[MODUL] mn:%s ms:0x%08x me:0x%08x\n", 
    //         module_name, (ptr_uint_t)info->start, (ptr_uint_t)info->end);

    fprintf(data->logf, "[MODUL] mn:%s ms:0x%08x me:0x%08x\n", 
            module_name, (ptr_uint_t)info->start, (ptr_uint_t)info->end);
    if ((ptr_uint_t)info->start == 0x8048000) {
        ms = (ptr_uint_t)info->start;
        me = (ptr_uint_t)info->end;
    }
}

/* Requires that hex_buf be at least as long as 2*memref->size + 1. */
static char *
write_hexdump(char *hex_buf, byte *write_base, mem_ref_t *mem_ref, int isopcode)
{
    int i;
    char *hexstring = hex_buf, *needle = hex_buf;
    
    if (!isopcode) {
        for (i = mem_ref->size - 1; i >= 0; --i) {
            needle += dr_snprintf(needle, 2*mem_ref->size+1-(needle-hex_buf),
                                  "%02x", write_base[i]);
        }

    }
    else {

        for (i = 0; i < mem_ref->instr_size; i++) {
            needle += dr_snprintf(needle, 2*mem_ref->instr_size+1-(needle-hex_buf),
                                  "%02x", write_base[i]);
        }

    }

    return hexstring;
    
}

/* Called when the trace buffer has filled up, and needs to be flushed to disk. */
static void
trace_fault(void *drcontext, void *buf_base, size_t size)
{
    per_thread_t *data = drmgr_get_tls_field(drcontext, tls_idx);
    mem_ref_t *trace_base = (mem_ref_t *)(char *)buf_base;
    mem_ref_t *trace_ptr  = (mem_ref_t *)((char *)buf_base + size);
    byte *write_base = drx_buf_get_buffer_base(drcontext, write_buffer);
    byte *write_ptr  = drx_buf_get_buffer_ptr (drcontext, write_buffer);
    int largest_size = 0;
    int largest_instr_size = 0;
    mem_ref_t *mem_ref;
    char *hex_buf;
    // char *opcode_buf;

    /* find the largest necessary buffer so we only perform a single allocation */
    for (mem_ref = trace_base; mem_ref < trace_ptr; mem_ref++) {
        if (mem_ref->size > largest_size)
            largest_size = mem_ref->size;
        if (mem_ref->instr_size > largest_instr_size)
            largest_instr_size = mem_ref->instr_size;
    }

    if (largest_size < largest_instr_size) largest_size = largest_instr_size;

    hex_buf = dr_thread_alloc(drcontext, 2*largest_size+1);
    // opcode_buf = dr_thread_alloc(drcontext, 2*largest_instr_size+1);
    /* write the memrefs to disk */
    for (mem_ref = trace_base; mem_ref < trace_ptr; mem_ref++) {
        /* Each memref in the trace buffer has an "associated" write in the write buffer.
         * We pull mem_ref->size bytes from the write buffer, and assert we haven't yet
         * gone too far.
         */
        /* We use libc's fprintf as it is buffered and much faster than dr_fprintf for
         * repeated printing that dominates performance, as the printing does here. Note
         * that a binary dump is *much* faster than fprintf still.
         */

        if (mem_ref->write == 1) {
            fprintf(data->logf, PFX" %d %s %1d "PFX" %s %d ",
                    (ptr_uint_t)mem_ref->pc, mem_ref->instr_size, 
                    write_hexdump(hex_buf, (byte *)mem_ref->pc, mem_ref, 1),
                    mem_ref->write,
                    (ptr_uint_t)mem_ref->addr, decode_opcode_name(mem_ref->type),
                    mem_ref->size);
            fprintf(data->logf, "%s\n", write_hexdump(hex_buf, write_base, mem_ref, 0));
            fflush(stdout);
            write_base += mem_ref->size;
            DR_ASSERT(write_base <= write_ptr);
        }
        else {
            fprintf(data->logf, PFX" %d %s %1d "PFX" %s %d ",
                    (ptr_uint_t)mem_ref->pc, mem_ref->instr_size, 
                    write_hexdump(hex_buf, (byte *)mem_ref->pc, mem_ref, 1),
                    mem_ref->write,
                    (ptr_uint_t)mem_ref->addr, decode_opcode_name(mem_ref->type),
                    mem_ref->size);
            if (mem_ref->size > 0) {
                fprintf(data->logf, "%s\n", write_hexdump(hex_buf, write_base, mem_ref, 0));
                write_base += mem_ref->size;
            }
            else
                fprintf(data->logf, "0\n");
            fflush(stdout);
        }

        fflush(stdout);

    }
    dr_thread_free(drcontext, hex_buf, 2*largest_size+1);
    // dr_thread_free(drcontext, opcode_buf, 2*largest_size+1);
    /* reset the write buffer (note: the trace buffer gets reset automatically) */
    drx_buf_set_buffer_ptr(drcontext, write_buffer,
                           drx_buf_get_buffer_base(drcontext, write_buffer));
}

static reg_id_t
instrument_mem(void *drcontext, instrlist_t *ilist, instr_t *where, opnd_t ref,bool ismem, bool iswrite)
{
    reg_id_t reg_ptr, reg_tmp, reg_addr;
    ushort type, size, write, instr_size;
    bool ok;
    app_pc pc;

    if (iswrite == true) write = 1;
    else write = 0;

    if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_tmp)
        != DRREG_SUCCESS) {
        DR_ASSERT(false);
        return DR_REG_NULL;
    }
    if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_ptr)
        != DRREG_SUCCESS) {
        DR_ASSERT(false);
        return DR_REG_NULL;
    }

    /* i#2449: In the situation that instrument_post_write, instrument_mem and ref all
     * have the same register reserved, drutil_insert_get_mem_addr will compute the
     * address of an operand using an incorrect register value, as drreg will elide the
     * save/restore.
     */

    // dr_printf("0x%08x %s\n", instr_get_app_pc(where), decode_opcode_name(instr_get_opcode(where)));

    // dr_printf("condition %d\n", opnd_uses_reg(ref, reg_tmp));
    // dr_printf("condition %d\n", drreg_get_app_value(drcontext, ilist, where, reg_tmp, reg_tmp) != DRREG_SUCCESS);

    if (ismem) {
        if (opnd_uses_reg(ref, reg_tmp) &&
            drreg_get_app_value(drcontext, ilist, where, reg_tmp, reg_tmp)
            != DRREG_SUCCESS) {
            DR_ASSERT(false);
            return DR_REG_NULL;
        }
        if (opnd_uses_reg(ref, reg_ptr) &&
            drreg_get_app_value(drcontext, ilist, where, reg_ptr, reg_ptr)
            != DRREG_SUCCESS) {
            DR_ASSERT(false);
            return DR_REG_NULL;
        }
    }

    /* We use reg_ptr as scratch to get addr. Note we do this first as reg_ptr or reg_tmp
     * may be used in ref.
     */

    if (ismem == true) {
        ok = drutil_insert_get_mem_addr(drcontext, ilist, where, ref, reg_tmp, reg_ptr);
        DR_ASSERT(ok);
    }
    
    drx_buf_insert_load_buf_ptr(drcontext, trace_buffer, ilist, where, reg_ptr);

    /* inserts pc */
    pc = instr_get_app_pc(where);
    drx_buf_insert_buf_store(drcontext, trace_buffer, ilist, where, reg_ptr, DR_REG_NULL, 
                             OPND_CREATE_INTPTR((ptr_int_t)pc), OPSZ_PTR, 
                             offsetof(mem_ref_t, pc));

    if (ismem == true)
        /* inserts memref addr */
        drx_buf_insert_buf_store(drcontext, trace_buffer, ilist, where, reg_ptr, DR_REG_NULL,
                                 opnd_create_reg(reg_tmp), OPSZ_PTR,
                                 offsetof(mem_ref_t, addr));
    else
        drx_buf_insert_buf_store(drcontext, trace_buffer, ilist, where, reg_ptr, DR_REG_NULL, 
                                 OPND_CREATE_INTPTR((ptr_int_t)instr_get_app_pc(where)), OPSZ_PTR,
                                 offsetof(mem_ref_t, addr));

    if (IF_AARCHXX_ELSE(true, false)) {
        /* At this point we save the write address for later, because reg_tmp's value
         * will get clobbered on ARM.
         */
        if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_addr)
            != DRREG_SUCCESS) {
            DR_ASSERT(false);
            return DR_REG_NULL;
        }
        MINSERT(ilist, where, XINST_CREATE_move
                (drcontext,
                 opnd_create_reg(reg_addr),
                 opnd_create_reg(reg_tmp)));
    }
    /* inserts write */
    drx_buf_insert_buf_store(drcontext, trace_buffer, ilist, where, reg_ptr, reg_tmp,
                             OPND_CREATE_INT16(write), OPSZ_2, offsetof(mem_ref_t, write));

    /* inserts type */
    type = (ushort)instr_get_opcode(where);
    drx_buf_insert_buf_store(drcontext, trace_buffer, ilist, where, reg_ptr, reg_tmp,
                             OPND_CREATE_INT16(type), OPSZ_2, offsetof(mem_ref_t, type));

    /* insert inst_size */
    instr_size = (ushort)instr_length(drcontext, where);
    drx_buf_insert_buf_store(drcontext, trace_buffer, ilist, where, reg_ptr, reg_tmp,
                             OPND_CREATE_INT16(instr_size), OPSZ_2, offsetof(mem_ref_t, instr_size));

    /* inserts size */
    if (ismem == true) {
        size = (ushort)drutil_opnd_mem_size_in_bytes(ref, where);
        
    }
    else {
        size = 0;
    }
    drx_buf_insert_buf_store(drcontext, trace_buffer, ilist, where, reg_ptr, reg_tmp,
                                  OPND_CREATE_INT16(size), OPSZ_2, offsetof(mem_ref_t, size));
    
    drx_buf_insert_update_buf_ptr(drcontext, trace_buffer, ilist, where, reg_ptr,
                                  DR_REG_NULL, sizeof(mem_ref_t));

    if (write == 1) {
        if (instr_is_call(where)) {
            

            /* Note that on ARM the call instruction writes only to the link register, so
             * we would never even get into instrument_mem() on ARM if this was a call.
             */
            IF_AARCHXX(DR_ASSERT(false));
            /* We simulate the call instruction's written memory by writing the next app_pc
             * to the written buffer, since we can't do this after the call has happened.
             */
            drx_buf_insert_load_buf_ptr(drcontext, write_buffer, ilist, where, reg_ptr);
            pc = decode_next_pc(drcontext, instr_get_app_pc(where));
            /* note that for a circular buffer, we don't need to specify a scratch register */
            drx_buf_insert_buf_store(drcontext, trace_buffer, ilist, where, reg_ptr,
                                     DR_REG_NULL, OPND_CREATE_INTPTR((ptr_int_t)pc),
                                     OPSZ_PTR, 0);
            drx_buf_insert_update_buf_ptr(drcontext, write_buffer, ilist, where,
                                          reg_ptr, reg_tmp, sizeof(app_pc));
            /* we don't need to persist reg_tmp to the next instruction */
           
            if (drreg_unreserve_register(drcontext, ilist, where, reg_tmp) != DRREG_SUCCESS)
                DR_ASSERT(false);
            reg_tmp = DR_REG_NULL;
        } else if (IF_AARCHXX_ELSE(true, false)) {
            /* Now reg_tmp has the address of the write again. */
            MINSERT(ilist, where, XINST_CREATE_move
                    (drcontext,
                     opnd_create_reg(reg_tmp),
                     opnd_create_reg(reg_addr)));
            if (drreg_unreserve_register(drcontext, ilist, where, reg_addr) != DRREG_SUCCESS)
                DR_ASSERT(false);
        }

        if (drreg_unreserve_register(drcontext, ilist, where, reg_ptr) != DRREG_SUCCESS)
            DR_ASSERT(false);
        return reg_tmp;
    }
    else {
        if (ismem == true) {

            ushort stride = (ushort)drutil_opnd_mem_size_in_bytes(ref, where);

            ok = drutil_insert_get_mem_addr(drcontext, ilist, where, ref, reg_tmp, reg_ptr);
            DR_ASSERT(ok);

            drx_buf_insert_load_buf_ptr(drcontext, write_buffer, ilist, where, reg_ptr);
            /* drx_buf_insert_memcpy() internally updates the buffer pointer */
            drx_buf_insert_buf_memcpy(drcontext, write_buffer, ilist, where, reg_ptr, reg_tmp, stride);

        }
        if (drreg_unreserve_register(drcontext, ilist, where, reg_tmp) != DRREG_SUCCESS)
                DR_ASSERT(false);

        if (drreg_unreserve_register(drcontext, ilist, where, reg_ptr) != DRREG_SUCCESS)
            DR_ASSERT(false);

        return DR_REG_NULL;
    }
}

static void
instrument_post_write(void *drcontext, instrlist_t *ilist, instr_t *where, opnd_t memref,
                      instr_t *write, reg_id_t reg_addr)
{
    reg_id_t reg_ptr;
    ushort stride = (ushort)drutil_opnd_mem_size_in_bytes(memref, write);

    if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_ptr)
        != DRREG_SUCCESS) {
        DR_ASSERT(false);
        return;
    }

    drx_buf_insert_load_buf_ptr(drcontext, write_buffer, ilist, where, reg_ptr);
    /* drx_buf_insert_memcpy() internally updates the buffer pointer */
    drx_buf_insert_buf_memcpy(drcontext, write_buffer, ilist, where, reg_ptr, reg_addr,
                              stride);

    if (drreg_unreserve_register(drcontext, ilist, where, reg_ptr)  != DRREG_SUCCESS)
        DR_ASSERT(false);
    if (drreg_unreserve_register(drcontext, ilist, where, reg_addr) != DRREG_SUCCESS)
        DR_ASSERT(false);
}

static void
handle_post_write(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t reg_addr)
{
    int i;
    instr_t *prev_instr = instr_get_prev_app(where);
    bool seen_memref = false;

    /* XXX: We assume that no write instruction has multiple distinct memory destinations.
     * This way we are able to persist a single register across an app instruction. Note
     * there are instructions which currently do break this assumption, but we punt on
     * this.
     */
    for (i = 0; i < instr_num_dsts(prev_instr); ++i) {
        if (opnd_is_memory_reference(instr_get_dst(prev_instr, i))) {
            DR_ASSERT_MSG(!seen_memref, "Found inst with multiple memory destinations");
            seen_memref = true;
            instrument_post_write(drcontext, ilist, where, instr_get_dst(prev_instr, i),
                                  prev_instr, reg_addr);
        }
    }
}

static dr_emit_flags_t
event_app_analysis(void *drcontext, void *tag, instrlist_t *bb, bool
                   for_trace, bool translating, void **user_data)
{
    per_thread_t *data = drmgr_get_tls_field(drcontext, tls_idx);

    *user_data = (void *)&data->reg_addr;
    /* If we have an outstanding write, that means we did not correctly handle a case
     * where there was a write but no fall-through NOP or terminating instruction in
     * the previous basic block.
     */
    DR_ASSERT(data->reg_addr == DR_REG_NULL);
    return DR_EMIT_DEFAULT;
}

/* For each memory reference app instr, we insert inline code to fill the buffer
 * with an instruction entry and memory reference entries.
 */
static dr_emit_flags_t
event_app_instruction(void *drcontext, void *tag, instrlist_t *bb,
                      instr_t *instr, bool for_trace,
                      bool translating, void *user_data)
{
    int i;
    reg_id_t *reg_next = (reg_id_t *)user_data;
    bool seen_memref = false;
    bool rf = false; //read flag

    /* If the previous instruction was a write, we should handle it. */
    if (*reg_next != DR_REG_NULL)
        handle_post_write(drcontext, bb, instr, *reg_next);

    *reg_next = DR_REG_NULL;

    if (!instr_is_app(instr))
        return DR_EMIT_DEFAULT;

    // if (opc_is_stringop_loop(instr_get_opcode(instr)))
    //     return DR_EMIT_DEFAULT;

    if (instr_reads_memory(instr)) {

        for (i = 0; i < instr_num_srcs(instr); ++i) {
            if (opnd_is_memory_reference(instr_get_src(instr, i))) {
                *reg_next = instrument_mem(drcontext, bb, instr, instr_get_src(instr, i), true, false);
                rf = true;
            }
        }
    }
    
    if (instr_writes_memory(instr)) {
        /* XXX: See above, in handle_post_write(). To simplify the handling of registers, we
         * assume no instruction has multiple distinct memory destination operands.
         */
        for (i = 0; i < instr_num_dsts(instr); ++i) {
            if (opnd_is_memory_reference(instr_get_dst(instr, i))) {
                DR_ASSERT_MSG(!seen_memref, "Found inst with multiple memory destinations");
                *reg_next = instrument_mem(drcontext, bb, instr, instr_get_dst(instr, i), true, true);
                seen_memref = true;
            }
        }
        return DR_EMIT_DEFAULT;
    }

    if (rf == true) return DR_EMIT_DEFAULT;

    if (instr_get_app_pc(instr) != NULL) {
        // if (strstr(decode_opcode_name(instr_get_opcode(instr)),"call") != NULL) {
        //     opnd_t tmp_opnd;
        //     *reg_next = instrument_mem(drcontext, bb, instr, tmp_opnd, false, false);
        //     return DR_EMIT_DEFAULT;
        // }

        // if (strstr(decode_opcode_name(instr_get_opcode(instr)),"ret") != NULL) {
        //     opnd_t tmp_opnd;
        //     *reg_next = instrument_mem(drcontext, bb, instr, tmp_opnd, false, false);
        //     return DR_EMIT_DEFAULT;
        // }

        // if (instr_num_srcs(instr) == 0 && instr_num_dsts(instr) == 0) return DR_EMIT_DEFAULT;
        // // opnd_t tmp_opnd;

        // //dr_printf("0x%08x %s\n", instr_get_app_pc(instr), decode_opcode_name(instr_get_opcode(instr)));
        // if (instr_num_srcs(instr) > 0) {
        //     *reg_next = instrument_mem(drcontext, bb, instr, instr_get_src(instr, 0), false, false);
        //     return DR_EMIT_DEFAULT;
        // }
        // else {
        //     *reg_next = instrument_mem(drcontext, bb, instr, instr_get_dst(instr, 0), false, false);
        //     return DR_EMIT_DEFAULT;
        // }
        

        // app_pc pc = instr_get_app_pc(instr);
        // ushort type = instr_get_opcode(instr);
        // if ((ptr_uint_t)pc < me && (ptr_uint_t)pc > ms && me != 0) {
        //     if (strstr(decode_opcode_name(instr_get_opcode(instr)),"loop") != NULL) {
        //         return DR_EMIT_DEFAULT;
        //     }

        //     printf("%08x, %s, %08x\n", (ptr_uint_t)pc, decode_opcode_name(type), me);
        //     opnd_t tmp_opnd;
        //     *reg_next = instrument_mem(drcontext, bb, instr, tmp_opnd, false, false);
        //     return DR_EMIT_DEFAULT;
        // }

    }

    return DR_EMIT_DEFAULT;
}

/* We transform string loops into regular loops so we can more easily
 * monitor every memory reference they make.
 */
static dr_emit_flags_t
event_bb_app2app(void *drcontext, void *tag, instrlist_t *bb,
                 bool for_trace, bool translating)
{
    if (!drutil_expand_rep_string(drcontext, bb)) {
        DR_ASSERT(false);
        /* in release build, carry on: we'll just miss per-iter refs */
    }

    drx_tail_pad_block(drcontext, bb);
    return DR_EMIT_DEFAULT;
}

static void
event_thread_init(void *drcontext)
{
    per_thread_t *data = dr_thread_alloc(drcontext, sizeof(per_thread_t));
    DR_ASSERT(data != NULL);
    data->reg_addr = DR_REG_NULL;
    drmgr_set_tls_field(drcontext, tls_idx, data);

    /* We're going to dump our data to a per-thread file.
     * On Windows we need an absolute path so we place it in
     * the same directory as our library. We could also pass
     * in a path as a client argument.
     */
    data->log = log_file_open(client_id, drcontext, NULL /* using client lib path */,
                              "memval_simple",
#ifndef WINDOWS
                              DR_FILE_CLOSE_ON_FORK |
#endif
                              DR_FILE_ALLOW_LARGE);
    data->logf = log_stream_from_file(data->log);
}

static void
event_thread_exit(void *drcontext)
{
    per_thread_t *data = drmgr_get_tls_field(drcontext, tls_idx);
    log_stream_close(data->logf);
    dr_thread_free(drcontext, data, sizeof(per_thread_t));
}

static void
event_exit(void)
{
    if (!drmgr_unregister_tls_field(tls_idx) ||
        !drmgr_unregister_thread_init_event(event_thread_init) ||
        !drmgr_unregister_thread_exit_event(event_thread_exit) ||
        !drmgr_unregister_module_load_event(event_module_load) ||
        !drmgr_unregister_bb_app2app_event(event_bb_app2app) ||
        !drmgr_unregister_bb_insertion_event(event_app_instruction))
        DR_ASSERT(false);

    drx_buf_free(write_buffer);
    drx_buf_free(trace_buffer);
    drutil_exit();
    drreg_exit();
    drmgr_exit();
    drx_exit();
}

DR_EXPORT void
dr_client_main(client_id_t id, int argc, const char *argv[])
{
    drreg_options_t ops = {sizeof(ops), 3 /*max slots needed*/, false};

    dr_set_client_name("DynamoRIO Sample Client 'memval_simple'",
                       "http://dynamorio.org/issues");
    if (!drmgr_init() || !drutil_init() || !drx_init())
        DR_ASSERT(false);
    if (drreg_init(&ops) != DRREG_SUCCESS)
        DR_ASSERT(false);

    /* register events */
    dr_register_exit_event(event_exit);
    if (!drmgr_register_thread_init_event(event_thread_init) ||
        !drmgr_register_thread_exit_event(event_thread_exit) ||
        !drmgr_register_module_load_event(event_module_load) ||
        !drmgr_register_bb_app2app_event(event_bb_app2app, NULL) ||
        !drmgr_register_bb_instrumentation_event(event_app_analysis,
                                                 event_app_instruction,
                                                 NULL))
        DR_ASSERT(false);
    client_id = id;

    tls_idx = drmgr_register_tls_field();
    trace_buffer = drx_buf_create_trace_buffer(MEM_BUF_SIZE, trace_fault);
    /* We could make this a trace buffer and specially handle faults, but it is not yet
     * worth the effort.
     */
    write_buffer = drx_buf_create_circular_buffer(WRT_BUF_SIZE);
    DR_ASSERT(tls_idx != -1 && trace_buffer != NULL && write_buffer != NULL);

    /* make it easy to tell, by looking at log file, which client executed */
    dr_log(NULL, LOG_ALL, 1, "Client 'memval_simple' initializing\n");
}
