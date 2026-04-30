(* Set up the goal *)
g `!res buf table (inlist:(24 word)list) pc stackpointer.
    LENGTH inlist = 280 /\
    nonoverlapping (word pc, 246) (res, 1024) /\
    nonoverlapping (word pc, 246) (buf, 840) /\
    nonoverlapping (word pc, 246) (table, 2048) /\
    nonoverlapping (res, 1024) (buf, 840) /\
    nonoverlapping (res, 1024) (table, 2048) /\
    nonoverlapping (stackpointer, 8) (res, 1024)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_tmc) /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              C_ARGUMENTS [res; buf; table] s /\
              read(memory :> bytes(buf,840)) s = num_of_wordlist inlist /\
              read(memory :> bytes(table,2048)) s =
                num_of_wordlist(mldsa_rej_uniform_table:byte list))
         (\s. read RIP s = word(pc + 245) /\
              let outlist = SUB_LIST(0,256) (REJ_SAMPLE inlist) in
              let outlen = LENGTH outlist in
              C_RETURN s = word outlen /\
              read(memory :> bytes(res,4 * outlen)) s =
                num_of_wordlist outlist)
         (MAYCHANGE [RSP; RIP; RAX; RCX; R8; R9; R10] ,,
          MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(res,1024)])`;;
Printf.printf "=== GOAL SET ===\n%!";;
