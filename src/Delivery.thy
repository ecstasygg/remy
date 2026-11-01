theory Delivery
  imports Frontend
begin

definition checksum :: "nat list \<Rightarrow> pixel" where
  "checksum bytes = foldl (\<lambda>h b. (h XOR word_of_nat b) * 1099511628211) 14695981039346656037 bytes"

definition delivery :: "string \<Rightarrow> string \<Rightarrow> (bool \<times> string) \<times> string" where
  "delivery sequence source = (case (number sequence,prepare source) of
    (Some revision,Some e) \<Rightarrow>
      let emitted = artifact source; code = map nat_of_char (snd (fst emitted));
        data = code @ map nat_of_char source @ concat (map (row e) [0..<512]);
        header = [82,77,89,49] @ octets 4 (length code) @ octets 4 (length source) @
          octets 4 512 @ octets 4 revision in
      if fst (fst emitted) \<and> revision < 2 ^ 32 \<and> 0 < revision \<and>
        length code \<le> 65536 \<and> length source \<le> 65536
      then ((True,map char_of_nat (header @ octets 8 (unat (checksum (header @ data))) @ data)),snd emitted)
      else ((False,[]),''invalid live payload limits'' @ newline)
    | (_,None) \<Rightarrow> ((False,[]),source_error source)
    | _ \<Rightarrow> ((False,[]),''invalid live revision'' @ newline))"

lemma checksum_empty: "checksum [] = 14695981039346656037"
  by (simp add: checksum_def)

lemma checksum_step:
  "checksum (bytes @ [b]) = (checksum bytes XOR word_of_nat b) * 1099511628211"
  by (simp add: checksum_def foldl_append)


lemma row_size [simp]: "length (row e i) = 32"
  by (simp add: row_def)

lemma rows_size [simp]: "length (concat (map (row e) xs)) = 32 * length xs"
  by (induction xs) auto

theorem delivery_bounds:
  "delivery sequence source = ((True,packet),report) \<Longrightarrow>
    16412 \<le> length packet \<and> length packet \<le> 147484"
  by (auto simp: delivery_def Let_def split: option.splits if_splits; linarith)

end
