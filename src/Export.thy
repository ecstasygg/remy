theory Export
  imports Examples Delivery
begin

definition ascii :: "integer \<Rightarrow> char" where "ascii = char_of"

definition ordinal :: "char \<Rightarrow> integer" where "ordinal = of_char"

export_code validate disassemble configured artifact baseline vectors reference simulate delivery ascii ordinal in SML module_name Remy file_prefix remy

end
