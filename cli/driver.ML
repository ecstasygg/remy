val root = valOf (OS.Process.getEnv "REMY_ROOT");
val _ = use (root ^ "/.build/Remy.Export/code/remy.ML");

fun chars s = map (Remy.ascii o IntInf.fromInt o Char.ord) (String.explode s);
fun text cs = String.implode (map (Char.chr o IntInf.toInt o Remy.ordinal) cs);

fun read path =
  let
    val stream = TextIO.openIn path
    val input = TextIO.inputN (stream, 65537)
      handle exn => (TextIO.closeIn stream; raise exn)
    val _ = TextIO.closeIn stream
  in
    if size input > 65536 then raise Fail "source exceeds 64 KiB" else chars input
  end;

fun write path bytes =
  let
    val stream = BinIO.openOut path
  in
    (BinIO.output (stream, Byte.stringToBytes (text bytes)); BinIO.closeOut stream)
      handle exn => ((BinIO.closeOut stream handle _ => ()); raise exn)
  end;

fun output (ok, message) =
  (TextIO.output (if ok then TextIO.stdOut else TextIO.stdErr, text message);
   if ok then () else OS.Process.exit OS.Process.failure);

fun emit destination ((ok, bytes), report) =
  if ok then (write destination bytes; output (true,report)) else output (false,report);

fun main () =
  (case CommandLine.arguments () of
    ["vectors", source, destination] =>
      (case Remy.vectors (read source) of (true, bytes) => write destination bytes | result => output result)
  | ["eval", source, x, y, t] => output (Remy.reference (read source) (chars x) (chars y) (chars t))
  | ["limits", depth, nodes, stack, source, destination] =>
      emit destination (Remy.configured (chars depth) (chars nodes) (chars stack) (read source))
  | ["disassemble", binary] => output (Remy.disassemble (read binary))
  | [source, destination] => emit destination (Remy.artifact (read source))
  | _ => raise Fail "usage: remy disassemble binary | remy limits depth nodes stack source binary | remy source binary | remy vectors source data | remy eval source x y t")
  handle exn =>
    (TextIO.output (TextIO.stdErr, "remy: " ^ General.exnMessage exn ^ "\n");
     OS.Process.exit OS.Process.failure);
