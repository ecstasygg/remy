val root = valOf (OS.Process.getEnv "REMY_ROOT");
val _ = use (root ^ "/.build/Remy.Export/code/remy.ML");

fun chars s = map (Remy.ascii o IntInf.fromInt o Char.ord) (String.explode s);
fun text cs = String.implode (map (Char.chr o IntInf.toInt o Remy.ordinal) cs);

fun read path =
  let
    val stream = if path = "-" then TextIO.stdIn else TextIO.openIn path
    fun close () = if path = "-" then () else TextIO.closeIn stream
    val input = TextIO.inputN (stream, 65537)
      handle exn => (close (); raise exn)
    val _ = close ()
  in
    if size input > 65536 then raise Fail "source exceeds 64 KiB" else chars input
  end;

fun write path data =
  let
    val bytes = Byte.stringToBytes (text data)
    val pid = SysWord.toString (Posix.Process.pidToWord (Posix.ProcEnv.getpid ()))
    val prefix = OS.Path.concat (OS.Path.dir path, "." ^ OS.Path.file path ^ "." ^ pid ^ ".")
    val defaultMode = Posix.FileSys.S.flags [Posix.FileSys.S.irusr, Posix.FileSys.S.iwusr,
      Posix.FileSys.S.irgrp, Posix.FileSys.S.iwgrp, Posix.FileSys.S.iroth, Posix.FileSys.S.iwoth]
    val mode = Posix.FileSys.S.intersect [Posix.FileSys.ST.mode (Posix.FileSys.stat path),
      Posix.FileSys.S.flags [Posix.FileSys.S.irwxu, Posix.FileSys.S.irwxg, Posix.FileSys.S.irwxo]]
      handle exn as OS.SysErr (_, SOME error) =>
        if error = Posix.Error.noent then defaultMode else raise exn
    fun reserve n =
      if n = 128 then raise Fail "cannot reserve output file"
      else
        let
          val temporary = prefix ^ Int.toString n
        in
          (temporary, Posix.FileSys.createf
            (temporary, Posix.FileSys.O_WRONLY, Posix.FileSys.O.excl, mode))
        end handle exn as OS.SysErr (_, SOME error) =>
          if error = Posix.Error.exist then reserve (n + 1) else raise exn
    val (temporary, fd) = reserve 0
    val closed = ref false
    fun close () = (Posix.IO.close fd; closed := true)
    fun discard () =
      ((if !closed then () else close ()) handle _ => ();
       OS.FileSys.remove temporary handle _ => ())
    fun loop offset =
      if offset = Word8Vector.length bytes then ()
      else
        let
          val count = Posix.IO.writeVec (fd, Word8VectorSlice.slice (bytes, offset, NONE))
        in
          if count = 0 then raise Fail "output write made no progress" else loop (offset + count)
        end
  in
    (loop 0; close (); OS.FileSys.rename {old = temporary, new = path})
      handle exn => (discard (); raise exn)
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
  | ["package", revision, source, destination] =>
      emit destination (Remy.delivery (chars revision) (read source))
  | ["eval", source, x, y, t] => output (Remy.reference (read source) (chars x) (chars y) (chars t))
  | ["simulate", binary, x, y, t] => output (Remy.simulate (read binary) (chars x) (chars y) (chars t))
  | ["limits", depth, nodes, stack, source, destination] =>
      emit destination (Remy.configured (chars depth) (chars nodes) (chars stack) (read source))
  | ["check", binary] => output (Remy.validate (read binary))
  | ["disassemble", binary] => output (Remy.disassemble (read binary))
  | ["baseline", source, destination] => emit destination (Remy.baseline (read source))
  | [source, destination] => emit destination (Remy.artifact (read source))
  | _ => raise Fail "usage: remy check binary | remy disassemble binary | remy simulate binary x y t | remy package revision source packet | remy baseline source binary | remy limits depth nodes stack source binary | remy source binary | remy vectors source data | remy eval source x y t (source - reads standard input)")
  handle exn =>
    (TextIO.output (TextIO.stdErr, "remy: " ^ General.exnMessage exn ^ "\n");
     OS.Process.exit OS.Process.failure);
