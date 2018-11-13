fun say m = print (m ^ "\n")

structure AST =
struct
  (**
   * atom      ::= n | sym | lambda (sym, ..., sym) sexp
   * primop    ::= + | - | * | / | eq | lt | nand
   * sexp-elem ::= atom | sexp
   * sexp      ::= (sexp-elem, ..., sexp-elem)
   * program   ::= sexp, ..., sexp
   *)
  type symbol = string
  datatype atom = Number of real
                | Symbol of symbol
                | Lambda of symbol list * sexp
       and sexp_element = SEAtom of atom
                        | SESexp of sexp
       and sexp = Sexp of sexp_element list
  type program = sexp list

  fun atomToString (atom: atom): string =
      case atom
       of Number x => Real.toString x
        | Symbol symbol => symbol
        | Lambda (params, body) =>
          String.concat ["(lambda ",
                         "(", String.concatWith " " params, ")",
                         " ",
                         sexpToString body,
                         ")"]
  and sexpElementToString (element: sexp_element): string =
      case element
       of SEAtom atom => atomToString atom
        | SESexp sexp => sexpToString sexp
  and sexpToString (Sexp elements: sexp): string =
      let
        val elementsString =
            String.concatWith " " (List.map sexpElementToString elements)
      in
        String.concat ["(", elementsString, ")"]
      end

  fun programToString (sexps: program): string =
      String.concatWith "\n" (List.map sexpToString sexps)
end

structure Lex:
          sig
            datatype keyword = Lambda | Add | Subtract | Multiply | Divide
            datatype token = Open
                           | Close
                           | Keyword of keyword
                           | Token of string
            val lex: string -> token list
          end =
struct
  datatype keyword = Lambda | Add | Subtract | Multiply | Divide
  datatype token = Open | Close | Keyword of keyword | Token of string

  val keywordMap = [("(", Open),
                    (")", Close),
                    ("lambda", Keyword Lambda)]

  fun stringToToken (tokenString: string): token =
      case List.find (fn (keyword, _) => keyword = tokenString) keywordMap
       of SOME (_, token) => token
        | NONE => Token tokenString

  fun lex (source: string): token list =
      let
        val spacified = String.translate (fn c =>
                                             case c
                                              of #"(" => " ( "
                                               | #")" => " ) "
                                               | _ => String.str c)
                                         source
        val rawTokens = String.tokens (Char.contains " \n") spacified
      in
        List.map stringToToken rawTokens
      end
end

structure Parse: sig val parse: Lex.token list -> AST.program end =
struct
  fun parseToken (Lex.Token token: Lex.token): AST.atom =
      case Real.fromString token
       of SOME number => AST.Number number
        | NONE => AST.Symbol token

  fun parseParams (tokens: Lex.token list):
      AST.symbol list * Lex.token list =
      case tokens
       of Lex.Open::tokens' => parseParams tokens'
        | Lex.Close::tokens' => ([], tokens')
        | token::tokens' =>
          let
            val atom = parseToken token
            val symbol = case atom
                          of AST.Symbol symbol => symbol
                           | _ => raise Fail ((AST.atomToString atom) ^
                                              " is a number not a symbol.")
            val (rest, tokens'') = parseParams tokens'
          in
            (symbol::rest, tokens'')
          end

  fun parseLambda (tokens: Lex.token list): AST.atom * Lex.token list =
      case tokens
       of Lex.Open::(Lex.Keyword Lex.Lambda)::tokens' =>
          let
            val (params, bodyTokens) = parseParams tokens'
            val (body, lambdaCloseTokens) = parseSexp bodyTokens
          in
            case lambdaCloseTokens
             of Lex.Close::remainingTokens =>
                (AST.Lambda (params, body), remainingTokens)
          end

  and parseSexpElements (tokens: Lex.token list):
      AST.sexp_element list * Lex.token list =
      case tokens
       of Lex.Close::tokens' => ([], tokens')
        | _ =>
          let
            val (element, tokens') =
                case tokens
                 of Lex.Open::(Lex.Keyword Lex.Lambda)::_ =>
                    let
                      val (lambda, tokens') = parseLambda tokens
                    in
                      (AST.SEAtom lambda, tokens')
                    end
                  | Lex.Open::_ =>
                    let
                      val (subsexp, tokens') = parseSexp tokens
                    in
                      (AST.SESexp subsexp, tokens')
                    end
                  | (token as Lex.Token _)::tokens' =>
                    (AST.SEAtom (parseToken token), tokens')
            val (rest, tokens'') = parseSexpElements tokens'
          in
            (element::rest, tokens'')
          end


  and parseSexp (tokens: Lex.token list): AST.sexp * Lex.token list =
      case tokens
       of [] => (AST.Sexp [], nil)
        | Open::tokens' =>
          let
            val (elements, tokens'') = parseSexpElements tokens'
          in
            (AST.Sexp elements, tokens'')
          end

  fun parseProgram (tokens: Lex.token list): AST.program =
      case tokens
       of [] => []
        | Open::_ =>
          let
            val (sexp, tokens') = parseSexp tokens
          in
            sexp::(parseProgram tokens')
          end

  val parse: Lex.token list -> AST.program = parseProgram
end

structure Context =
struct
  type 'a t = (string * 'a) list

  fun make (symbols: string list, values: 'a list): 'a t =
      case (symbols, values)
       of ([], []) => []
        | (_, []) => raise Fail "More symbols than values"
        | ([], _) => raise Fail "More values than symbols"
        | (symbol::symbols', value::values') =>
          (symbol, value)::(make (symbols', values'))

  fun find (ctxs: 'a t list, sym: string): 'a =
      case ctxs
       of [] => raise Fail ("Could not find symbol \"" ^ sym ^ "\"")
        | ctx::ctxs' => case List.find (fn (candSym, _) => candSym = sym) ctx
                         of NONE => find (ctxs', sym)
                          | SOME (_, binding) => binding

  fun push (ctxs: 'a t list, ctx: 'a t) = ctx::ctxs
end

structure Evaluate:
          sig
            type value
            val eval: AST.program -> value list
            val valueToString: value -> string
          end =
struct
  (**
   * ## Dynamics
   * N.B. Ctx is a binding-value mapping, not a type context like usual.
   *
   * atom:
   * -
   * --------
   * Ctx |- n val
   *
   *
   * -
   * ---------
   * Ctx |- lambda val
   *
   *
   * sym \in Ctx
   * ------------------------------
   * Ctx |- sym --> Ctx |- Ctx[sym]
   *
   *
   * sexp:
   * Ctx |- s_i --> s_i'
   * --------------------------------------------
   * Ctx |- (s_0 ... s_n) --> (s_0' ... s_n')
   *
   *
   * Ctx |- (a_0)
   * ------------
   * Ctx |- (a_0) --> a_0
   *
   *
   * Ctx |- (a_0 ... a_n)    a_1: lambda (param_1 ... param_n) body
   * ----------------------------------------------------------
   * Ctx |-  (a_0 ... a_n) --> Ctx, param_i = a_i |- body
   *
   *
   * program :
   * - |- s_i --> s_i'
   * ------------------------------------------
   * - |- [s_0, ..., s_n] --> [s_0', ..., s_n']
   *
   *
   * -
   * ------------------------
   * - |- [a_0, ..., a_n] val
   *)

  datatype prim = Add
                | Subtract
                | Multiply
                | Divide
                | Equal
                | Lesser
                | Nand

  datatype value = Number of real
                 | Lambda of AST.symbol list * AST.sexp
                 | Prim of prim

  val trueValue = Number 1.0
  val falseValue = Number 0.0

  fun primToString (prim: prim): string =
      case prim
       of Add => "+"
        | Subtract => "-"
        | Multiply => "*"
        | Divide => "/"
        | Equal => "eq"
        | Lesser => "<"
        | Nand => "nand"

  fun valueToString (value: value): string =
      case value
       of Number n => Real.toString n
        | Lambda (params, body) =>
          String.concat ["(lambda ",
                         "(", String.concatWith " " params, ")",
                         " ",
                         AST.sexpToString body,
                         ")"]
        | Prim prim => primToString prim

  fun numberOf (value: value): real =
      case value
       of Number n => n
        | _ => raise Fail ((valueToString value) ^ " is not a number")

  fun evalArith (primop: real * real -> real)
                (prim: prim)
                (args: value list): value =
      case List.map numberOf args
         of [] => raise Fail ("Applied prim " ^
                              (primToString prim) ^
                              " to zero arguments")
          | first::rest => Number (List.foldl primop first rest)

  fun evalEq (prim: prim) (args: value list): value =
      case args
       of [] => trueValue
        | first::rest =>
          let
            fun equal value =
                case (first, value)
                 of (Number n1, Number n2) => Real.==(n1, n2)
                  | _  => false
          in
            if List.all equal rest
            then trueValue
            else falseValue
          end

  fun evalLt (prim: prim) (args: value list): value =
      let
        fun ltFolder (value: value,
                      (previous: real, result: bool)): real * bool =
            if result
            then case value
                  of Number n => (n, Real.<(previous, n))
                   | _ => (previous, false)
            else (previous, result)
      in
        case args
         of [] => trueValue
          | first::rest =>
            let
              val (_, result) =
                  List.foldl ltFolder (numberOf first, true) rest
            in
              if result
              then trueValue
              else falseValue
            end
      end

  fun evalNand (prim: prim) (args: value list): value =
      let
        fun andFolder (value: value, acc: bool): bool =
            case value
             of Number n => acc andalso (not (Real.== (n, 0.0)))
              | _ => false
      in
        if not (List.foldl andFolder true args)
        then trueValue
        else falseValue
      end

  val primDefinitions: (prim * (prim -> value list -> value)) list =
      [(Add, evalArith Real.+),
       (Subtract, evalArith (fn (elt, acc) => Real.- (acc, elt))),
       (Multiply, evalArith Real.* ),
       (Divide, evalArith (fn (elt, acc) => Real./ (acc, elt))),
       (Equal, evalEq),
       (Lesser, evalLt),
       (Nand , evalNand)]

  fun evalPrim (prim: prim) (args: value list): value =
      case List.find (fn (candPrim, _) => candPrim = prim) primDefinitions
       of NONE => raise Fail ("No definition for prim " ^ (primToString prim))
        | SOME (_, f) => f prim args

  fun evalAtom (ctxs: value Context.t list)
               (atom: AST.atom): value =
      case atom
       of AST.Number n => Number n
        | AST.Symbol symbol => Context.find (ctxs, symbol)
        | AST.Lambda (params, body) => Lambda (params, body)

  fun evalSexpElement (ctxs: value Context.t list)
                      (element: AST.sexp_element): value =
      case element
       of AST.SEAtom atom => evalAtom ctxs atom
        | AST.SESexp sexp => evalSexp ctxs sexp

  and evalSexp (ctxs: value Context.t list)
               (sexp as AST.Sexp elements: AST.sexp): value =
      let
        val reducedElements = List.map (evalSexpElement ctxs) elements
      in
        case reducedElements
         of [value] => value
          | (Lambda (params, body))::args =>
            let
              val ctx = Context.make (params, args)
            in
              evalSexp (Context.push (ctxs, ctx)) body
            end
          | (Prim prim)::args => evalPrim prim args
          | _ =>
            raise Fail ((AST.sexpToString sexp) ^ " is not a function call!!")
      end


  val baseContext = [("+", Prim Add),
                     ("-", Prim Subtract),
                     ("*", Prim Multiply),
                     ("/", Prim Divide),
                     ("eq", Prim Equal),
                     ("<", Prim Lesser),
                     ("nand", Prim Nand)]
  local
    val sexp = AST.Sexp
    val symatom = AST.SEAtom o AST.Symbol
    val sexpse = AST.SESexp o sexp
  in
    (* (defun not (x) (nand x)) *)
    val notSexp =
        Lambda (["x"],
                sexp [symatom "nand",
                      symatom "x"])
    val baseContext = ("not", notSexp)::baseContext

    (* (defun and (x y) (not (nand x y))) *)
    val andSexp =
        Lambda (["x", "y"],
                sexp [symatom "not",
                      sexpse [symatom "nand", symatom "x", symatom "y"]])
    val baseContext = ("and", andSexp)::baseContext

    (* (defun or (x y) (not (and (not x) (not y)))) *)
    val orSexp =
        Lambda (["x", "y"],
                sexp [symatom "not",
                      sexpse [symatom "and",
                              sexpse [symatom "not",
                                      symatom "x"],
                              sexpse [symatom "not",
                                      symatom "y"]]])
    val baseContext = ("or", orSexp)::baseContext

    (* (defun > (x y) (and (not (< x y)) (not (eq x y)))) *)
    val gtSexp =
        Lambda (["x", "y"],
                sexp [symatom "and",
                      sexpse [symatom "not",
                              sexpse [symatom "<",
                                      symatom "x",
                                      symatom "y"]],
                      sexpse [symatom "not",
                              sexpse [symatom "eq",
                                      symatom "x",
                                      symatom "y"]]])
    val baseContext = (">", gtSexp)::baseContext
  end

  fun eval (program: AST.program): value list =
      List.map (evalSexp [baseContext]) program
end

fun repl (printParse: bool) =
    let
      val program =
          (Parse.parse o Lex.lex o valOf o TextIO.inputLine) TextIO.stdIn
      val _ = if printParse
              then say ("Parsed to:\n" ^ (AST.programToString program))
              else ()

      val result = Evaluate.eval program
      val _ = say (String.concatWith "\n"
                                     (List.map Evaluate.valueToString
                                               result))
    in
      repl printParse
    end

local
    val argvs = CommandLine.arguments ()
in
    fun optionEnabled option =
        List.exists (fn argv => argv = ("--" ^ option)) argvs
end

val _ = repl (optionEnabled "print-parse")
