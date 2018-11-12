fun say m = print (m ^ "\n")

structure AST =
struct
  (**
   * atom      ::= n | sym |lambda (sym, ..., sym, [*sym]) sexp
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
            datatype token = Open | Close | Lambda | Token of string
            val lex: string -> token list
          end =
struct
  datatype token = Open | Close | Lambda | Token of string

  val keywordMap = [("(", Open),
                    (")", Close),
                    ("lambda", Lambda)]

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
                                      (* val _ = List.app say tokens *)
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
       of Lex.Open::Lex.Lambda::tokens' =>
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
                 of Lex.Open::Lex.Lambda::_ =>
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
  type t = (string * AST.atom) list

  fun find (ctxs: t list, sym: string): AST.atom =
      case ctxs
       of [] => raise Fail ("Could not find symbol \"" ^ sym ^ "\"")
        | ctx::ctxs' => case List.find (fn (candSym, _) => candSym = sym) ctx
                         of NONE => find (ctxs', sym)
                          | SOME (_, atom) => atom

  fun push (ctxs: t list, ctx: t) = ctx::ctxs
end

structure Evaluate: sig val eval: AST.program -> AST.atom list end =
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

  fun bind (params: AST.symbol list, args: AST.atom list): Context.t =
      case (params, args)
       of ([], []) => []
        | (_, []) => raise Fail "More params than args"
        | ([], _) => raise Fail "More args than params"
        | (param::params', arg::args') =>
          (param, arg)::(bind (params', args'))

  fun evalAtom (ctxs: Context.t list)
               (atom: AST.atom): AST.atom =
      case atom
       of AST.Number _ => atom
        | AST.Symbol symbol => evalAtom ctxs (Context.find (ctxs, symbol))
        | AST.Lambda _ => atom

  fun evalSexpElement (ctxs: Context.t list)
                      (element: AST.sexp_element): AST.atom =
      case element
       of AST.SEAtom atom => evalAtom ctxs atom
        | AST.SESexp sexp => evalSexp ctxs sexp

  and evalSexp (ctxs: Context.t list)
               (sexp as AST.Sexp elements: AST.sexp): AST.atom =
      let
        val reducedElements = List.map (evalSexpElement ctxs) elements
      in
        case reducedElements
         of [atom] => evalAtom ctxs atom
          | (AST.Lambda (params, body))::args =>
            let
              val ctx = bind (params, args)
            in
              evalSexp (Context.push (ctxs, ctx)) body
            end
          | _ =>
            raise Fail ((AST.sexpToString sexp) ^ " is not a function call!!")
      end

  fun eval (program: AST.program): AST.atom list =
      List.map (evalSexp []) program
end

fun repl () =
    let
      val program =
          (Parse.parse o Lex.lex o valOf o TextIO.inputLine) TextIO.stdIn
      val _ = say ("Parsed to:\n" ^ (AST.programToString program))

      val result = Evaluate.eval program
      val _ = say ("Evaluated to:\n" ^
                   (String.concatWith "\n"
                                      (List.map AST.atomToString result)))
    in
      repl ()
    end

val _ = repl ()
