fun say m = print (m ^ "\n")

structure AST =
struct
    datatype atom = Number of real | Lambda of symbol list * sexp
         and sexp_element = SEAtom of atom
                          | SESymbol of string
                          | SESexp of sexp
         and sexp = Sexp of sexp_element list
    type program = sexp list

    fun atomToString (atom: atom): string =
        case atom
         of Number x => Real.toString x
          | Lambda (args, body) =>
            String.concat ["(lambda ",
                           "(", String.concatWith " " args, ")",
                           " ",
                           sexpToString body]
    and sexpElementToString (element: sexp_element): string =
        case element
         of SEAtom atom => atomToString atom
          | SESymbol symbol => symbol
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
          | NONE => Token of tokenString

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


    fun parseToken (token: string): AST.atom =
        if token = "+"
        then AST.Symbol AST.Add
        else if token = "-"
        then AST.Symbol AST.Subtract
        else if token = "*"
        then AST.Symbol AST.Multiply
        else if token = "/"
        then AST.Symbol AST.Divide
        else AST.Number ((valOf o Int.fromString) token)

    fun parseSexpElements (tokens: Lex.token list):
        AST.sexp_element list * string list =
        case tokens
         of Open::Lambda:: =>
          | Open::_ =>
            let
                val (subsexp, tokens') = parseSexp tokens
                val element = AST.SESexp subsexp
                val (rest, tokens'') = parseSexpElements tokens'
            in
                (element::rest, tokens'')
            end
          | Close::tokens' => ([], tokens')
          | (Token t)::tokens' =>
            let
                val atom = AST.A (parseToken token)
                val (rest, tokens'') = parseSexpElements tokens'
            in
                (atom::rest, tokens'')
            end

    and parseSexp (tokens: Lex.token list): AST.sexp * string list =
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

    fun lex

    val parse: Lex.token list -> AST.program = parseProgram
end

structure Context =
struct
    type t = string * AST.atom list

    fun find (ctxs: t list, sym: string): AST.atom =
        case ctxs
         of [] => raise Fail ("Could not find symbol \"" ^ sym ^ "\"")
          | ctx::ctxs' => case List.find (fn candSym => candSym = sym) ctx
                           of NONE => find (ctxs', sym)
                            | SOME atom => atom

    fun push (ctxs: t list, ctx: t) = ctx::ctxs

    val pop: t list -> t * t list option = List.getItem
end

local
    fun evalSymbol (sym: AST.symbol, args: AST.atom list): AST.atom =
        let
            val numbers = List.map (fn AST.Number x => x) args
            val (first, rest) = (hd numbers, tl numbers)
            val operation = case sym
                             of AST.Add => op+
                              | AST.Subtract => (fn (elt, acc) => acc - elt)
                              | AST.Multiply => op*
                              | AST.Divide => (fn (elt, acc) => acc div elt)
        in
            AST.Number (List.foldl operation first rest)
        end

    fun evalSexpElement (element: AST.sexp_element): AST.atom =
        case element
         of AST.A atom => atom
          | AST.S sexp => evalSexp sexp
    and evalSexp (AST.Sexp elements: AST.sexp): AST.atom =
        let
            val reduced = List.map evalSexpElement elements
        in
            case reduced
             of (AST.Symbol sym)::args => evalSymbol (sym, args)
        end
in
    fun eval (s: AST.sexp): int =
        case evalSexp s
         of AST.Number n => n
end



fun repl () =
    let
        val program = (parse o valOf o TextIO.inputLine) TextIO.stdIn
        val _ = say ((Int.toString o eval) program)
    in
        repl ()
    end

val _ = repl ()
