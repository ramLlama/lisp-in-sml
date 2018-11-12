fun say m = print (m ^ "\n")

structure AST =
struct
    datatype symbol = Add | Subtract | Multiply | Divide
    datatype atom = Number of int | Symbol of symbol
    datatype sexp_element = A of atom | S of sexp
         and sexp = Sexp of sexp_element list
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

local
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

    fun parseSexpElements (tokens: string list): AST.sexp_element list * string list =
        case tokens
         of ")"::tokens' => ([], tokens')
          | "("::tokens' =>
            let
                val (subsexp, tokens'') = parseSexp tokens
                val atom = AST.S subsexp
                val (rest, tokens''') = parseSexpElements tokens''
            in
                (atom::rest, tokens''')
            end
          | token::tokens' =>
            let
                val atom = AST.A (parseToken token)
                val (rest, tokens'') = parseSexpElements tokens'
            in
                (atom::rest, tokens'')
            end

    and parseSexp (tokens: string list): AST.sexp * string list =
        case tokens
         of [] => (AST.Sexp [], nil)
          | "("::tokens' =>
            let
                val (elements, tokens'') = parseSexpElements tokens'
            in
                (AST.Sexp elements, tokens'')
            end
in
    fun parse (source: string): AST.sexp =
        let
            val spacified = String.translate (fn c =>
                                                 case c
                                                  of #"(" => " ( "
                                                   | #")" => " ) "
                                                   | _ => String.str c)
                                             source
            val tokens = String.tokens (Char.contains " \n") spacified
                                       (* val _ = List.app say tokens *)
        in
            #1 (parseSexp tokens)
        end
end

fun repl () =
    let
        val program = (parse o valOf o TextIO.inputLine) TextIO.stdIn
        val _ = say ((Int.toString o eval) program)
    in
        repl ()
    end

val _ = repl ()
