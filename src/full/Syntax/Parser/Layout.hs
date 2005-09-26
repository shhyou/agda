{-# OPTIONS -cpp #-}

{-| This module contains the lex actions that handle the layout rules. The way
    it works is that the 'Parser' monad keeps track of a stack of
    'LayoutContext's specifying the indentation of the layout blocks in scope.
    For instance, consider the following incomplete (Haskell) program:

    > f x = x'
    >   where
    >     x' = case x of { True -> ...

    At the @...@ the layout context would be

    > [NoLayout, Layout 4, Layout 0]

    The closest layout block is the one containing the @case@ branches.  This
    block starts with an open brace (@\'{\'@) and so doesn't use layout.  The
    second closest block is the @where@ clause.  Here, there is no open brace
    so the block is started by the @x'@ token which has indentation 4. Finally
    there is a top-level layout block with indentation 0.
-}
module Syntax.Parser.Layout
    ( openBrace, closeBrace
    , withLayout
    , offsideRule
    , newLayoutContext
    , emptyLayout
    ) where

#ifndef __HADDOCK__
import {-# SOURCE #-} Syntax.Parser.Lexer
#endif

import Syntax.Parser.Alex
import Syntax.Parser.Monad
import Syntax.Parser.Tokens
import Syntax.Parser.LexActions
import Syntax.Position

-- | Executed upon lexing an open brace (@\'{\'@). Enters the 'NoLayout'
--   context.
openBrace :: LexAction Token
openBrace = token $ \_ ->
    do	pushContext NoLayout
	r <- getParseRange
	return (TkOpenBrace r)

{-| Executed upon lexing a close brace (@\'}\'@). Exits the current layout
    context. This might look a bit funny--the lexer will happily use a close
    brace to close a context open by a virtual brace. This is not a problem
    since the parser will make sure the braces are appropriately matched.
-}
closeBrace :: LexAction Token
closeBrace = token $ \_ ->
    do	popContext
	r <- getParseRange
	return (TkCloseBrace r)

{-| Executed for layout keywords. Enters the 'Syntax.Parser.Lexer.layout'
    state and performs the given action.
-}
withLayout :: LexAction r -> LexAction r
withLayout a i1 i2 n =
    do	pushLexState layout
	a i1 i2 n

{-| Executed for the first token in each line (see 'Syntax.Parser.Lexer.bol').
    Checks the position of the token relative to the current layout context.
    If the token is

    - /to the left/ :
	Exit the current context and a return virtual close brace (stay in the
	'Syntax.Parser.Lexer.bol' state).

    - /same column/ :
	Exit the 'Syntax.Parser.Lexer.bol' state and return a virtual semi
	colon.

    - /to the right/ :
	Exit the 'Syntax.Parser.Lexer.bol' state and continue lexing.

    If the current block doesn't use layout (i.e. it was started by
    'openBrace') all positions are considered to be /to the right/.
-}
offsideRule :: LexAction Token
offsideRule inp _ _ =
    do	offs <- getOffside $ lexPos p
	case offs of
	    LT	-> do	popContext
			return (TkVCloseBrace (Range p p))
	    EQ	-> do	popLexState
			return (TkVSemi (Range p p))
	    GT	-> do	popLexState
			lexToken

{-| This action is only executed from the 'Syntax.Parser.Lexer.empty_layout'
    state. It will exit this state, enter the 'Syntax.Parser.Lexer.bol' state,
    and return a virtual close brace (closing the empty layout block started
    by 'newLayoutContext').
-}
emptyLayout :: LexAction Token
emptyLayout inp _ _ =
    do	popLexState
	pushLexState bol
	return (TkVCloseBrace (Range p p))
    where
	p = lexPos inp

{-| Start a new layout context. This is one of two ways to get out of the
    'Syntax.Parser.Lexer.layout' state (the other is 'openBrace'). There are
    two possibilities:

    - The current token is to the right of the current layout context (or we're
      in a no layout context).

    - The current token is to the left of or in the same column as the current
      context.

    In the first case everything is fine and we enter a new layout context at
    the column of the current token. In the second case we have an empty layout
    block so we enter the 'Syntax.Parser.Lexer.empty_layout' state. In both
    cases we return a virtual open brace without consuming any input.

    Entering a new state when we know we want to generate a virtual @{}@ may
    seem a bit roundabout. The thing is that we can only generate one token at
    a time, so the way to generate two tokens is to generate the first one and
    then enter a state in which the only thing you can do is generate the
    second one.
-}
newLayoutContext :: LexAction Token
newLayoutContext inp _ _ =
    do	let offset = posCol $ lexPos inp
	ctx <- topContext
	case ctx of
	    Layout prev_off | prev_off >= offset ->
		do  -- token is indented to the left of the previous context.
		    -- we must generate a {} sequence now.
		    pushLexState layout_left
		    return (TkVOpenBrace (Range p p))
	    _ -> do pushContext (Layout offset)
		    return (TkVOpenBrace (Range p p))


-- | Compute the relative position of a location to the
--   current layout context.
getOffside :: Position -> Parser Ordering
getOffside loc =
    do	ctx <- topContext
	return $ case ctx of
	    Layout n	-> compare (posCol loc) n
	    _		-> GT

