@*=
@header
@register_commands
@requires
@functions
@register_mappings
@register_commands

@header+=
" Vim plugin for algebra symbolic manipulation
" Creation Date: 2020 Sep 11
" Maintainer:  jbyuki
" License:     This file is placed in the public domain 

@requires+=
lua algebra = require("algebra")

@register_mappings+=
nnoremap <F2> :lua algebra.simplify()<CR>
nnoremap <F3> :lua algebra.evaluate()<CR>
nnoremap <F5> :lua algebra.printSymTable()<CR>
