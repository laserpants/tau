# 01. A simple toy language

A first rendition of the core language, implementing a simplified AST, parser, evaluation logic and a Hindley-Milner type system.
Many important pieces, like code generation, algebraic data types, case statementes, modules, and higher-kinded polymorphism are still missing.

## Syntax

<table style="margin: 1em;">
  <tr>
    <td>\(e\,\)</td>
    <td align="center">\(\Coloneqq\)</td>
    <td>\(v\)</td>
    <td style="width: 3em;"></td>
    <td>Variable</td>
  </tr>
  <tr>
    <td></td>
    <td align="center">\(\vert\)</td>
    <td>\(e\, e\)</td>
    <td></td>
    <td>Function application</td>
  </tr>
  <tr>
    <td></td>
    <td align="center">\(\vert\)</td>
    <td>\(\lambda v.e\)</td>
    <td></td>
    <td>Lambda abstraction</td>
  </tr>
  <tr>
    <td></td>
    <td align="center">\(\vert\)</td>
    <td>\(\mu\,e\)</td>
    <td></td>
    <td>Fixpoint combinator</td>
  </tr>
  <tr>
    <td></td>
    <td align="center">\(\vert\)</td>
    <td>\(\text{let}\,v=\,e\,\text{in}\,e\)</td>
    <td></td>
    <td>Let-binding</td>
  </tr>
  <tr>
    <td></td>
    <td align="center">\(\vert\)</td>
    <td>\(\text{if}\;e\,\text{then}\,e\,\text{else}\,e\)</td>
    <td></td>
    <td>If-clause</td>
  </tr>
  <tr>
    <td></td>
    <td align="center">\(\vert\)</td>
    <td>\((+)\; e\, e\)</td>
    <td></td>
    <td rowspan="4">Binary operators</td>
  </tr>
  <tr>
    <td></td>
    <td align="center">\(\vert\)</td>
    <td>\((-)\; e\, e\)</td>
    <td></td>
  </tr>
  <tr>
    <td></td>
    <td align="center">\(\vert\)</td>
    <td>\((\times)\; e\, e\)</td>
    <td></td>
  </tr>
  <tr>
    <td></td>
    <td align="center">\(\vert\)</td>
    <td>\((=)\; e\, e\)</td>
    <td></td>
  </tr>
  <tr>
    <td></td>
    <td align="center">\(\vert\)</td>
    <td>\(c\)</td>
    <td></td>
    <td>Literal</td>
  </tr>
</table>

### Values

### Free Variables

## Parser

## Interpreter

## Types

<table style="margin: 1em;">
  <tr>
    <td>\(\tau\,\)</td>
    <td align="center">\(\Coloneqq\)</td>
    <td>\( \text{Int} \)</td>
    <td style="width: 3em;"></td>
    <td>Integer</td>
  </tr>
  <tr>
    <td></td>
    <td align="center">\(\vert\)</td>
    <td>\( \text{Bool} \)</td>
    <td></td>
    <td>Boolean</td>
  </tr>
  <tr>
    <td></td>
    <td align="center">\(\vert\)</td>
    <td>\(\alpha\)</td>
    <td></td>
    <td>Type variable</td>
  </tr>
  <tr>
    <td></td>
    <td align="center">\(\vert\)</td>
    <td>\(\tau \rightarrow \tau\)</td>
    <td></td>
    <td>Type arrow</td>
  </tr>
</table>

### Type Schemes

<table style="margin: 1em;">
  <tr>
    <td>\(\sigma\,\)</td>
    <td align="center">\(\Coloneqq\)</td>
    <td>\(\tau\)</td>
    <td style="width: 3em;"></td>
    <td>Monotype</td>
  </tr>
  <tr>
    <td></td>
    <td align="center">\(\vert\)</td>
    <td>\( \forall \alpha.\sigma \)</td>
    <td></td>
    <td>Polytype quantifier</td>
  </tr>
</table>

### Type Inference

<p style="font-size: 1.2em;">
$$
  \begin{aligned}
    \text{FV}( \text{Int} ) &= \varnothing \\
    \text{FV}( \text{Bool} ) &= \varnothing \\
    \text{FV}( \alpha ) &= \{ \alpha \} \\
    \text{FV}( \tau_1 \rightarrow \tau_2 ) &= \text{FV}(\tau_1) \cup \text{FV}(\tau_2)
  \end{aligned}
$$
</p>
