This crate implements elliptic curve arithmetic and bilinear pairings for Barreto-Lynn-Scott curves
containing a (large) prime-order torsion of embedding degree 24 (hence, BLS24 curves).

A BLS24 curve is specified by an integer parameter <i>u</i> &#8712; &Zopf; with
<i>u</i> &equiv; 1 (mod 3) such that the values
<i>r</i>&nbsp;&#x2254; <i>u&#x2078;</i> - <i>u&#x2074;</i> + 1 and
<i>p</i>&nbsp;&#x2254; ((<i>u</i> - 1)&sup2;/3)<i>r</i> + <i>u</i> are prime, defining
finite fields <b>F</b><sub><i>r</i></sub> and <b>F</b><sub><i>p</i></sub>.
The curve equation is <i>E</i>/<b>F</b><sub><i>p</i></sub> : <i>Y&sup2;Z</i> = <i>X&sup3; + bZ&sup3;</i>,
whose number of <b>F</b><sub><i>p</i></sub>-rational points is
<i>#E</i>(<b>F</b><sub><i>p</i></sub>) = <i>c&#xFEFF;r</i> with
<i>c</i>&nbsp;&#x2254; (<i>u</i> - 1)&sup2;/3 being the so-called cofactor of the <i>r</i>-torsion.
The quadratic twist of the curve is <i>E'</i>/<b>F</b><sub><i>p&#x2074;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3; + b'Z'&sup3;</i>,
whose number of <b>F</b><sub><i>p&#x2074;</i></sub>&thinsp;-rational points is
<i>#E'</i>(<b>F</b><sub><i>p&#x2074;</i></sub>) = <i>h'r</i>, where <i>h'</i> is called
the cofactor of the <i>r</i>-torsion on the curve twist.
Parameter <i>u</i> is also the order of the optimal pairing for BLS24 curves.

This implementation focuses on curves with <i>u</i> &equiv; 16 (mod 72), which constitute
one of the four Costello-Lauter-Naehrig families of particularly attractive BLS24 curves.
This enables specifying the tower-friendly extension fields
<b>F</b><sub><i>p&sup2;</i></sub> &simeq; <b>F</b><sub><i>p</i></sub>&lbrack;<i>i</i>&rbrack;/&lt;<i>i&sup2;</i>&nbsp;+&nbsp;1&gt;,
<b>F</b><sub><i>p&#x2074;</i></sub> &simeq; <b>F</b><sub><i>p&sup2;</i></sub>&nbsp;&lbrack;<i>v</i>&rbrack;/&lt;<i>v&sup2;</i>&nbsp;+&nbsp;<i>&xi;</i>&gt; with <i>&xi;</i>&nbsp;&#x2254; 1 + <i>i</i>,
and <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub> &simeq; <b>F</b><sub><i>p&#x2074;</i></sub>&nbsp;&lbrack;<i>z</i>&rbrack;/&lt;<i>z&#x2076;</i>&nbsp;+&nbsp;<i>v</i>&gt;
(notice the signs of <i>&xi;</i> and <i>v</i>).

This family also tends to be KZG-friendly, in the sense that the curve order <i>r</i> has high 2-adicity
(that is, 2<i>&#x1D50;</i> | <i>r</i> - 1 for some fairly large <i>m</i>>) by just requiring
<i>u</i> itself to be a multiple of a suitably high power of 2.
The equations of the curve and its twist take simple, uniform shapes, with
<i>b</i> = 4 and <i>b'</i> = 4<i>v</i>.
For simplicity and efficiency, only positive, sparse (trinomial, tetranomial, and pentanomial)
<i>u</i> parameters are currently supported.

All feasible care has been taken to make sure the arithmetic algorithms adopted in this crate
are isochronous ("constant-time") and efficient.
Yet, the no-warranty clause of the MIT license is in full force for this whole crate.

References:

* Paulo S. L. M. Barreto, Ben Lynn, Michael Scott:
  "Constructing Elliptic Curves with Prescribed Embedding Degrees."
  In: Cimato, S., Persiano, G., Galdi, C. (eds). <i>Security in Communication Networks -- SCN 2002</i>.
  Lecture Notes in Computer Science, vol. 2576, pp. 257--267.
  Springer, Berlin, Heidelberg. 2003. https://doi.org/10.1007/3-540-36413-7_19

* Craig Costello, Kristin Lauter, Michael Naehrig:
  "Attractive Subfamilies of BLS Curves for Implementing High-Security Pairings."
  In: Bernstein, D.J., Chatterjee, S. (eds) <i>Progress in Cryptology -- INDOCRYPT 2011</i>.
  Lecture Notes in Computer Science, vol 7107, pp. 320--342.
  Springer, Berlin, Heidelberg, 2011. https://doi.org/10.1007/978-3-642-25578-6_23
