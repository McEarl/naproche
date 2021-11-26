# The Cantor-Schröder-Bernstein Theorem

[readtex basic-notions/sets-and-functions/sections/02_functions/05_functions-and-set-systems.ftl.tex]
[readtex basic-notions/sets-and-functions/sections/02_functions/06_equipollency.ftl.tex]

Let x \in y stand for x is an element of y.
Let x \notin y denote x is not an element of y.

Theorem Cantor Schroeder Bernstein.
Let x,y be sets.
x and y are equipollent iff there exists a function from x into y and
there exists a function from y into x.

Proof.
  Case x and y are equipollent.
    Take a bijection f between x and y.
    Then f^{-1} is a bijection between y and x.
    Hence f is a function from x into y and f^{-1} is a function from y into x.
  End.

  Case there exists a function from x into y and there exists a function from into x.
    Take a function f from x into y.
    Take a function g from y into x.
    We have y \setminus f[a] \subseteq y for any a \in \pow(x).

    (1) Define h(a) = x \setminus g[y \setminus f[a]] for a \in \pow(x).

    h is a function from \pow(x) to \pow(x).

    Let us show that h preserves subsets.
      Let a,b be subsets of x.
      Assume a \subseteq b.
      Then f[a] \subseteq f[b].
      Hence y \setminus f[b] \subseteq y \setminus f[a].
      Thus g[y \setminus f[b]] \subseteq g[y \setminus f[a]] (by SF 02 02 889945).
      Indeed y \setminus f[b] and y \setminus f[a] are subsets of y.
      Therefore x \setminus g[y \setminus f[a]] \subseteq x \setminus g[y \setminus f[b]].
      Consequently h[a] \subseteq h[b].
    End.

    Hence we can take a fixed point c of h.

    (2) Define F(u) = f(u) for u \in c.

    We have c = h(c) iff x \setminus c = g[y \setminus f[c]].
    g^{-1} is a bijection between \range(g) and y.
    Thus x \setminus c = g[y \setminus f[c]] \subseteq \range(g).

    (3) Define G(u) = g^{-1}(u) for u \in x \setminus c.

    F is a bijection between c and \range(F).
    G is a bijection between x \setminus c and \range(G).

    Define H(u) =
      u \in x    -> F(u)
      u \notin c -> G(u)
    for u \in x.

    Let us show that H is a function to y.
      Let v be a value of H.
      Take u \in x such that H(u) = v.
      If u \in c then v = H(u) = F(u) = f(u) \in y.
      If u \notin c then v = H(u) = G(u) = g^{-1}(u) \in y.
    End.

    Let us show that every element of y is a value of H.
      Let v \in y.

      Case v \in f[c].
        Take u \in c such that f(u) = v.
        Then F(u) = v.
      End.

      Case v \notin f[c].
        Then v \in y \setminus f[c].
        Hence g(v) \in g[y \setminus f[c]].
        Thus g(v) \in x \setminus h(c).
        We have g(v) \in x \setminus c.
        Therefore we can take u \in x \setminus c such that G(u) = v.
        Then v = H(u).
      End.
    End.

    Let us show that H is one to one.
      Let u,v \in \dom(H).
      Assume u \neq v.

      Case u,v \in c.
        Then H(u) = F(u) and H(v) = F(v).
        We have F(u) \neq F(v).
        Hence H(u) \neq H(v).
      End.

      Case u,v \notin c.
        Then H(u) = G(u) and H(v) = G(v).
        We have G(u) \neq G(v).
        Hence H(u) \neq H(v).
      End.

      Case u \in c and v \notin c.
        Then H(u) = F(u) and H(v) = G(v).
        Hence v \in g[y \setminus f[c]].
        We have G(v) \in y \setminus F[c].
        Thus G(v) \neq F(u).
      End.

      Case u \notin c and v \in c.
        Then H(u) = G(u) and H(v) = F(v).
        Hence u \in g[y \setminus f[c]].
        We have G(u) \in y \setminus f[c].
        Thus G(u) \neq F(v).
      End.
    End.

    Hence H is a bijection between x and y.
  End.
Qed.