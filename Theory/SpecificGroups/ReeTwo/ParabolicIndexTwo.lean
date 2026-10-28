module

public import Theory.SpecificGroups.ReeTwo.ParabolicIndexTwo.Derived
public import Theory.SpecificGroups.ReeTwo.ParabolicIndexTwo.QuotientAction
public import Theory.SpecificGroups.ReeTwo.ParabolicIndexTwo.Involutions
public import Theory.SpecificGroups.ReeTwo.ParabolicIndexTwo.Parity

/-!
# Intrinsic structure of the three index-two Ree local kernels

This interface assembles the concrete calculations for the literal kernels of
`character`, `coreCharacter`, and `mixedCharacter` in `ReeTwo.Centralizer`.
All three kernels H have order 10240 and index two. Write Q = O₂(H), E = [Q,Q],
F = C_H(E), and P = ⟨fiveGenerator⟩, with the same marked five-element in H.

* For the core-character and mixed-character kernels, the actual inclusion
  identifies Q with Ω₁(Core), of order 512. The compatible quotient map
  identifies H/Q with the specified faithful C5:C4 group. E is elementary
  abelian of order 32 and F = E. The subgroup C_Q(P) is the image of ⟨v12⟩,
  central of order two. There are involutions in Q − E and they form one
  conjugacy class under H. Every Sylow two-subgroup of H/Q is cyclic of order
  four. These statements are uniform with the sole selector
  `χ = coreCharacter ∨ χ = mixedCharacter`.
* The parity kernel retains the full coordinate core, of order 1024. Its
  quotient is identified with `DihedralGroup 5` through the actual even
  complement coordinates, preserving the five-rotation and a chosen reflection.
  E has order 32 and F has order 64. With W the embedded Ω₁(Core),
  E < W < Q, W ∩ F = E, and W ∨ F = Q; W has order 512. These subgroups are
  characteristic in H and in Q, and Ω₁(F) = E. Involutions in Q − F exist and
  form one H-class. C_Q(P) is the image of ⟨v5⟩, cyclic of order four and
  noncentral in Q. Every Sylow two-subgroup of H/Q is cyclic of order two.
* In all three kernels, the actual core inclusion induces an isomorphism
  Q/C_Q(E) ≃ Core/C_Core(Core'). The quotient is elementary abelian of order
  sixteen. The comparison intertwines intrinsic conjugation with the computed
  coordinate action. The marked five-element acts with order five, and the
  H-action has no nontrivial proper invariant subgroup.

The proofs use the coordinate omega intersection and generation identities,
the compatible complement projections, and the saved involution conjugators
whose binary character is zero. `Kernels` and `Derived` establish the intrinsic
subgroups; `QuotientAction`, `Involutions` (including `FiveFixed`), and `Parity`
complete the action, orbit, fixed-subgroup, Sylow, and lattice calculations.

These are unconditional facts about the named local kernels. Selection of an
ambient Tits parabolic still requires a compatible model comparison. In
particular the parity kernel's extra characteristic subgroup W is retained;
irreducibility on Q/F does not give an unrestricted subgroup dichotomy.

Sources: the Ree/Tits passage in the proof of quasithin Lemma 14.2.21,
printed p.989 (PDF p.1006); Aschbacher, *The Tits group as a standard subgroup*
(1982), Section 3, especially (3.2.7) and (3.2.11); Parrott,
*A characterization of the Tits' simple group* (1972), printed p.672.
The fixed-subgroup calculation concerns P, the cyclic-five complement; it
does not replace P by the two-residual O²(H).
-/
