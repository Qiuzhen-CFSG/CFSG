module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.LocalGeometry.Products
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.LocalGeometry.SylowControl
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.LocalGeometry.FixedSpace
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.LocalGeometry.PlaneNormalizer

/-!
# Local geometry of the exceptional order-27 normalizer

For every exceptional A and every displayed decomposition N_G(A)=A(VX),
the four-group character calculation gives |C_A(X)|=3. The product and
relative-normalizer calculations then show that X is not contained in A,
that Y=C_A(X)X has order nine, and that Z=N_G(A)∩N_G(Y) is nonabelian
of order 27. These are the five fields of ExceptionalLocalGeometry.

The same fixed-subgroup calculation gives uniqueness of A among abelian
order-27 subgroups of N_G(A). The p-group normalizer condition promotes
uniqueness to every ambient Sylow three-subgroup containing A. The independent
index-three argument proves that A normalizes every order-27 subgroup of
N_G(A), completing ExceptionalSylowControl. Both producers are uniform in A,
so the final contradiction may also apply them to its actual conjugate B.
Neither producer requires an OddCentralizerComplement or an extra local
calculation premise.

Source: Bender, *Finite groups with large subgroups* (1974), proof of (4.1),
printed p.225 (PDF page 3).
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- The complete local geometry for every exceptional normalizer decomposition.
This supplies the `localGeometry` argument of
`not_exceptionalOddNormalizer_of_local_steps`. -/
public theorem exceptional_localGeometry (h : Janko1CentralizerData G)
    (A : Subgroup G) (e : ExceptionalOddNormalizer A)
    (V X : Subgroup G) (hVe : IsElementaryAbelian 2 V)
    (hV : Nat.card V = 4) (hX : Nat.card X = 3)
    (hXV : X ≤ normalizer (V : Set G))
    (hN : normalizer (A : Set G) = A ⊔ (V ⊔ X)) :
    ExceptionalLocalGeometry A X := by
  have hfixed := h.exceptional_fixed_card A e V X hVe hV hX hXV hN
  obtain ⟨hZcard, hZnonabelian⟩ :=
    h.exceptional_plane_normalizer_card_nonabelian_of_fixed_card
      A e V X hV hX hXV hN hfixed
  exact
    { outside := h.exceptional_actor_outside A V X e.card hV hX hXV hN
      fixed_card := hfixed
      plane_card := h.exceptional_plane_card_of_fixed_card A V X e.card hV hX hXV hN hfixed
      normalizer_card := hZcard
      normalizer_nonabelian := hZnonabelian }

/-- Every exceptional A has the ambient Sylow uniqueness and local normalization
properties used in `not_exceptionalOddNormalizer_of_local_steps`.
The decomposition and its fixed-subgroup order are both discharged here. -/
public theorem exceptional_sylowControl (h : Janko1CentralizerData G)
    (A : Subgroup G) (e : ExceptionalOddNormalizer A) :
    ExceptionalSylowControl A := by
  obtain ⟨V, X, hVe, hV, hX, hXV, hN⟩ := e.normalizer_decomposition
  exact h.exceptional_sylowControl_of_fixed_card A e V X hV hX hXV hN
    (h.exceptional_fixed_card A e V X hVe hV hX hXV hN)

end CFSG.Quasithin.Janko1CentralizerData
