module

public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDecomposition.Basic
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDecomposition.Normalizer
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDecomposition.Rigidity

/-!
# Decomposition of the small odd-support factors

Aschbacher--Smith, *The Classification of Quasithin Groups*, D.2.12(1–2),
printed pp.183–184. Local rigidity says distinct commuting factors fix each
other's supports. The maximal commuting family and nilpotent normalizer
argument then makes the entire canonical family commute. Coprime splitting
gives independence of the supports, and faithfulness gives independence of
the actors.

The internal product and sum are expressed by independence and generation
of the actual subgroups: each factor meets the join of the other factors
trivially. Thus all inclusions are the canonical subgroup inclusions; no
abstract product identification replaces the given factors. The basic module
also exports their conjugation permutation and the equivariant transport
formula for supports.
-/

namespace CFSG.Quasithin.ChapterD

variable {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V] [FaithfulSMul G V]

/-- All canonical small-support factors centralize each other. The statement
also includes the commutativity of each individual factor. -/
public theorem smallSupportFactors_commutingFamily
    {k : ℕ} (hk : k = 1 ∨ k = 2) :
    ∀ X ∈ smallSupportFactors G V k, ∀ Y ∈ smallSupportFactors G V k,
      X ≤ Subgroup.centralizer (Y : Set G) := by
  apply smallSupport_commutingFamily_of_local_rigidity hk
  intro X hX Y hY hne hcomm
  exact smallSupportFactors_cross_fixed_of_commuting hk hX hY hne hcomm

/-- Distinct canonical factors fix each other's supports. -/
public theorem smallSupportFactors_cross_fixed
    {k : ℕ} (hk : k = 1 ∨ k = 2) {X Y : Subgroup G}
    (hX : X ∈ smallSupportFactors G V k) (hY : Y ∈ smallSupportFactors G V k)
    (hne : X ≠ Y) :
    commutatorAction Y V ≤ FixedPoints.subgroup X V :=
  smallSupportFactors_cross_fixed_of_commuting hk hX hY hne
    (smallSupportFactors_commutingFamily hk X hX Y hY)

/-- D.2.12(1–2): the canonical actors form an internal direct product in G_k,
and their supports form an internal direct sum in [V,G_k]. Independence is
with respect to the full join of all other factors, not just pairwise
disjointness. Both generation equalities use the given subgroup inclusions. -/
public theorem smallSupport_decomposition
    {k : ℕ} (hk : k = 1 ∨ k = 2) :
    iSupIndep (fun X : smallSupportFactors G V k => X.val) ∧
    Pairwise (fun X Y : smallSupportFactors G V k =>
      ∀ x y : G, x ∈ X.val → y ∈ Y.val → Commute x y) ∧
    iSupIndep (fun X : smallSupportFactors G V k => commutatorAction X.val V) ∧
    smallSupportGroup G V k = (⨆ X : smallSupportFactors G V k, X.val) ∧
    commutatorAction (smallSupportGroup G V k) V =
      ⨆ X : smallSupportFactors G V k, commutatorAction X.val V := by
  apply smallSupport_decomposition_of_cross_fixed hk
  intro X Y hne
  exact smallSupportFactors_cross_fixed hk X.property Y.property
    (fun heq => hne (Subtype.ext heq))

/-- D.2.12(1), retaining the original factors as subgroups of G. -/
public theorem smallSupportFactors_internalDirectProduct
    {k : ℕ} (hk : k = 1 ∨ k = 2) :
    iSupIndep (fun X : smallSupportFactors G V k => X.val) ∧
    Pairwise (fun X Y : smallSupportFactors G V k =>
      ∀ x y : G, x ∈ X.val → y ∈ Y.val → Commute x y) ∧
    smallSupportGroup G V k = (⨆ X : smallSupportFactors G V k, X.val) := by
  have h := smallSupport_decomposition (G := G) (V := V) hk
  exact ⟨h.1, h.2.1, h.2.2.2.1⟩

/-- D.2.12(2), retaining the original supports as subgroups of V. Since V is
elementary abelian, independence and generation give its internal direct sum. -/
public theorem smallSupportSupports_internalDirectSum
    {k : ℕ} (hk : k = 1 ∨ k = 2) :
    iSupIndep (fun X : smallSupportFactors G V k => commutatorAction X.val V) ∧
    commutatorAction (smallSupportGroup G V k) V =
      ⨆ X : smallSupportFactors G V k, commutatorAction X.val V := by
  have h := smallSupport_decomposition (G := G) (V := V) hk
  exact ⟨h.2.2.1, h.2.2.2.2⟩

/-- A support identifies its canonical factor uniquely. Together with
`smallSupport_support_conjBy`, this identifies the permutations of factors
and supports under ambient conjugation. -/
public theorem smallSupportFactors_support_injective
    {k : ℕ} (hk : k = 1 ∨ k = 2) :
    Function.Injective (fun X : smallSupportFactors G V k => commutatorAction X.val V) := by
  intro X Y hsupport
  apply Subtype.ext
  exact smallSupportFactors_eq_of_commuting_support_eq hk X.property Y.property
    (smallSupportFactors_commutingFamily hk X.val X.property Y.val Y.property)
    hsupport.symm

end CFSG.Quasithin.ChapterD
