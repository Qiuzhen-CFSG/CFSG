module

public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDefs
public import Theory.GroupAction.SupportTransport
public import Theory.GroupAction.IndependentCoprimeSupports
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.ElementaryAbelian.Basic

/-!
# The canonical small-support family

The family and its supports are stable under conjugation. Coprime splitting
makes any mutually fixed family of supports independent, and faithfulness
makes the corresponding actors independent as well. These facts give the
assembly interface for the maximal commuting family and nilpotent normalizer
argument of Aschbacher--Smith, *The Classification of Quasithin Groups*,
D.2.12(1–2), printed pp.183–184.
-/

namespace CFSG.Quasithin.ChapterD

variable {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]

/-- The canonical inclusions generate precisely G_k. -/
public theorem smallSupportGroup_eq_iSup (k : ℕ) :
    smallSupportGroup G V k = ⨆ X : smallSupportFactors G V k, X.val :=
  sSup_eq_iSup' _

/-- Conjugation transports the support by the given ambient action. -/
public theorem smallSupport_support_conjBy (X : Subgroup G) (g : G) :
    (commutatorAction X V).map (MulDistribMulAction.toMulAut G V g).toMonoidHom =
      commutatorAction (X.conjBy g) V :=
  ActionSupport.commutatorAction_conjBy X g

/-- Membership in the canonical family is stable under ambient conjugation. -/
public theorem smallSupportFactors_conjBy {k : ℕ} {X : Subgroup G}
    (hX : X ∈ smallSupportFactors G V k) (g : G) :
    X.conjBy g ∈ smallSupportFactors G V k := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    exact (inferInstance : (fittingSubgroup G).Normal).conj_mem y (hX.1 hy) g
  · change Nat.card (X.map (MulAut.conj g).toMonoidHom) = _
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hX.2.1
  · rw [← smallSupport_support_conjBy X g]
    exact (Subgroup.card_map_of_injective
      (MulDistribMulAction.toMulAut G V g).injective).trans hX.2.2

/-- Ambient conjugation acts as an actual permutation of the canonical factors. -/
@[expose] public def smallSupportFactors_conjEquiv (k : ℕ) (g : G) :
    smallSupportFactors G V k ≃ smallSupportFactors G V k where
  toFun X := ⟨X.val.conjBy g, smallSupportFactors_conjBy X.property g⟩
  invFun X := ⟨X.val.conjBy g⁻¹, smallSupportFactors_conjBy X.property g⁻¹⟩
  left_inv X := Subtype.ext (Subgroup.conjBy_inv X.val g)
  right_inv X := Subtype.ext (Subgroup.conjBy_inv' X.val g)

/-- The generated small-support subgroup is normal in the full ambient group. -/
public instance smallSupportGroup_normal (k : ℕ) :
    (smallSupportGroup G V k).Normal := by
  constructor
  intro x hx g
  have hmap : (smallSupportGroup G V k).map (MulAut.conj g).toMonoidHom ≤
      smallSupportGroup G V k := by
    rw [smallSupportGroup_eq_iSup, Subgroup.map_iSup]
    apply iSup_le
    intro X
    exact le_iSup_of_le ⟨X.val.conjBy g, smallSupportFactors_conjBy X.property g⟩ le_rfl
  exact hmap (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx)

/-- Nilpotency uses only containment in the Fitting subgroup, with no solvability
assumption on the ambient group. -/
public instance smallSupportGroup_nilpotent [Finite G] (k : ℕ) :
    Group.IsNilpotent (smallSupportGroup G V k) := by
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe (smallSupportGroup_le_fitting G V k))

/-- The canonical supports generate exactly the support of G_k. -/
public theorem smallSupportGroup_support_eq_iSup (k : ℕ) :
    commutatorAction (smallSupportGroup G V k) V =
      ⨆ X : smallSupportFactors G V k, commutatorAction X.val V :=
  ActionSupport.commutatorAction_eq_iSup_of_eq_iSup
    (fun X : smallSupportFactors G V k => X.val) (smallSupportGroup_eq_iSup k)

/-- Every canonical factor has order coprime to the binary module. -/
public theorem smallSupportFactor_coprime [Finite V] [IsElementaryAbelian 2 V]
    {k : ℕ} (hk : k = 1 ∨ k = 2) {X : Subgroup G}
    (hX : X ∈ smallSupportFactors G V k) :
    Nat.Coprime (Nat.card X) (Nat.card V) := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
  rw [hX.2.1, hn]
  apply Nat.Coprime.pow_right
  rcases hk with rfl | rfl <;> decide

/-- Each canonical factor is cyclic of the indicated prime order. -/
public theorem smallSupportFactor_isCyclic {k : ℕ} (hk : k = 1 ∨ k = 2)
    {X : Subgroup G} (hX : X ∈ smallSupportFactors G V k) : IsCyclic X := by
  let _ : Fact (Nat.Prime (2 * k + 1)) := ⟨by
    rcases hk with rfl | rfl <;> decide⟩
  exact isCyclic_of_prime_card hX.2.1

/-- Faithfulness restricts to the support of each canonical factor. -/
public theorem smallSupportFactor_eq_one_of_fixes_support
    [Finite G] [Finite V] [IsElementaryAbelian 2 V] [FaithfulSMul G V]
    {k : ℕ} (hk : k = 1 ∨ k = 2) {X : Subgroup G}
    (hX : X ∈ smallSupportFactors G V k) (x : X)
    (hfix : ∀ v ∈ commutatorAction X V, (x : G) • v = v) : (x : G) = 1 :=
  ActionSupport.eq_one_of_fixes_support X (smallSupportFactor_coprime hk hX) x hfix

/-- Mutual fixedness supplies genuine independence of both canonical families.
The two equalities identify their generated groups, without choosing an abstract
product isomorphism. -/
public theorem smallSupport_decomposition_of_cross_fixed
    [Finite G] [Finite V] [IsElementaryAbelian 2 V] [FaithfulSMul G V]
    {k : ℕ} (hk : k = 1 ∨ k = 2)
    (hcross : ∀ X Y : smallSupportFactors G V k, X ≠ Y →
      commutatorAction Y.val V ≤ FixedPoints.subgroup X.val V) :
    iSupIndep (fun X : smallSupportFactors G V k => X.val) ∧
    Pairwise (fun X Y : smallSupportFactors G V k =>
      ∀ x y : G, x ∈ X.val → y ∈ Y.val → Commute x y) ∧
    iSupIndep (fun X : smallSupportFactors G V k => commutatorAction X.val V) ∧
    smallSupportGroup G V k = (⨆ X : smallSupportFactors G V k, X.val) ∧
    commutatorAction (smallSupportGroup G V k) V =
      ⨆ X : smallSupportFactors G V k, commutatorAction X.val V := by
  have hcop (X : smallSupportFactors G V k) := smallSupportFactor_coprime hk X.property
  refine ⟨ActionSupport.actors_iSupIndep _ hcop hcross, ?_,
    ActionSupport.supports_iSupIndep _ hcop hcross,
    smallSupportGroup_eq_iSup k, smallSupportGroup_support_eq_iSup k⟩
  intro X Y hXY x y hx hy
  exact ActionSupport.commute_of_cross_fixed X.val Y.val
    (hcross X Y hXY) (hcross Y X hXY.symm) ⟨x, hx⟩ ⟨y, hy⟩

end CFSG.Quasithin.ChapterD
