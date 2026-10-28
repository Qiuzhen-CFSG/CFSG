module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.ModelCalculations
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.SpecificGroups.PSL2.SemilinearCoverage
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.Bounds.Quotient
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# Ambient field actions of the marked Hermitian layer

Self-centralization of F* and the centerless SL₂ model make conjugation on
L faithful. Semilinear coverage identifies the actual quotient G/L with
its subgroup of field automorphisms. Removing inner factors realizes every
field component in G. Thus even index supplies an actual outer involution
inducing half-degree Frobenius; all outer involutions are conjugate by L.
Odd index places all elementary two-subgroups in L. An outer elementary
actor is its inner intersection times one outer involution and has one more
rank than that intersection.

These are group-theoretic conclusions on the original source carrier.
Identification of the involution's action on the Hermitian vector space,
fixed-space calculations, and global ratio assertions remain separate.
No full-linear-normalizer SQTK or unfinished H.1 assertion is used.
Source: Aschbacher–Smith, K.3.1.2, printed p.454, and D.2.1, printed p.178,
combined manuscript of 1 March 2004.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterK.RankOne
open Representation Representation.BinaryOffender Subgroup
open Representation.OrthogonalFourMinus.FiniteModel
open Theory.GroupTheory
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  {s : ℕ} [NeZero s] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
local instance fieldAutFinite : Finite (Field s ≃+* Field s) :=
  Finite.of_injective (fun σ : Field s ≃+* Field s => (σ : Field s → Field s))
    DFunLike.coe_injective
namespace OrthogonalModel
variable (M : OrthogonalModel s ρ L)

/-- The marked layer, with the canonical projective quotient. -/
def projectiveEquiv : L ≃* Theory.PSL2.Group (Field s) :=
  M.groupEquiv.trans (Theory.PSL2.sl2QuotientEquiv (Field s))

include M in
omit [Finite G] in
theorem layer_center_eq_bot : center L = ⊥ := by
  apply bot_unique
  intro g hg
  have hz := (Subgroup.centerCongr M.groupEquiv ⟨g, hg⟩).property
  change M.groupEquiv g ∈ center _ at hz
  rw [Theory.PSL2.sl2_center_eq_bot] at hz
  exact M.groupEquiv.injective ((mem_bot.mp hz).trans M.groupEquiv.map_one.symm)

include M in
/-- F* self-centralization and the marked centerless layer kill its ambient centralizer. -/
theorem centralizer_eq_bot (h : SourceHypotheses ρ L) : centralizer (L : Set G) = ⊥ := by
  have hCL : centralizer (L : Set G) ≤ L := by
    rw [← h.fitting]
    exact centralizer_generalizedFitting_le G
  apply bot_unique
  intro g hg
  have hgZ : (⟨g, hCL hg⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro x
    exact Subtype.ext (hg x x.property)
  rw [M.layer_center_eq_bot] at hgZ
  exact congrArg Subtype.val (mem_bot.mp hgZ)

variable [L.Normal]
/-- The actual ambient conjugation action in the marked projective coordinates. -/
def ambientAut : G →* MulAut (Theory.PSL2.Group (Field s)) :=
  (MulAut.congr M.projectiveEquiv).toMonoidHom.comp MulAut.conjNormal

theorem ambientAut_injective (h : SourceHypotheses ρ L) :
    Function.Injective M.ambientAut :=
  (MulAut.congr M.projectiveEquiv).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot L (M.centralizer_eq_bot h))

omit [Finite G] in
theorem ambientAut_layer (g : L) :
    M.ambientAut g = MulAut.conj (M.projectiveEquiv g) := by
  change MulAut.congr M.projectiveEquiv (MulAut.conjNormal (g : G)) = _
  rw [MulAut.conjNormal_val, MulAut.congr_conj]

omit [Finite G] in
theorem ambientAut_semilinear (g : G) :
    ∃ (a : Theory.PSL2.Group (Field s)) (σ : Field s ≃+* Field s),
      M.ambientAut g = MulAut.conj a * Theory.PSL2.fieldAut σ :=
  Theory.PSL2.semilinear_coverage _

theorem ambientAut_mem_inner_iff (h : SourceHypotheses ρ L) (g : G) :
    M.ambientAut g ∈ Theory.PSL2.inner (Field s) ↔ g ∈ L := by
  constructor
  · intro hg
    obtain ⟨a, ha⟩ := (Theory.PSL2.mem_inner_iff _ _).mp hg
    have he : g = (M.projectiveEquiv.symm a : G) := by
      apply M.ambientAut_injective h
      rw [ha, M.ambientAut_layer, M.projectiveEquiv.apply_symm_apply]
    rw [he]
    exact (M.projectiveEquiv.symm a).property
  · intro hg
    exact (Theory.PSL2.mem_inner_iff _ _).mpr ⟨M.projectiveEquiv ⟨g, hg⟩,
      M.ambientAut_layer ⟨g, hg⟩⟩

/-- The literal field factor of the ambient action on the marked layer. -/
def fieldHom : G →* (Field s ≃+* Field s) :=
  (Theory.PSL2.fieldProjectionOfCoverage Theory.PSL2.semilinear_coverage).comp M.ambientAut

theorem fieldHom_ker (h : SourceHypotheses ρ L) : M.fieldHom.ker = L := by
  ext g
  change M.ambientAut g ∈
    (Theory.PSL2.fieldProjectionOfCoverage Theory.PSL2.semilinear_coverage).ker ↔ g ∈ L
  rw [Theory.PSL2.fieldProjectionOfCoverage_ker, M.ambientAut_mem_inner_iff h]

/-- The actual extension quotient is the subgroup of field automorphisms it induces. -/
def quotientEquivFieldImage (h : SourceHypotheses ρ L) :
    G ⧸ L ≃* M.fieldHom.range :=
  (QuotientGroup.quotientMulEquivOfEq (M.fieldHom_ker h).symm).trans
    (QuotientGroup.quotientKerEquivRange M.fieldHom)

include M in
theorem quotient_isCyclic (h : SourceHypotheses ρ L) : IsCyclic (G ⧸ L) := by
  let : IsCyclic (Field s ≃+* Field s) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  exact isCyclic_of_injective (M.quotientEquivFieldImage h).toMonoidHom
    (M.quotientEquivFieldImage h).injective

omit [Finite G] in
/-- In an odd extension every elementary two-subgroup is inside the original layer. -/
theorem elementary_le_layer_of_odd_index (hodd : Odd L.index)
    (A : Subgroup G) [IsElementaryAbelian 2 A] : A ≤ L := by
  intro a ha
  have hp : a ^ 2 = 1 := congrArg A.subtype
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) ⟨a, ha⟩)
  have hpow : (QuotientGroup.mk' L a) ^ 2 = 1 := by rw [← map_pow, hp, map_one]
  have hcard : Odd (Nat.card (G ⧸ L)) := hodd
  apply (QuotientGroup.eq_one_iff a).mp
  exact hcard.coprime_two_right.pow_left_bijective.injective (by simpa using hpow)


omit [Finite G] in
/-- Removing the inner factor realizes each occurring field action inside G. -/
theorem exists_pure_field_lift (σ : Field s ≃+* Field s) (hσ : σ ∈ M.fieldHom.range) :
    ∃ g : G, M.ambientAut g = Theory.PSL2.fieldAut σ := by
  obtain ⟨x, hx⟩ := hσ
  obtain ⟨a, τ, ha⟩ := M.ambientAut_semilinear x
  have hpa : Theory.PSL2.fieldProjectionOfCoverage Theory.PSL2.semilinear_coverage
      (MulAut.conj a) = 1 := by
    change MulAut.conj a ∈
      (Theory.PSL2.fieldProjectionOfCoverage Theory.PSL2.semilinear_coverage).ker
    rw [Theory.PSL2.fieldProjectionOfCoverage_ker]
    exact ⟨a, rfl⟩
  have he : τ = σ := by
    rw [← hx]
    change τ = Theory.PSL2.fieldProjectionOfCoverage Theory.PSL2.semilinear_coverage
      (M.ambientAut x)
    rw [ha, map_mul, hpa, one_mul, Theory.PSL2.fieldProjectionOfCoverage_fieldAut]
  subst τ
  refine ⟨(M.projectiveEquiv.symm a : G)⁻¹ * x, ?_⟩
  rw [map_mul, map_inv, M.ambientAut_layer, M.projectiveEquiv.apply_symm_apply, ha,
    inv_mul_cancel_left]

/-- Half-degree Frobenius is a nontrivial involution on the actual quadratic field. -/
theorem conjugation_order (s : ℕ) [NeZero s] : orderOf (conjugation s) = 2 := by
  apply orderOf_eq_prime
  · ext x
    exact conjugation_involutive s x
  · intro he
    obtain ⟨x, hx⟩ := exists_conjugation_ne s
    exact hx (DFunLike.congr_fun he x)

/-- Even extension index supplies an actual outer involution, with the canonical
field action on the marked layer. No linear-normalizer hypothesis is imposed. -/
theorem exists_outer_involution (h : SourceHypotheses ρ L) (heven : Even L.index) :
    ∃ t : G, t ^ 2 = 1 ∧ t ∉ L ∧
      M.ambientAut t = Theory.PSL2.fieldAut (conjugation s) := by
  have hi : Nat.card M.fieldHom.range = L.index :=
    (Nat.card_congr (M.quotientEquivFieldImage h).toEquiv).symm
  have heven' : Even (Nat.card M.fieldHom.range) := hi.symm ▸ heven
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := M.fieldHom.range) 2
    (even_iff_two_dvd.mp heven')
  let : IsCyclic (Field s ≃+* Field s) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  have hσc : σ.val = conjugation s := IsCyclic.eq_of_orderOf_eq_two
    ((Subgroup.orderOf_coe σ).trans hσ) (conjugation_order s)
  obtain ⟨t, ht⟩ := M.exists_pure_field_lift (conjugation s) (hσc ▸ σ.property)
  refine ⟨t, ?_, ?_, ht⟩
  · apply M.ambientAut_injective h
    rw [map_pow, map_one, ht]
    have ho := (Theory.PSL2.orderOf_fieldAut (conjugation s)).trans (conjugation_order s)
    simpa only [ho] using pow_orderOf_eq_one (Theory.PSL2.fieldAut (conjugation s))
  · intro htL
    have hk : M.fieldHom t = 1 := by
      change t ∈ M.fieldHom.ker
      rw [M.fieldHom_ker h]
      exact htL
    change Theory.PSL2.fieldProjectionOfCoverage Theory.PSL2.semilinear_coverage
      (M.ambientAut t) = 1 at hk
    rw [ht, Theory.PSL2.fieldProjectionOfCoverage_fieldAut] at hk
    have ho := (conjugation_order s)
    rw [hk, orderOf_one] at ho
    exact (by decide : (1 : ℕ) ≠ 2) ho

/-- Every outer involution has the same layer action up to a genuine layer
conjugation; this is stronger than an isomorphism of its fixed group. -/
theorem outer_involution_conjugate (h : SourceHypotheses ρ L)
    {t u : G} (ht : t ^ 2 = 1) (htL : t ∉ L)
    (hu : M.ambientAut u = Theory.PSL2.fieldAut (conjugation s)) :
    ∃ c : L, (c : G) * u * (c : G)⁻¹ = t := by
  obtain ⟨a, σ, heq⟩ := M.ambientAut_semilinear t
  have hta : M.ambientAut t ^ 2 = 1 := by rw [← map_pow, ht, map_one]
  have houter : M.ambientAut t ∉ Theory.PSL2.inner (Field s) :=
    fun he => htL ((M.ambientAut_mem_inner_iff h t).mp he)
  obtain ⟨hσ, c, hc⟩ := Theory.PSL2.outer_conjugate_field_of_semilinear
    (M.ambientAut t) hta a σ heq houter
  let : IsCyclic (Field s ≃+* Field s) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  have hσc : σ = conjugation s := IsCyclic.eq_of_orderOf_eq_two hσ (conjugation_order s)
  subst σ
  refine ⟨M.projectiveEquiv.symm c, ?_⟩
  apply M.ambientAut_injective h
  rw [map_mul, map_mul, map_inv, M.ambientAut_layer,
    M.projectiveEquiv.apply_symm_apply, hu, ← hc]
  ext x
  simp [MulAut.congr, MulAut.conj_apply, MulAut.conj_symm_apply, mul_assoc]


/-- An outer elementary actor has exactly two field components. -/
theorem outer_elementary_field_card (h : SourceHypotheses ρ L)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hout : ¬ A ≤ L) :
    Nat.card (A.map M.fieldHom) = 2 := by
  let : IsCyclic (Field s ≃+* Field s) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  let : IsElementaryAbelian 2 (A.map M.fieldHom) := IsElementaryAbelian.map M.fieldHom
  have hd : Nat.card (A.map M.fieldHom) ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 _
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hc | hc
  · have hb : A.map M.fieldHom = ⊥ := Subgroup.card_eq_one.mp hc
    have hle : A ≤ M.fieldHom.ker := by
      intro a ha
      have hm := Subgroup.mem_map_of_mem M.fieldHom ha
      rw [hb, Subgroup.mem_bot] at hm
      exact hm
    rw [M.fieldHom_ker h] at hle
    exact (hout hle).elim
  · exact hc

include M in
/-- The rank increase of an outer elementary actor is exactly one. -/
theorem outer_elementary_rank (h : SourceHypotheses ρ L)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hout : ¬ A ≤ L) :
    rank A = rank (A ⊓ L) + 1 := by
  have hprod := IsElementaryAbelian.card_inf_ker_mul_card_map A M.fieldHom
  rw [M.fieldHom_ker h, M.outer_elementary_field_card h A hout] at hprod
  obtain ⟨n, hn⟩ := ((IsElementaryAbelian.isPGroup 2 A).to_le
    (show A ⊓ L ≤ A from inf_le_left)).exists_card_eq
  change Nat.log 2 (Nat.card A) = Nat.log 2 (Nat.card (A ⊓ L : Subgroup G)) + 1
  rw [← hprod, hn, ← pow_succ, Nat.log_pow Nat.one_lt_two, Nat.log_pow Nat.one_lt_two]

/-- Every element of an elementary actor has field component either identity
or the same component as any chosen outer involution. -/
theorem elementary_field_dichotomy (h : SourceHypotheses ρ L)
    (A : Subgroup G) [IsElementaryAbelian 2 A] {t : G} (ht : t ∈ A) (htL : t ∉ L)
    {a : G} (ha : a ∈ A) : M.fieldHom a = 1 ∨ M.fieldHom a = M.fieldHom t := by
  by_cases ha1 : M.fieldHom a = 1
  · exact Or.inl ha1
  right
  let : IsCyclic (Field s ≃+* Field s) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  apply IsCyclic.eq_of_orderOf_eq_two
  · apply orderOf_eq_prime
    · rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian a ha, map_one]
    · exact ha1
  · apply orderOf_eq_prime
    · rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian t ht, map_one]
    · intro ht1
      apply htL
      have hm : t ∈ M.fieldHom.ker := ht1
      rwa [M.fieldHom_ker h] at hm

include M in
/-- The actual outer elementary actor is its inner intersection times its
chosen outer involution. This uses the literal intersection in G. -/
theorem outer_elementary_decomposition (h : SourceHypotheses ρ L)
    (A : Subgroup G) [IsElementaryAbelian 2 A] {t : G} (ht : t ∈ A) (htL : t ∉ L) :
    A = (A ⊓ L) ⊔ zpowers t := by
  apply le_antisymm
  · intro a ha
    rcases M.elementary_field_dichotomy h A ht htL ha with ha1 | hat
    · have haL : a ∈ L := by
        have hm : a ∈ M.fieldHom.ker := ha1
        rwa [M.fieldHom_ker h] at hm
      exact (le_sup_left : A ⊓ L ≤ (A ⊓ L) ⊔ zpowers t) ⟨ha, haL⟩
    · have hatL : a * t⁻¹ ∈ L := by
        rw [← M.fieldHom_ker h]
        change M.fieldHom (a * t⁻¹) = 1
        rw [map_mul, map_inv, hat, mul_inv_cancel]
      have hm : a * t⁻¹ ∈ (A ⊓ L) ⊔ zpowers t :=
        (le_sup_left : A ⊓ L ≤ (A ⊓ L) ⊔ zpowers t) ⟨A.mul_mem ha (A.inv_mem ht), hatL⟩
      simpa only [inv_mul_cancel_right] using
        ((A ⊓ L) ⊔ zpowers t).mul_mem hm ((le_sup_right : zpowers t ≤ (A ⊓ L) ⊔ zpowers t) (mem_zpowers t))
  · exact sup_le inf_le_left (zpowers_le.mpr ht)

end OrthogonalModel

/-- The actual source actor has a cyclic field quotient. Odd extensions contain
all elementary two-subgroups in L; even extensions contain the canonical field
involution as an element of G. Linear realization and fixed spaces are separate
from this group-theoretic reduction. -/
theorem SourceHypotheses.orthogonal_ambient_alternatives (h : SourceHypotheses ρ L)
    (M : OrthogonalModel s ρ L) :
    let : L.Normal := h.layer_normal
    IsCyclic (G ⧸ L) ∧
      ((Odd L.index ∧ ∀ A : Subgroup G, IsElementaryTwo A → A ≤ L) ∨
       (Even L.index ∧ ∃ t : G, t ^ 2 = 1 ∧ t ∉ L ∧
          M.ambientAut t = Theory.PSL2.fieldAut (conjugation s))) := by
  let : L.Normal := h.layer_normal
  refine ⟨M.quotient_isCyclic h, ?_⟩
  rcases Nat.even_or_odd L.index with he | ho
  · exact Or.inr ⟨he, M.exists_outer_involution h he⟩
  · refine Or.inl ⟨ho, ?_⟩
    intro A hA
    let : IsElementaryAbelian 2 A := hA.2
    exact OrthogonalModel.elementary_le_layer_of_odd_index ho A

end CFSG.Quasithin.ChapterK.RankOne
