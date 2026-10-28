module
public import Theory.Representation.PSL3Two.NaturalDualEmbedding

/-!
# Two natural--dual component actions

The original embeddings and fixed supplement make the two component action
maps jointly faithful. The image ranks bound the full actor rank, while the
fixed codimensions add. The no-FF theorem for each natural--dual pair therefore
excludes offenders on their sum. A quadratic rank-two component image is inner
and has fixed codimension three, without assuming a budget on that component.

These are the representation estimates in Aschbacher--Smith 14.6.24(c)--(i),
printed pp.1039--1040. The ambient critical point and component containment
arguments are supplied by the Chapter14 consumers.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryLinearThree.NaturalDual.Paired
variable {H E : Type*} [_root_.Group H] [AddCommGroup E] [Module (ZMod 2) E]

/-- Two actual natural--dual component supports, with a fixed supplement.
The action maps are allowed to have kernels; joint faithfulness is proved. -/
structure Marking (ρ : Representation (ZMod 2) H E) where
  left : H →* MulAut Group
  right : H →* MulAut Group
  leftEmbedding : Space →ₗ[ZMod 2] E
  rightEmbedding : Space →ₗ[ZMod 2] E
  left_injective : Function.Injective leftEmbedding
  right_injective : Function.Injective rightEmbedding
  disjoint : Disjoint leftEmbedding.range rightEmbedding.range
  span : leftEmbedding.range ⊔ rightEmbedding.range ⊔ fixedSpace ρ ⊤ = ⊤
  left_intertwines : ∀ a v, ρ a (leftEmbedding v) = leftEmbedding (autAction (left a) v)
  right_intertwines : ∀ a v, ρ a (rightEmbedding v) = rightEmbedding (autAction (right a) v)

namespace Marking
variable {ρ : Representation (ZMod 2) H E} (m : Marking ρ)

/-- Neither component action need be faithful by itself. Together they
are faithful because they control both supports and the fixed supplement. -/
theorem joint_injective (hf : Function.Injective ρ) :
    Function.Injective (m.left.prod m.right) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  have hl : m.left a = 1 := congrArg Prod.fst ha
  have hr : m.right a = 1 := congrArg Prod.snd ha
  apply hf
  apply LinearMap.ext
  intro v
  have hv : v ∈ m.leftEmbedding.range ⊔ m.rightEmbedding.range ⊔ fixedSpace ρ ⊤ := by
    rw [m.span]; trivial
  obtain ⟨w,hw,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨x,⟨x',rfl⟩,y,⟨y',rfl⟩,rfl⟩ := Submodule.mem_sup.mp hw
  have hfixed : ρ a z = z := hz ⟨a,mem_top a⟩
  simp only [map_add,m.left_intertwines,m.right_intertwines,hl,hr,map_one,
    Module.End.one_apply,hfixed]

private noncomputable def sumEmbedding : Space × Space →ₗ[ZMod 2] E :=
  m.leftEmbedding.coprod m.rightEmbedding

private theorem sumEmbedding_injective : Function.Injective m.sumEmbedding := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  rintro ⟨x,y⟩ hxy
  change m.leftEmbedding x + m.rightEmbedding y = 0 at hxy
  have hleft : m.leftEmbedding x = 0 := Submodule.disjoint_def.mp m.disjoint _
    ⟨x,rfl⟩ ⟨-y,by simpa only [map_neg] using eq_neg_of_add_eq_zero_left hxy |>.symm⟩
  have hright : m.rightEmbedding y = 0 := by rw [hleft,zero_add] at hxy; exact hxy
  exact Prod.ext (m.left_injective (hleft.trans (map_zero _).symm))
    (m.right_injective (hright.trans (map_zero _).symm))

variable [FiniteDimensional (ZMod 2) E]

/-- The two component displacement costs add on the same actor, even with
an additional fixed factor. -/
theorem sum_fixedCodim_le (A : Subgroup H) :
    fixedCodim autAction (A.map m.left) + fixedCodim autAction (A.map m.right) ≤
      fixedCodim ρ A := by
  let σ : Representation (ZMod 2) H (Space × Space) :=
    Representation.prod (autAction.comp m.left) (autAction.comp m.right)
  have he : ∀ a v, ρ a (m.sumEmbedding v) = m.sumEmbedding (σ a v) := by
    intro a v
    change ρ a (m.leftEmbedding v.1 + m.rightEmbedding v.2) = _
    rw [map_add,m.left_intertwines,m.right_intertwines]
    rfl
  have hh := fixedCodim_map_le_of_embedding ρ σ (MonoidHom.id H)
    m.sumEmbedding m.sumEmbedding_injective he A
  rw [Subgroup.map_id,fixedCodim_prod] at hh
  rw [←fixedCodim_map_equivariant (autAction.comp m.left) autAction m.left
    (LinearEquiv.refl _ _) (fun _ _ => rfl),
    ←fixedCodim_map_equivariant (autAction.comp m.right) autAction m.right
    (LinearEquiv.refl _ _) (fun _ _ => rfl)]
  exact hh

private theorem elementary_card {J : Type*} [_root_.Group J] [Finite J]
    (A : Subgroup J) [IsElementaryAbelian 2 A] : Nat.card A = 2 ^ rank A := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  rw [rank,hn,Nat.log_pow (by decide : 1 < 2)]

variable [Finite H]

omit [FiniteDimensional (ZMod 2) E] in
/-- The literal projections bound the actor rank by the sum of their ranks. -/
theorem rank_le_sum (hf : Function.Injective ρ)
    (A : Subgroup H) [IsElementaryAbelian 2 A] :
    rank A ≤ rank (A.map m.left) + rank (A.map m.right) := by
  let f : A → (A.map m.left) × (A.map m.right) := fun a =>
    (⟨m.left a,mem_map_of_mem _ a.property⟩,⟨m.right a,mem_map_of_mem _ a.property⟩)
  have hf' : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply m.joint_injective hf
    exact Prod.ext (congrArg (fun x => x.1.val) he) (congrArg (fun x => x.2.val) he)
  let : IsElementaryAbelian 2 (A.map m.left) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (A.map m.right) := IsElementaryAbelian.map _
  have hc := Nat.card_le_card_of_injective f hf'
  rw [Nat.card_prod,elementary_card A,elementary_card (A.map m.left),
    elementary_card (A.map m.right),←pow_add] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

private theorem local_rank_bound (A : Subgroup (MulAut Group))
    [IsElementaryAbelian 2 A] : rank A ≤ 2 := by
  by_cases hn : A = ⊥
  · simp [hn]
  · rcases LowRankProfiles.rank_one_or_two A ⟨hn,inferInstance⟩ with h | h <;> omega

omit [FiniteDimensional (ZMod 2) E] [Finite H] in
/-- Each actual component image has rank at most two. -/
theorem image_ranks_le_two (A : Subgroup H) [IsElementaryAbelian 2 A] :
    rank (A.map m.left) ≤ 2 ∧ rank (A.map m.right) ≤ 2 := by
  let : IsElementaryAbelian 2 (A.map m.left) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (A.map m.right) := IsElementaryAbelian.map _
  exact ⟨local_rank_bound _,local_rank_bound _⟩

private theorem local_rank_le_codim (A : Subgroup (MulAut Group))
    [IsElementaryAbelian 2 A] : rank A ≤ fixedCodim autAction A := by
  by_cases hn : A = ⊥
  · simp [hn]
  · exact (Nat.lt_of_not_ge (fun hh => not_isFFModule_autAction
      ⟨A,⟨hn,inferInstance⟩,hh⟩)).le

omit [FiniteDimensional (ZMod 2) E] [Finite H] in
/-- Both components acting nontrivially costs at least one extra dimension
per component, as in 14.6.24(c). -/
theorem image_rank_lt_codim (A : Subgroup H) [IsElementaryAbelian 2 A] :
    (A.map m.left ≠ ⊥ → rank (A.map m.left) < fixedCodim autAction (A.map m.left)) ∧
    (A.map m.right ≠ ⊥ → rank (A.map m.right) < fixedCodim autAction (A.map m.right)) := by
  let : IsElementaryAbelian 2 (A.map m.left) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (A.map m.right) := IsElementaryAbelian.map _
  constructor <;> intro hn <;>
    exact Nat.lt_of_not_ge (fun hh => not_isFFModule_autAction ⟨_,⟨hn,inferInstance⟩,hh⟩)

include m in
/-- A faithful marked pair, including its fixed supplement, has no offender. -/
theorem not_ff (hf : Function.Injective ρ) : ¬ IsFFModule ρ := by
  rintro ⟨A,hA⟩
  let : IsElementaryAbelian 2 A := hA.1.2
  let : IsElementaryAbelian 2 (A.map m.left) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (A.map m.right) := IsElementaryAbelian.map _
  have hr := m.rank_le_sum hf A
  have hd := m.sum_fixedCodim_le A
  have hl := local_rank_le_codim (A.map m.left)
  have hh := local_rank_le_codim (A.map m.right)
  have he := m.image_rank_lt_codim A
  have hnon : A.map m.left ≠ ⊥ ∨ A.map m.right ≠ ⊥ := by
    by_contra! hn
    have hp := hA.1.rank_pos
    rw [hn.1,hn.2,Representation.BinaryOffender.rank_bot,zero_add] at hr
    omega
  have hbound := hA.2
  rcases hnon with hn | hn
  · have := he.1 hn; omega
  · have := he.2 hn; omega

omit [FiniteDimensional (ZMod 2) E] [Finite H] in
/-- Centralizing the second component leaves a faithful action on the first,
with the same rank, now at most two. -/
theorem rank_eq_left_of_right_trivial (hf : Function.Injective ρ)
    (A : Subgroup H) [IsElementaryAbelian 2 A] (hr : A ≤ m.right.ker) :
    rank A = rank (A.map m.left) ∧ rank A ≤ 2 := by
  have hj : Function.Injective (m.left.comp A.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    apply Subtype.ext
    apply m.joint_injective hf
    change (m.left a, m.right a) = (m.left 1, m.right 1)
    simp only [map_one]
    exact Prod.ext ha (hr a.property)
  have he := rank_map_injective (m.left.comp A.subtype) hj (⊤ : Subgroup A)
  have hmap : (⊤ : Subgroup A).map (m.left.comp A.subtype) = A.map m.left := by
    ext x
    constructor
    · rintro ⟨a,_,rfl⟩
      exact mem_map_of_mem _ a.property
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,mem_top _,rfl⟩
  rw [hmap] at he
  have ht : rank (⊤ : Subgroup A) = rank A := by
    exact congrArg (Nat.log 2) (Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toEquiv)
  rw [ht] at he
  exact ⟨he.symm,he ▸ (m.image_ranks_le_two A).1⟩

omit [FiniteDimensional (ZMod 2) E] [Finite H] in
/-- The same quadratic actor acts quadratically on both marked component images. -/
theorem quadratic_images (A : Subgroup H) (hq : IsQuadratic ρ A) :
    IsQuadratic autAction (A.map m.left) ∧ IsQuadratic autAction (A.map m.right) := by
  constructor
  · rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
    apply m.left_injective
    have hh := hq a ha b hb (m.leftEmbedding v)
    simpa only [m.left_intertwines,←map_sub] using hh
  · rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
    apply m.right_injective
    have hh := hq a ha b hb (m.rightEmbedding v)
    simpa only [m.right_intertwines,←map_sub] using hh
end Marking

/-- A quadratic rank-two component image is inner and has fixed codimension
three. No quadratic budget on that individual component is assumed. -/
theorem rank_two_profile (A : Subgroup (MulAut Group)) [IsElementaryAbelian 2 A]
    (hq : IsQuadratic autAction A) (hr : rank A = 2) :
    A ≤ MulAut.innerSubgroup Group ∧ fixedCodim autAction A = 3 := by
  have hcard : Nat.card A = 4 := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    have he : n = 2 := by simpa only [rank,hn,Nat.log_pow (by decide : 1 < 2)] using hr
    norm_num [hn,he]
  have hi := LowRankProfiles.inner_of_quadratic_of_card_gt_two autAction autAction_inner
    A inferInstance (by omega) hq
  refine ⟨hi,?_⟩
  have hc : Nat.card (fixedSpace autAction A) = 8 := by
    rw [LowRankProfiles.fixedSpace_eq_naturalDualFixed autAction autAction_inner A hi]
    exact (FourGroupGeometry.FixedSpaces.naturalDualFixed_geometry A hi inferInstance hcard).1
  have hd : Module.finrank (ZMod 2) (fixedSpace autAction A) = 3 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) hc
  have hs := fixedCodim_add_finrank autAction A
  have he : Module.finrank (ZMod 2) Space = 6 := by
    change Module.finrank (ZMod 2) (Vector × Module.Dual (ZMod 2) Vector) = 6
    rw [Module.finrank_prod,Subspace.dual_finrank_eq]
    norm_num [Vector,Matrix.PSL3Two.Fano.Vector]
  omega
end BinaryLinearThree.NaturalDual.Paired
