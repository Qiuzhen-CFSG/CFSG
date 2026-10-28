module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.Reduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FixedCoordinates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.Transport.Coordinates
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.SylowCard

/-!
# Transport of the finite star bound to the actual max1 Sylow group

The literal local quotient maps onto the star group. Sylow conjugacy, lifted
back to the local group, aligns any local Sylow image with the certified fixed
candidate. The resulting surjection has exactly the restricted local kernel,
so subgroup images have the same order as their actual quotient images.

Conjugating a centralizing kernel element by the same lift and taking its
unique binary mask injects the kernel centralizer into the masks fixed by the
aligned image. Thus the finite normal elementary fixed-mask bound implies the
intrinsic quotient-centralizer bound, with the finite bound retained as an
explicit premise.

Source: the ATLAS max1 words and kernel/star certificates documented in
`Cardinality.Subgroup` and `Image.Comparison`; Kleidman–Wilson, *The maximal
subgroups of J₄* (1988), and GLS3 Table 5.3i. The Sylow argument uses only the
certified local quotient and star candidate orders.
-/

set_option backward.isDefEq.respectTransparency true

@[expose] public section
namespace Janko4.LocalStructure.SylowCore.Transport
open Subgroup Cardinality Cardinality.QuotientCount Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion.QuotientInvolutions
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup

local notation "π" => starProjection matrixA_mul_self matrixB_pow_four
local notation "E" => localKernel matrixA_mul_self matrixB_pow_four

private theorem fixedCandidate_isSylow :
    ∃ S : Sylow 2 StarGroup, S.toSubgroup = sylowCandidate := by
  have hp : IsPGroup 2 sylowCandidate := IsPGroup.of_card (n := 10) sylowCandidate_card
  have hind : ¬ 2 ∣ sylowCandidate.index := by
    have hi := sylowCandidate.card_mul_index
    rw [sylowCandidate_card, starGroup_order] at hi
    have he : sylowCandidate.index = 239085 := by omega
    rw [he]
    decide
  exact ⟨hp.toSylow hind, rfl⟩

/-- Lift Sylow conjugacy through the actual quotient. -/
theorem exists_alignment (P : Sylow 2 Local) :
    ∃ g : Local, P.toSubgroup.map ((π).comp (MulAut.conj g).toMonoidHom) = sylowCandidate := by
  let Q := P.mapSurjective (starProjection_surjective matrixA_mul_self matrixB_pow_four)
  obtain ⟨S, hS⟩ := fixedCandidate_isSylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq StarGroup Q S
  obtain ⟨g, rfl⟩ := starProjection_surjective matrixA_mul_self matrixB_pow_four c
  refine ⟨g, ?_⟩
  have he := congrArg Sylow.toSubgroup hc
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at he
  have hQ : Q.toSubgroup = P.toSubgroup.map π := rfl
  rw [hQ, hS] at he
  change (P.toSubgroup.map π).map (MulAut.conj (π g)).toMonoidHom = sylowCandidate at he
  rw [Subgroup.map_map] at he
  convert he using 1
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.conj_apply, map_mul, map_inv]

/-- The aligned image map, with the fixed Sylow as its codomain. -/
noncomputable def alignedHom (P : Sylow 2 Local) (g : Local)
    (hg : P.toSubgroup.map ((π).comp (MulAut.conj g).toMonoidHom) = sylowCandidate) :
    P →* sylowCandidate :=
  (((π).comp (MulAut.conj g).toMonoidHom).comp P.toSubgroup.subtype).codRestrict
    sylowCandidate (fun x => by
      rw [← hg]
      exact ⟨x.val, x.property, rfl⟩)

theorem alignedHom_surjective (P : Sylow 2 Local) (g : Local)
    (hg : P.toSubgroup.map ((π).comp (MulAut.conj g).toMonoidHom) = sylowCandidate) :
    Function.Surjective (alignedHom P g hg) := by
  intro y
  have hy : y.val ∈ P.toSubgroup.map ((π).comp (MulAut.conj g).toMonoidHom) := by
    simpa only [hg] using y.property
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem alignedHom_ker (P : Sylow 2 Local) (g : Local)
    (hg : P.toSubgroup.map ((π).comp (MulAut.conj g).toMonoidHom) = sylowCandidate) :
    (alignedHom P g hg).ker = core P := by
  ext x
  change (alignedHom P g hg x = 1) ↔ x.val ∈ E
  rw [Subtype.ext_iff]
  change π ((MulAut.conj g) x.val) = 1 ↔ _
  change (MulAut.conj g) x.val ∈ (π).ker ↔ _
  rw [starProjection_ker]
  constructor
  · intro hx
    have hn := (inferInstance : (E).Normal).conj_mem _ hx g⁻¹
    simpa only [MulAut.conj_apply, inv_inv, ← mul_assoc, inv_mul_cancel, one_mul,
      inv_mul_cancel_right] using hn
  · intro hx
    exact (inferInstance : (E).Normal).conj_mem _ hx g

/-- The aligned image has exactly the order of the image in the actual quotient. -/
theorem alignedHom_image_card (P : Sylow 2 Local) (g : Local)
    (hg : P.toSubgroup.map ((π).comp (MulAut.conj g).toMonoidHom) = sylowCandidate)
    (A : Subgroup P) :
    Nat.card (A.map (alignedHom P g hg)) =
      Nat.card (A.map (QuotientGroup.mk' (core P))) := by
  rw [← relIndex_ker, ← relIndex_ker, alignedHom_ker, QuotientGroup.ker_mk']

/-- Core restriction retains the literal kernel element. -/
noncomputable def coreEquiv (P : Sylow 2 Local) : core P ≃* E :=
  Subgroup.subgroupOfEquivOfLe (localKernel_le_sylow P)

@[simp] theorem coreEquiv_val (P : Sylow 2 Local) (x : core P) :
    (coreEquiv P x).val = x.val.val := rfl

private theorem centralizer_fixed (P : Sylow 2 Local) (A : Subgroup P)
    (x : (centralizer (A : Set P)).subgroupOf (core P)) (a : P) (ha : a ∈ A) :
    action matrixA_mul_self matrixB_pow_four a.val (coreEquiv P x.val) = coreEquiv P x.val := by
  apply Subtype.ext
  rw [action_apply, coreEquiv_val]
  have hc := (mem_centralizer_iff.mp x.property) a ha
  have hv := congrArg (fun p : P => p.val) hc
  change a.val * x.val.val.val = x.val.val.val * a.val at hv
  rw [hv, mul_inv_cancel_right]

/-- Conjugating both the actor and the kernel element preserves fixed points. -/
private theorem conjugated_fixed (P : Sylow 2 Local) (A : Subgroup P)
    (x : (centralizer (A : Set P)).subgroupOf (core P)) (a : P) (ha : a ∈ A) (g : Local) :
    action matrixA_mul_self matrixB_pow_four ((MulAut.conj g) a.val)
      (action matrixA_mul_self matrixB_pow_four g (coreEquiv P x.val)) =
        action matrixA_mul_self matrixB_pow_four g (coreEquiv P x.val) := by
  simp only [MulAut.conj_apply, map_mul, map_inv, Equiv.Perm.mul_apply]
  simpa using congrArg (action matrixA_mul_self matrixB_pow_four g)
    (centralizer_fixed P A x a ha)

/-- Inject the actual kernel centralizer into the bounded masks fixed by the aligned image. -/
theorem centralizer_card_le_fixedMasks (P : Sylow 2 Local) (A : Subgroup P) (g : Local)
    (hg : P.toSubgroup.map ((π).comp (MulAut.conj g).toMonoidHom) = sylowCandidate) :
    Nat.card ((centralizer (A : Set P)).subgroupOf (core P)) ≤
      Nat.card (FixedMasks (A.map (alignedHom P g hg))) := by
  let e := maskEquiv matrixA_mul_self matrixB_pow_four
  let c := action matrixA_mul_self matrixB_pow_four g
  let code := fun x : (centralizer (A : Set P)).subgroupOf (core P) =>
    e.symm (c (coreEquiv P x.val))
  have hfix (x : (centralizer (A : Set P)).subgroupOf (core P)) :
      ∀ b : A.map (alignedHom P g hg), starMask b.val.val (code x).val = (code x).val := by
    intro b
    obtain ⟨a, ha, hab⟩ := b.property
    have hb : b.val.val = π ((MulAut.conj g) a.val) := congrArg Subtype.val hab.symm
    rw [hb]
    have he : e ⟨starMask (π ((MulAut.conj g) a.val)) (code x).val, starMask_lt _ _⟩ =
        e (code x) := by
      rw [maskEquiv_starMask]
      change action matrixA_mul_self matrixB_pow_four ((MulAut.conj g) a.val)
        (e (e.symm (c (coreEquiv P x.val)))) = e (e.symm (c (coreEquiv P x.val)))
      rw [e.apply_symm_apply]
      exact conjugated_fixed P A x a ha g
    exact congrArg Fin.val (e.injective he)
  let f : (centralizer (A : Set P)).subgroupOf (core P) →
      FixedMasks (A.map (alignedHom P g hg)) := fun x => ⟨code x, hfix x⟩
  have : Finite (FixedMasks (A.map (alignedHom P g hg))) := by
    unfold FixedMasks
    infer_instance
  apply Nat.card_le_card_of_injective f
  intro x y hxy
  have he := congrArg Subtype.val hxy
  exact Subtype.ext ((coreEquiv P).injective (c.injective (e.symm.injective he)))

end Janko4.LocalStructure.SylowCore.Transport

namespace Janko4.LocalStructure.SylowCore
open Subgroup Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion.QuotientInvolutions Transport
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.localKernel
  Cardinality.max1Subgroup

/-- The finite fixed-mask inequality implies the inequality in the actual local Sylow group. -/
theorem quotientCentralizerBound_of_fixedBound (h : NormalElementaryFixedBound) :
    QuotientCentralizerBound := by
  intro P A hA hAe hn
  let := hA
  let := hAe
  obtain ⟨g, hg⟩ := exists_alignment P
  let f := alignedHom P g hg
  have hB : (A.map f).Normal := hA.map f (alignedHom_surjective P g hg)
  have hBe : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hBn : A.map f ≠ ⊥ := by
    rw [ne_eq, Subgroup.map_eq_bot_iff, alignedHom_ker]
    exact hn
  have hc := h (A.map f) hB hBe hBn
  have hcard := alignedHom_image_card P g hg A
  rw [← hcard]
  exact (Nat.mul_le_mul_left _ (centralizer_card_le_fixedMasks P A g hg)).trans hc

end Janko4.LocalStructure.SylowCore
