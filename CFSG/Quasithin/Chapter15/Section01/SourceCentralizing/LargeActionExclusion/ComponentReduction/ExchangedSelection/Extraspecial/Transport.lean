module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.Definitions

/-!+# Pointwise subspace stabilizers in the original action image

The full preimage of a pointwise stabilizer is the literal centralizer of
the corresponding subgroup of V. Its faithful quotient and residual retain
the original action map. This extends the cyclic-vector transport to the
four-subgroup in Notation 15.1.16(c), Aschbacher--Smith, printed p.1092.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
variable (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (W : Submodule (ZMod 2) (Additive V))

omit [Finite G] in
/-- Pointwise fixedness in the faithful image is ambient centralization. -/
theorem image_mem_kernel_iff (m : M) :
    (actionHom M V hn).rangeRestrict m ∈
      subspaceKernel (imageRepresentation M V hn) W ⊤ ↔
    (m : G) ∈ centralizer ((binarySubgroup W).map V.subtype : Set G) := by
  change (True ∧ ∀ v ∈ W,
    imageRepresentation M V hn ((actionHom M V hn).rangeRestrict m) v = v) ↔ _
  constructor
  · rintro ⟨_,hm⟩ z ⟨v,hv,rfl⟩
    have he := congrArg (fun w : Additive V => (w.toMul : G)) (hm (Additive.ofMul v) hv)
    change (m : G) * v * (m : G)⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hm
    refine ⟨True.intro,?_⟩
    intro v hv
    apply Additive.toMul.injective
    apply Subtype.ext
    change (m : G) * v.toMul * (m : G)⁻¹ = v.toMul
    have hc : (m : G) * (v.toMul : G) = (v.toMul : G) * m :=
      (hm v.toMul (mem_map_of_mem V.subtype hv)).symm
    rw [hc,mul_inv_cancel_right]

omit [Finite G] in
theorem stabilizer_preimage :
    ((subspaceKernel (imageRepresentation M V hn) W ⊤).comap
      (actionHom M V hn).rangeRestrict).map M.subtype =
    M ⊓ centralizer ((binarySubgroup W).map V.subtype : Set G) := by
  ext x
  constructor
  · rintro ⟨m,hm,rfl⟩
    exact ⟨m.property,(image_mem_kernel_iff M V hn W m).mp hm⟩
  · intro hx
    exact ⟨⟨x,hx.1⟩,(image_mem_kernel_iff M V hn W ⟨x,hx.1⟩).mpr hx.2,rfl⟩

omit [Finite G] in
/-- Surjection onto the same pointwise stabilizer, with its exact kernel. -/
theorem stabilizer_projection :
    let K := subspaceKernel (imageRepresentation M V hn) W ⊤
    let C := M ⊓ centralizer ((binarySubgroup W).map V.subtype : Set G)
    ∃ q : C →* K, Function.Surjective q ∧
      q.ker = (M ⊓ centralizer (V : Set G)).subgroupOf C ∧
      ∀ x : C, (q x : internalActionImage M V hn) =
        (actionHom M V hn).rangeRestrict ⟨x,x.property.1⟩ := by
  let K := subspaceKernel (imageRepresentation M V hn) W ⊤
  let C := M ⊓ centralizer ((binarySubgroup W).map V.subtype : Set G)
  let f : M →* internalActionImage M V hn := (actionHom M V hn).rangeRestrict
  let q : C →* K := (f.comp (inclusion (show C ≤ M from inf_le_left))).codRestrict K
    (fun x => (image_mem_kernel_iff M V hn W ⟨x,x.property.1⟩).mpr x.property.2)
  have hq : Function.Surjective q := by
    intro k
    obtain ⟨m,hm⟩ := (actionHom M V hn).rangeRestrict_surjective (k : internalActionImage M V hn)
    have hmk : f m ∈ K := hm.symm ▸ k.property
    exact ⟨⟨m,m.property,(image_mem_kernel_iff M V hn W m).mp hmk⟩,Subtype.ext hm⟩
  refine ⟨q,hq,?_,fun _ => rfl⟩
  ext x
  constructor
  · intro hx
    have ha : (actionHom M V hn) ⟨x,x.property.1⟩ = 1 :=
      congrArg (fun d : K => ((d : internalActionImage M V hn) : MulAut V)) hx
    have hc : (⟨x,x.property.1⟩ : M) ∈ (actionHom M V hn).ker := ha
    rw [actionHom_ker] at hc
    exact ⟨x.property.1,hc⟩
  · intro hx
    apply Subtype.ext
    apply Subtype.ext
    change (⟨x,x.property.1⟩ : M) ∈ (actionHom M V hn).ker
    rw [actionHom_ker]
    exact hx.2

/-- Transport the faithful quotient residual order through the actual map. -/
theorem residual_card :
    let K := subspaceKernel (imageRepresentation M V hn) W ⊤
    let Z := (binarySubgroup W).map V.subtype
    let C := M ⊓ centralizer (Z : Set G)
    letI := caseI_module_centralizer_normal (Z1 := Z) hn
    Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) =
      Nat.card (pResidual 2 K) := by
  dsimp only
  let := caseI_module_centralizer_normal (Z1 := (binarySubgroup W).map V.subtype) hn
  obtain ⟨q,hq,hker,_⟩ := stabilizer_projection M V hn W
  let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have he := map_pResidual_of_surjective 2 e.toMonoidHom e.surjective
  exact (Nat.card_congr ((pResidual 2 _).equivMapOfInjective e.toMonoidHom e.injective).toEquiv).trans
    (Nat.card_congr (MulEquiv.subgroupCongr he).toEquiv)

/-- The original residual has precisely the image stabilizer residual. -/
theorem residual_action_image :
    let K := subspaceKernel (imageRepresentation M V hn) W ⊤
    let C := M ⊓ centralizer ((binarySubgroup W).map V.subtype : Set G)
    let R := (pResidual 2 C).map C.subtype
    let hRM : R ≤ M := (map_subtype_le _).trans inf_le_left
    ((actionHom M V hn).rangeRestrict.comp (inclusion hRM)).range =
      (pResidual 2 K).map K.subtype := by
  dsimp only
  let K := subspaceKernel (imageRepresentation M V hn) W ⊤
  let C := M ⊓ centralizer ((binarySubgroup W).map V.subtype : Set G)
  let R := (pResidual 2 C).map C.subtype
  let hRM : R ≤ M := (map_subtype_le _).trans inf_le_left
  let f : M →* internalActionImage M V hn := (actionHom M V hn).rangeRestrict
  let a := f.comp (inclusion hRM)
  obtain ⟨q,hq,_,hcoord⟩ := stabilizer_projection M V hn W
  have he := map_pResidual_of_surjective 2 q hq
  change a.range = _
  rw [←he,map_map]
  ext d
  constructor
  · rintro ⟨r,rfl⟩
    obtain ⟨c,hc,hcr⟩ := r.property
    refine ⟨c,hc,?_⟩
    change (q c : internalActionImage M V hn) = f (inclusion hRM r)
    rw [hcoord]
    congr 1
    exact Subtype.ext hcr
  · rintro ⟨c,hc,rfl⟩
    refine ⟨⟨c,mem_map_of_mem C.subtype hc⟩,?_⟩
    exact (hcoord c).symm

/-- Fixed and moved subgroups use the same literal ambient residual. -/
theorem residual_spaces :
    let K := subspaceKernel (imageRepresentation M V hn) W ⊤
    let C := M ⊓ centralizer ((binarySubgroup W).map V.subtype : Set G)
    let R := (pResidual 2 C).map C.subtype
    (V ⊓ centralizer (R : Set G)).subgroupOf V =
      binarySubgroup (fixedSpace (imageRepresentation M V hn) ((pResidual 2 K).map K.subtype)) ∧
    ⁅V,R⁆.subgroupOf V = binarySubgroup
      (subspaceCommutator (imageRepresentation M V hn) ⊤ ((pResidual 2 K).map K.subtype)) := by
  intro K C R
  let hRM : R ≤ M := (map_subtype_le _).trans inf_le_left
  let a : R →* internalActionImage M V hn :=
    (actionHom M V hn).rangeRestrict.comp (inclusion hRM)
  have he : a.range = (pResidual 2 K).map K.subtype := residual_action_image M V hn W
  constructor
  · rw [←he]
    ext w
    constructor
    · intro hw
      rintro ⟨d,⟨r,rfl⟩⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      change (r : G) * (w : G) * (r : G)⁻¹ = w
      have hc : (r : G) * (w : G) = (w : G) * r := hw.2 r r.property
      rw [hc,mul_inv_cancel_right]
    · intro hw
      refine ⟨w.property,?_⟩
      intro r hr
      have hh := hw ⟨a ⟨r,hr⟩,⟨⟨r,hr⟩,rfl⟩⟩
      have hh' := congrArg (fun u : Additive V => (u.toMul : G)) hh
      change r * (w : G) * r⁻¹ = w at hh'
      exact mul_inv_eq_iff_eq_mul.mp hh'
  · have hh := commutator_image_eq (imageRepresentation M V hn) V V R
      (hRM.trans hn) le_rfl a (MonoidHom.id V) (fun _ _ => rfl) ⊤ (by
        ext x
        simp [binarySubgroup])
    simpa only [map_id,he] using hh

end CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker
