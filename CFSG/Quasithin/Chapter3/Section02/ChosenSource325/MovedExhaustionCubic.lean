module

public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.Setup
public import CFSG.Quasithin.ChapterD.Section02.StarredConjugacy
public import CFSG.Quasithin.ChapterD.Section02.Inheritance

/-!
# Minimal cubic actors and the original section centralizers

Choose an inclusion-minimal cubic actor in the specified Sylow subgroup.
For an internal section W of U, identify its action kernel with the image
of the original centralizer in the full actor preimage. Fixed codimension
is the rank difference for W and its literal fixed subgroup. D.2.7 then
gives centralization, strict decrease, or faithful action with a fixed-space
supplement, and the kernel and section share the same actor rank budget.

The actual chosen-seed application is `SeedAlternativesMovedExhaustionCubic`.
These are the quotient and numerical steps used by D.3.19 and its final
contradiction. The model and centralizer exclusions in D.3.12--18 remain
with the source325 assembly; no multiplicity bound is assumed here.
Source: Aschbacher--Smith D.2.7--8 and D.3.19, printed pp.179--180,203--204.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterD
variable {H E : Type*} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E] (ρ : Representation (ZMod 2) H E)

/-- The cubic minimum is attained by an inclusion-minimal elementary actor
inside any specified Sylow two-subgroup, using actual conjugation. -/
theorem exists_starred_in_sylow (S : Sylow 2 H) (hq : cubicRatio ρ ≤ 2) :
    ∃ A : Subgroup H, A ≤ S ∧ A ∈ QhatStar ρ := by
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr hq
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  obtain ⟨P,hP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H P S
  refine ⟨A.map (MulAut.conj g).toMonoidHom,?_,QhatStar.map_conj ρ hA g⟩
  rintro _ ⟨a,ha,rfl⟩
  rw [←hg]
  change (MulAut.conj g) • a ∈ (MulAut.conj g) • (P : Set H)
  exact Set.smul_mem_smul_set (hP ha)

/-- A nontrivial section kernel excludes the faithful-span alternative of
D.2.7, forcing the strict inequality needed in D.3.19. -/
theorem starred_restriction_strict_of_kernel
    {A : Subgroup H} (hA : A ∈ QhatStar ρ)
    (W : Submodule (ZMod 2) E) (hW : A ≤ subspaceStabilizer ρ W)
    (hn : ¬ W ≤ fixedSpace ρ A) (hk : subspaceKernel ρ W A ≠ ⊥) :
    restrictedSubgroup ρ W A ∈ Qhat (subspaceImageRepresentation ρ W) ∧
    actionRatio (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) < 2 := by
  rcases (QhatStar.restriction_alternatives ρ hA W hW hn).2.2 with hs | hs
  · exact ⟨hs.1,hs.2.trans_le hA.1.1⟩
  · exact (hk hs.1).elim

variable {G : Type*} [Group G]

/-- A literal ambient subgroup, viewed as a binary subspace of U. -/
abbrev internalSection (U W : Subgroup G) [IsElementaryAbelian 2 U] :
    Submodule (ZMod 2) (Additive U) :=
  AddSubgroup.toZModSubmodule 2 (W.subgroupOf U).toAddSubgroup

/-- The original conjugation map onto its faithful image on U. -/
abbrev internalHom (M U : Subgroup G) (hn : M ≤ normalizer (U : Set G)) :
    M →* internalActionImage M U hn :=
  (UniqueFactor.actionHom M U hn).rangeRestrict

/-- Ambient normalization descends to the faithful action on the internal section. -/
theorem internalSection_stable (M U W R : Subgroup G)
    [IsElementaryAbelian 2 U] (hn : M ≤ normalizer (U : Set G))
    (hR : R ≤ normalizer (W : Set G)) :
    (R.subgroupOf M).map (internalHom M U hn) ≤
      subspaceStabilizer (UniqueFactor.imageRepresentation M U hn) (internalSection U W) := by
  apply le_subspaceStabilizer
  rintro _ ⟨r,hr,rfl⟩ v hv
  change r.val * v.toMul.val * r.val⁻¹ ∈ W
  exact (mem_normalizer_iff.mp (hR hr) _).mp hv

/-- The section kernel is the image of the actor preimage intersected with
its original centralizer of W inside M. -/
theorem internalSection_kernel (M U W : Subgroup G)
    [IsElementaryAbelian 2 U] (hn : M ≤ normalizer (U : Set G)) (hWU : W ≤ U)
    (A : Subgroup (internalActionImage M U hn)) :
    subspaceKernel (UniqueFactor.imageRepresentation M U hn) (internalSection U W) A =
      (A.comap (internalHom M U hn) ⊓ (centralizer (W : Set G)).subgroupOf M).map
        (internalHom M U hn) := by
  ext a
  constructor
  · rintro ⟨ha,hfix⟩
    obtain ⟨m,hm⟩ := (UniqueFactor.actionHom M U hn).rangeRestrict_surjective a
    change internalHom M U hn m = a at hm
    refine ⟨m,⟨?_,?_⟩,hm⟩
    · change internalHom M U hn m ∈ A
      rw [hm]
      exact ha
    · intro w hw
      have he := congrArg (fun v : Additive U => v.toMul.val)
        (hfix (Additive.ofMul ⟨w,hWU hw⟩) hw)
      rw [←hm] at he
      change m.val * w * m.val⁻¹ = w at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · rintro ⟨m,⟨hm,hc⟩,rfl⟩
    refine ⟨hm,?_⟩
    intro v hv
    apply Additive.toMul.injective
    apply Subtype.ext
    change m.val * v.toMul.val * m.val⁻¹ = v.toMul.val
    have he : v.toMul.val * m.val = m.val * v.toMul.val := hc v.toMul.val hv
    rw [←he,mul_inv_cancel_right]

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterD
variable {G : Type*} [Group G] [Finite G]

/-- The image of the original ambient Sylow subgroup under conjugation on U. -/
abbrev internalSylow (T : Sylow 2 G) (M U : Subgroup G)
    (hn : M ≤ normalizer (U : Set G)) (hTM : (T : Subgroup G) ≤ M) :
    Sylow 2 (internalActionImage M U hn) :=
  (T.subtype hTM).mapSurjective (UniqueFactor.actionHom M U hn).rangeRestrict_surjective

/-- The literal Sylow image preserves every section normalized by T. -/
theorem internalSylow_section_stable (T : Sylow 2 G) (M U W : Subgroup G)
    [IsElementaryAbelian 2 U] (hn : M ≤ normalizer (U : Set G))
    (hTM : (T : Subgroup G) ≤ M) (hTW : (T : Subgroup G) ≤ normalizer (W : Set G)) :
    (internalSylow T M U hn hTM : Subgroup (internalActionImage M U hn)) ≤
      subspaceStabilizer (UniqueFactor.imageRepresentation M U hn) (internalSection U W) :=
  internalSection_stable M U W T hn hTW

omit [Finite G] in
/-- Centralization of the internal section is equivalent to centralization
of W by the full preimage of the acting subgroup. -/
theorem internalSection_noncentral_iff (M U W : Subgroup G)
    [IsElementaryAbelian 2 U] (hn : M ≤ normalizer (U : Set G)) (hWU : W ≤ U)
    (A : Subgroup (internalActionImage M U hn)) :
    internalSection U W ≤ fixedSpace (UniqueFactor.imageRepresentation M U hn) A ↔
      A.comap (internalHom M U hn) ≤ (centralizer (W : Set G)).subgroupOf M := by
  constructor
  · intro hf m hm w hw
    have he := congrArg (fun v : Additive U => v.toMul.val)
      (hf (show Additive.ofMul (⟨w,hWU hw⟩ : U) ∈ internalSection U W from hw)
        ⟨internalHom M U hn m,hm⟩)
    change m.val * w * m.val⁻¹ = w at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hf v hv a
    obtain ⟨m,hm⟩ := (UniqueFactor.actionHom M U hn).rangeRestrict_surjective a.val
    change internalHom M U hn m = a.val at hm
    have hc := hf (show m ∈ A.comap (internalHom M U hn) by
      change internalHom M U hn m ∈ A
      rw [hm]
      exact a.property)
    change UniqueFactor.imageRepresentation M U hn a.val v = v
    rw [←hm]
    apply Additive.toMul.injective
    apply Subtype.ext
    change m.val * v.toMul.val * m.val⁻¹ = v.toMul.val
    have he : v.toMul.val * m.val = m.val * v.toMul.val := hc v.toMul.val hv
    rw [←he,mul_inv_cancel_right]

/-- The literal ambient subgroup and its internal binary subspace have the
same rank, even though the surrounding full module may be strictly larger. -/
theorem internalSection_finrank (U W : Subgroup G) [IsElementaryAbelian 2 U]
    (hWU : W ≤ U) : Module.finrank (ZMod 2) (internalSection U W) = rank W := by
  let e : internalSection U W ≃ W := {
    toFun w := ⟨w.val.toMul.val,w.property⟩
    invFun w := ⟨Additive.ofMul ⟨w.val,hWU w.property⟩,w.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := internalSection U W)
  rw [Nat.card_congr e,Nat.card_zmod] at hc
  rw [rank,hc,Nat.log_pow (by decide)]

/-- Fixed vectors in the actual section are precisely the original subgroup
centralizer of the actor preimage. No elementary lift through the action
quotient is asserted. -/
theorem internalSection_fixed_finrank (M U W : Subgroup G)
    [IsElementaryAbelian 2 U] (hn : M ≤ normalizer (U : Set G)) (hWU : W ≤ U)
    (A : Subgroup (internalActionImage M U hn)) :
    Module.finrank (ZMod 2) (internalSection U W ⊓
      fixedSpace (UniqueFactor.imageRepresentation M U hn) A : Submodule (ZMod 2) (Additive U)) =
      rank (W ⊓ centralizer (((A.comap (internalHom M U hn)).map M.subtype : Subgroup G) : Set G)) := by
  let J := internalSection U W ⊓ fixedSpace (UniqueFactor.imageRepresentation M U hn) A
  let C := W ⊓ centralizer (((A.comap (internalHom M U hn)).map M.subtype : Subgroup G) : Set G)
  let e : J ≃ C := {
    toFun w := ⟨w.val.toMul.val,w.property.1,by
      rintro m ⟨m,hm,rfl⟩
      have he := congrArg (fun v : Additive U => v.toMul.val)
        (w.property.2 ⟨internalHom M U hn m,hm⟩)
      change m.val * w.val.toMul.val * m.val⁻¹ = w.val.toMul.val at he
      exact mul_inv_eq_iff_eq_mul.mp he⟩
    invFun w := ⟨Additive.ofMul ⟨w.val,hWU w.property.1⟩,w.property.1,by
      intro a
      obtain ⟨m,hm⟩ := (UniqueFactor.actionHom M U hn).rangeRestrict_surjective a.val
      change internalHom M U hn m = a.val at hm
      have hmem : m ∈ A.comap (internalHom M U hn) := by
        change internalHom M U hn m ∈ A
        rw [hm]
        exact a.property
      have he : m.val * w.val = w.val * m.val := w.property.2 m.val ⟨m,hmem,rfl⟩
      change UniqueFactor.imageRepresentation M U hn a.val _ = _
      rw [←hm]
      apply Additive.toMul.injective
      apply Subtype.ext
      change m.val * w.val * m.val⁻¹ = w.val
      rw [he,mul_inv_cancel_right]⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := J)
  rw [Nat.card_congr e,Nat.card_zmod] at hc
  change Module.finrank (ZMod 2) J = rank C
  rw [rank,hc,Nat.log_pow (by decide)]

/-- The numerator of the restricted action ratio is the rank difference
for W and its literal centralizer of the full actor preimage. -/
theorem internalSection_fixedCodim (M U W : Subgroup G)
    [IsElementaryAbelian 2 U] (hn : M ≤ normalizer (U : Set G)) (hWU : W ≤ U)
    (A : Subgroup (internalActionImage M U hn))
    (hA : A ≤ subspaceStabilizer (UniqueFactor.imageRepresentation M U hn) (internalSection U W)) :
    fixedCodim (subspaceImageRepresentation (UniqueFactor.imageRepresentation M U hn) (internalSection U W))
      (restrictedSubgroup (UniqueFactor.imageRepresentation M U hn) (internalSection U W) A) =
      rank W - rank (W ⊓ centralizer
        (((A.comap (internalHom M U hn)).map M.subtype : Subgroup G) : Set G)) := by
  rw [fixedCodim_restrictedSubgroup _ _ A hA,internalSection_finrank U W hWU,
    internalSection_fixed_finrank M U W hn hWU A]

/-- The D.3.19 strict decrease on a Sylow-invariant internal section, retaining
both the movement premise and the nontrivial literal centralizer image. -/
theorem internal_starred_section_strict (T : Sylow 2 G) (M U W : Subgroup G)
    [IsElementaryAbelian 2 U] (hn : M ≤ normalizer (U : Set G))
    (hTM : (T : Subgroup G) ≤ M) (hTW : (T : Subgroup G) ≤ normalizer (W : Set G))
    (hWU : W ≤ U) {A : Subgroup (internalActionImage M U hn)}
    (hAS : A ≤ internalSylow T M U hn hTM)
    (hA : A ∈ QhatStar (UniqueFactor.imageRepresentation M U hn))
    (hmove : ¬ A.comap (internalHom M U hn) ≤ (centralizer (W : Set G)).subgroupOf M)
    (hkernel : (A.comap (internalHom M U hn) ⊓
      (centralizer (W : Set G)).subgroupOf M).map (internalHom M U hn) ≠ ⊥) :
    actionRatio (subspaceImageRepresentation (UniqueFactor.imageRepresentation M U hn)
      (internalSection U W))
      (restrictedSubgroup (UniqueFactor.imageRepresentation M U hn) (internalSection U W) A) < 2 := by
  exact (starred_restriction_strict_of_kernel _ hA _
    (hAS.trans (internalSylow_section_stable T M U W hn hTM hTW))
    (fun hf => hmove ((internalSection_noncentral_iff M U W hn hWU A).mp hf))
    (by rwa [internalSection_kernel M U W hn hWU])).2

/-- D.2.7 on the original internal section. The faithful alternative includes
its full fixed-space supplement; the strict alternative keeps the actual image. -/
theorem internal_starred_section_alternatives (T : Sylow 2 G) (M U W : Subgroup G)
    [IsElementaryAbelian 2 U] (hn : M ≤ normalizer (U : Set G))
    (hTM : (T : Subgroup G) ≤ M) (hTW : (T : Subgroup G) ≤ normalizer (W : Set G))
    (hWU : W ≤ U) {A : Subgroup (internalActionImage M U hn)}
    (hAS : A ≤ internalSylow T M U hn hTM)
    (hA : A ∈ QhatStar (UniqueFactor.imageRepresentation M U hn)) :
    A.comap (internalHom M U hn) ≤ (centralizer (W : Set G)).subgroupOf M ∨
    actionRatio (subspaceImageRepresentation (UniqueFactor.imageRepresentation M U hn)
      (internalSection U W))
      (restrictedSubgroup (UniqueFactor.imageRepresentation M U hn) (internalSection U W) A) < 2 ∨
    ((A.comap (internalHom M U hn) ⊓ (centralizer (W : Set G)).subgroupOf M).map
      (internalHom M U hn) = ⊥ ∧
      internalSection U W ⊔ fixedSpace (UniqueFactor.imageRepresentation M U hn) A = ⊤) := by
  by_cases hc : A.comap (internalHom M U hn) ≤ (centralizer (W : Set G)).subgroupOf M
  · exact Or.inl hc
  · have hmove : ¬ internalSection U W ≤ fixedSpace (UniqueFactor.imageRepresentation M U hn) A :=
      fun hf => hc ((internalSection_noncentral_iff M U W hn hWU A).mp hf)
    rcases (QhatStar.restriction_alternatives _ hA _
      (hAS.trans (internalSylow_section_stable T M U W hn hTM hTW)) hmove).2.2 with hh | hh
    · exact Or.inr (Or.inl (hh.2.trans_le hA.1.1))
    · exact Or.inr (Or.inr ⟨(internalSection_kernel M U W hn hWU A).symm.trans hh.1,hh.2⟩)

/-- The same actor's kernel and section displacement fit inside its original
cubic budget. The kernel here is the literal centralizer image, not an
independently chosen elementary actor. -/
theorem internal_starred_section_budget (T : Sylow 2 G) (M U W : Subgroup G)
    [IsElementaryAbelian 2 U] (hn : M ≤ normalizer (U : Set G))
    (hTM : (T : Subgroup G) ≤ M) (hTW : (T : Subgroup G) ≤ normalizer (W : Set G))
    (hWU : W ≤ U) {A : Subgroup (internalActionImage M U hn)}
    (hAS : A ≤ internalSylow T M U hn hTM)
    (hA : A ∈ QhatStar (UniqueFactor.imageRepresentation M U hn)) :
    let ρ := UniqueFactor.imageRepresentation M U hn
    let C := (A.comap (internalHom M U hn) ⊓ (centralizer (W : Set G)).subgroupOf M).map
      (internalHom M U hn)
    rank C + rank (restrictedSubgroup ρ (internalSection U W) A) = rank A ∧
    fixedCodim ρ C + fixedCodim (subspaceImageRepresentation ρ (internalSection U W))
      (restrictedSubgroup ρ (internalSection U W) A) ≤ 2 * rank A := by
  let ρ := UniqueFactor.imageRepresentation M U hn
  have hs := hAS.trans (internalSylow_section_stable T M U W hn hTM hTW)
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hr := rank_subspaceKernel_add_image ρ (internalSection U W) A hs
    (IsElementaryAbelian.isPGroup 2 A)
  have hb := (fixedCodim_kernel_add_restricted_le ρ (internalSection U W) A hs).trans
    ((actionRatio_le_nat_iff ρ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hA.1.1))
  rw [internalSection_kernel M U W hn hWU A] at hr hb
  exact ⟨hr,hb⟩

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
