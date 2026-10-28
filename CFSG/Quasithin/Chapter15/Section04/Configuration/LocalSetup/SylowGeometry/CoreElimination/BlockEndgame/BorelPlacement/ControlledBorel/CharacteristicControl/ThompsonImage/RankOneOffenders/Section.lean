module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.CharacteristicControl.ThompsonImage.Offenders
public import Theory.GroupTheory.PCoreRestriction
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Mathlib.Algebra.Algebra.ZMod

/-!
# The first block image and its prospective natural section

The actual conjugation image of K₁ is normal in the faithful action group.
Its kernel is O₂(K₁) under the supplied kernel equality for D = K₁R, so
its quotient is identified with the concrete SL₂ model of the block.
Irreducibility and commutator idempotence also put U(K₁) inside Ω₁(Z(O₂(D))).

`NaturalSection` records an invariant section of that omega-center action,
an equivariant natural-module identification, and faithfulness on the section.
Its existence remains to be proved. Once constructed, fixed-codimension
monotonicity transfers the maximum elementary offenders to the natural module.
This does not assert the rank-one offender classification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7–13,
printed pp.123–125; B.2.10, p.77; B.4.2(1), p.86; C.2.7, pp.145–146,
as used in the proof of 15.4.20, p.1164.
-/

@[expose] public section

open Subgroup Stellmacher
open Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.ThompsonImage
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}
variable {c : ContraryData κ d i j} (b : ExchangedBlock c)
noncomputable section

/-- The first block is normal in the faithful action group. -/
instance faithfulImage_first_normal : (faithfulImage b b.first).Normal := by
  have hN : (b.first.subgroupOf (localGroup b)).Normal :=
    normal_subgroupOf_of_le_normalizer (localGroup_normalizes_first b)
  exact hN.map (actionProjection b) (actionProjection_surjective b)

/-- The local two-core restricts to the intrinsic two-core of the first block. -/
theorem first_inf_core : b.first ⊓ blockRadicalCore b = b.first.pCoreIn 2 :=
  le_antisymm (inf_pCoreIn_le_of_le 2 (show b.first ≤ localGroup b from le_sup_left))
    (le_inf (pCoreIn_le 2 b.first) (first_core_le_core b))

/-- Conjugation of the first block with codomain restricted to its actual image. -/
def firstProjection : b.first →* faithfulImage b b.first where
  toFun x := ⟨actionProjection b ⟨x, (show b.first ≤ localGroup b from le_sup_left) x.property⟩,
    ⟨⟨x, (show b.first ≤ localGroup b from le_sup_left) x.property⟩, x.property, rfl⟩⟩
  map_one' := Subtype.ext ((actionProjection b).map_one)
  map_mul' x y := Subtype.ext ((actionProjection b).map_mul
    ⟨x, (show b.first ≤ localGroup b from le_sup_left) x.property⟩ ⟨y, (show b.first ≤ localGroup b from le_sup_left) y.property⟩)

theorem firstProjection_surjective : Function.Surjective (firstProjection b) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The supplied kernel equality restricts to the genuine intrinsic quotient. -/
theorem firstProjection_ker
    (hker : (action b).ker = (blockRadicalCore b).subgroupOf (localGroup b)) :
    (firstProjection b).ker = pCore 2 b.first := by
  ext x
  have hmem : x ∈ (firstProjection b).ker ↔
      (⟨(x : G), (show b.first ≤ localGroup b from le_sup_left) x.property⟩ : localGroup b) ∈ (action b).ker := by
    change firstProjection b x = 1 ↔ action b ⟨(x : G), (show b.first ≤ localGroup b from le_sup_left) x.property⟩ = 1
    constructor
    · intro h
      exact congrArg (fun z : faithfulImage b b.first =>
        ((z : ActionGroup b) : MulAut (omegaModule b))) h
    · intro h
      apply Subtype.ext
      exact Subtype.ext h
  rw [hmem, hker]
  change (x : G) ∈ blockRadicalCore b ↔ x ∈ pCore 2 b.first
  constructor
  · intro hx
    have h := (first_inf_core b).le ⟨x.property, hx⟩
    obtain ⟨y, hy, he⟩ := h
    have he' : y = x := Subtype.ext he
    exact he' ▸ hy
  · intro hx
    exact first_core_le_core b (mem_map_of_mem b.first.subtype hx)

/-- First isomorphism theorem for the faithful image of the first block. -/
def firstQuotientEquiv
    (hker : (action b).ker = (blockRadicalCore b).subgroupOf (localGroup b)) :
    (b.first ⧸ pCore 2 b.first) ≃* faithfulImage b b.first :=
  (QuotientGroup.quotientMulEquivOfEq (firstProjection_ker b hker).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (firstProjection_surjective b))

/-- The quotient isomorphism sends a coset to the same conjugation image. -/
theorem firstQuotientEquiv_mk
    (hker : (action b).ker = (blockRadicalCore b).subgroupOf (localGroup b))
    (x : b.first) :
    firstQuotientEquiv b hker (QuotientGroup.mk' (pCore 2 b.first) x) =
      firstProjection b x := rfl

/-- The concrete matrix group in the block model is also the first action image. -/
theorem exists_firstImage_SL2
    (hker : (action b).ker = (blockRadicalCore b).subgroupOf (localGroup b)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 2 ^ b.n ∧
      Nonempty (faithfulImage b b.first ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨_, _, F, hF, hfin, hcard, _, hmodel⟩ := b.model
  exact ⟨F, hF, hfin, hcard,
    ⟨(firstQuotientEquiv b hker).symm.trans hmodel.quotient_iso.some⟩⟩

/-- Coprime commutator idempotence makes the intrinsic block layer perfect
under the first block's action. -/
theorem blockU_commutator_top :
    ⁅ChapterC.blockU b.first, (⊤ : Subgroup b.first)⁆ = ChapterC.blockU b.first := by
  apply Subgroup.map_injective b.first.subtype_injective
  rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  change ⁅FieldFourCentrality.firstLayer b, b.first⁆ = FieldFourCentrality.firstLayer b
  have h := commutator_isPPerfect_idempotent b.first (blockRadicalCore b)
    b.model.2.1.twoPerfect (isPGroup_pCoreIn 2 (localGroup b))
    (first_normalizes_blockRadicalCore c b)
  rwa [core_commutator_first] at h

/-- The natural block layer lies in the omega center. This follows from
irreducibility and the supplied faithful quotient, without cohomology or a
restriction on the field size. -/
theorem firstLayer_le_omegaModule_of_kernel
    (hker : (action b).ker = (blockRadicalCore b).subgroupOf (localGroup b)) :
    FieldFourCentrality.firstLayer b ≤ omegaModule b := by
  let W : Subgroup b.first := (omegaModule b).subgroupOf b.first
  have hKV : b.first ≤ normalizer (omegaModule b : Set G) :=
    (show b.first ≤ localGroup b from le_sup_left).trans (localGroup_normalizes_module b)
  let _ : W.Normal := normal_subgroupOf_of_le_normalizer hKV
  let N : Subgroup b.first := ChapterC.blockU b.first ⊓ (W ⊔ center b.first)
  have hNnormal : N.Normal := inferInstance
  have hC : ChapterC.blockU b.first ⊓ center b.first ≤ N :=
    inf_le_inf_left _ le_sup_right
  have hNle : N ≤ ChapterC.blockU b.first := inf_le_left
  rcases b.model.2.1.irreducible.2 N hNnormal hC hNle with hN | hN
  · have hcommU : ⁅omegaModule b, b.first⁆ ≤ FieldFourCentrality.firstLayer b := by
      rw [← core_commutator_first]
      exact commutator_mono (omegaModule_le_core b) le_rfl
    have hcommV : ⁅omegaModule b, b.first⁆ ≤ omegaModule b :=
      le_normalizer_iff_commutator_le_left.mp hKV
    have hcommC : ⁅omegaModule b, b.first⁆ ≤ (center b.first).map b.first.subtype := by
      intro x hx
      obtain ⟨u, hu, he⟩ := hcommU hx
      refine ⟨u, ?_, he⟩
      have hw : u ∈ W := by change b.first.subtype u ∈ omegaModule b; rw [he]; exact hcommV hx
      have hn : u ∈ N := ⟨hu, (show W ≤ W ⊔ center b.first from le_sup_left) hw⟩
      rw [hN] at hn
      exact hn.2
    have hCC : ⁅(center b.first).map b.first.subtype, b.first⁆ = ⊥ := by
      have h := congrArg (Subgroup.map b.first.subtype)
        (commutator_top_right_eq_bot_iff_le_center.mpr
          (le_rfl : center b.first ≤ center b.first))
      simpa only [map_commutator, ← MonoidHom.range_eq_map, range_subtype, Subgroup.map_bot] using h
    have hsecond : ⁅⁅omegaModule b, b.first⁆, b.first⁆ = ⊥ :=
      bot_unique ((commutator_mono hcommC le_rfl).trans hCC.le)
    have hVV : IsPGroup 2 (omegaModule b) :=
      (isPGroup_pCoreIn 2 (localGroup b)).to_le (omegaModule_le_core b)
    rw [commutator_isPPerfect_idempotent b.first (omegaModule b)
      b.model.2.1.twoPerfect hVV hKV] at hsecond
    have hKQ : b.first ≤ blockRadicalCore b := by
      intro x hx
      have hk : (⟨x, (show b.first ≤ localGroup b from le_sup_left) hx⟩ : localGroup b)
          ∈ (action b).ker := by
        rw [action_ker]
        exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hsecond) hx
      rwa [hker] at hk
    have hp : IsPGroup 2 b.first := (isPGroup_pCoreIn 2 (localGroup b)).to_le hKQ
    have ht := b.model.2.1.twoPerfect.hom_eq_one_of_isPGroup hp (MonoidHom.id b.first)
    exact False.elim (b.model.2.1.blockU_ne_bot (bot_unique (fun x _ =>
      show x ∈ (⊥ : Subgroup b.first) from DFunLike.congr_fun ht x)))
  · have hU : ChapterC.blockU b.first ≤ W ⊔ center b.first := hN ▸ inf_le_right
    let q := QuotientGroup.mk' W
    have hcenter : (ChapterC.blockU b.first).map q ≤ center (b.first ⧸ W) := by
      apply (map_mono hU).trans
      rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff W).mpr
        (by change W ≤ (QuotientGroup.mk' W).ker; rw [QuotientGroup.ker_mk']), bot_sup_eq]
      rintro y ⟨z, hz, rfl⟩
      apply mem_center_iff.mpr
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective W y
      exact (map_mul q x z).symm.trans
        ((congrArg q (mem_center_iff.mp hz x)).trans (map_mul q z x))
    have hbot : (ChapterC.blockU b.first).map q = ⊥ := by
      rw [← blockU_commutator_top b, map_commutator,
        map_top_of_surjective q (QuotientGroup.mk'_surjective W)]
      exact commutator_top_right_eq_bot_iff_le_center.mpr hcenter
    have hUW : ChapterC.blockU b.first ≤ W := by
      have h := (Subgroup.map_eq_bot_iff _).mp hbot
      rwa [QuotientGroup.ker_mk'] at h
    rintro x ⟨u, hu, rfl⟩
    exact hUW hu

/-- A literal invariant section of the omega-center representation, identified
with the natural module. Constructing this witness is a separate proof obligation. -/
structure NaturalSection (F : Type) [Field F] [Algebra (ZMod 2) F] where
  lower : Subrepresentation (representation b)
  upper : Subrepresentation (representation b)
  lower_le_upper : lower ≤ upper
  moduleIso : (upper.toSubmodule ⧸
      (sectionLower (representation b) lower upper).toSubmodule) ≃ₗ[ZMod 2] (Fin 2 → F)
  faithful : Function.Injective (sectionRepresentation (representation b) lower upper)
  firstIso : faithfulImage b b.first ≃* Matrix.SpecialLinearGroup (Fin 2) F
  intertwining : ∀ (g : faithfulImage b b.first) v,
    moduleIso (sectionRepresentation (representation b) lower upper g v) =
      Matrix.mulVec (firstIso g).val (moduleIso v)

namespace NaturalSection
variable {b} {F : Type} [Field F] [Algebra (ZMod 2) F] (s : NaturalSection b F)

/-- The whole faithful action group acts on the concrete binary natural module. -/
def naturalAction : Representation (ZMod 2) (ActionGroup b) (Fin 2 → F) :=
  s.moduleIso.conjRingEquiv.toMonoidHom.comp
    (sectionRepresentation (representation b) s.lower s.upper)

theorem naturalAction_apply (g : ActionGroup b) (v : Fin 2 → F) :
    s.naturalAction g v =
      s.moduleIso (sectionRepresentation (representation b) s.lower s.upper g
        (s.moduleIso.symm v)) := rfl

theorem naturalAction_injective : Function.Injective s.naturalAction :=
  s.moduleIso.conjRingEquiv.injective.comp s.faithful

/-- The first block's action is the specified natural matrix action. -/
theorem naturalAction_first (g : faithfulImage b b.first) (v : Fin 2 → F) :
    s.naturalAction g v = Matrix.mulVec (s.firstIso g).val v := by
  rw [naturalAction_apply, s.intertwining, s.moduleIso.apply_symm_apply]

/-- Fixed codimension cannot increase on this actual invariant section. -/
theorem fixedCodim_le [Finite F] (A : Subgroup (ActionGroup b)) :
    fixedCodim s.naturalAction A ≤ fixedCodim (representation b) A := by
  have he := fixedCodim_map_equivariant
    (sectionRepresentation (representation b) s.lower s.upper) s.naturalAction
    (MonoidHom.id (ActionGroup b)) s.moduleIso
    (fun g v => by simp only [naturalAction_apply, MonoidHom.id_apply,
      s.moduleIso.symm_apply_apply]) A
  rw [Subgroup.map_id] at he
  rw [← he]
  exact fixedCodim_section_le (representation b) s.lower s.upper A

/-- Each nontrivial maximum elementary image remains an offender on the
natural section, with no offender classification assumed. -/
theorem maximum_isOffender [Finite F] (hQ : blockRadicalCore b ≤ contraryCore c)
    {A : Subgroup G} (hA : A ∈ elementaryAbelianMaxSubgroups (contraryCore c))
    (hne : image b A ≠ ⊥) : IsOffender s.naturalAction (faithfulImage b A) := by
  have h := ThompsonImage.maximum_isOffender b hQ hA hne
  exact ⟨h.1, (s.fixedCodim_le (faithfulImage b A)).trans h.2⟩

end NaturalSection

end
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.ThompsonImage
