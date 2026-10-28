module

public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.IntersectionBalance.Models
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Supports
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPlaneQuotient

/-!
# The literal natural seed quotient is irreducible

The original StarAction and whole-module coordinates identify subgroup
images with subspaces of the natural six-letter module. Conjugation
identifies their actual commutators with linear displacements. Thus a
fully moved complement to the kernel line fills the marked seed plane.
Symplectic duality makes every invariant subgroup between the seed and
U_H equal to one of these endpoints.

This retains the central kernel and the original quotient/action maps;
no ambient normality or chief-factor count is assumed. The application
in CaseOne.NaturalKernel constructs the complement and its movement.
Source: Aschbacher--Smith, Lemma 13.8.33, printed p.966, last paragraph.
-/

public section
open Subgroup BinaryPermutation Module Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33
open IntersectionBalance
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry Representation.BinaryOffender
variable {G : Type*} [Group G] {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
  (a : SolvableExclusion.Five.StarAction H U Z)
  (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
  (F : Additive (U ⧸ Z.subgroupOf U) ≃ₗ[ZMod 2] natural (Fin 6))
  (hF : ∀ g v, F (tildeRepresentation H U Z a g v) =
    naturalRepresentation (Fin 6) (e g) (F v))

private noncomputable def coordinate : Additive U →ₗ[ZMod 2] natural (Fin 6) :=
  F.toLinearMap.comp ((QuotientGroup.mk' (Z.subgroupOf U)).toAdditive.toZModLinearMap 2)

private noncomputable def image (D : Subgroup G) : Submodule (ZMod 2) (natural (Fin 6)) :=
  (quotientSpace U Z D).map F.toLinearMap

private theorem mem_image (D : Subgroup G) (v : natural (Fin 6)) :
    v ∈ image F D ↔ ∃ u : U, (u : G) ∈ D ∧ coordinate F (Additive.ofMul u) = v := by
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, ⟨u, hu, rfl⟩, rfl⟩

include hF in
private theorem coordinate_conjugation (x : H) (u : U) :
    coordinate F (Additive.ofMul (U.normalizerMonoidHom ⟨x, a.normalizes x.property⟩ u)) =
      naturalRepresentation (Fin 6) (e (QuotientGroup.mk' (pCore 2 H) x))
        (coordinate F (Additive.ofMul u)) := by
  have he := hF (QuotientGroup.mk' (pCore 2 H) x)
    (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u))
  change F (Additive.ofMul (a.action (QuotientGroup.mk' (pCore 2 H) x)
    (QuotientGroup.mk' (Z.subgroupOf U) u))) = _ at he
  rw [a.conjugation] at he
  exact he

private def actor (X : Subgroup G) (hX : X ≤ H) : X →* Equiv.Perm (Fin 6) :=
  e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 H)).comp (inclusion hX))

include a hF in
private theorem image_invariant (X D : Subgroup G) (hX : X ≤ H)
    (hn : X ≤ normalizer (D : Set G)) (x : X) :
    (image F D).map (naturalRepresentation (Fin 6) (actor e X hX x)) = image F D := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨u, hu, rfl⟩ := (mem_image F D v).mp hv
    dsimp only [actor, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← coordinate_conjugation a e F hF (inclusion hX x) u]
    apply (mem_image F D _).mpr
    exact ⟨_, (mem_normalizer_iff.mp (hn x.property) u).mp hu, rfl⟩
  · exact (LinearMap.GeneralLinearGroup.toLinearEquiv
      ((naturalRepresentation (Fin 6)).asGroupHom (actor e X hX x))).finrank_map_eq _

include a hF in
private theorem image_commutator (X W : Subgroup G) (hX : X ≤ H) (hW : W ≤ U) :
    image F ⁅W, X⁆ = subspaceCommutator (naturalRepresentation (Fin 6))
      (image F W) (actor e X hX).range := by
  let D := subspaceCommutator (naturalRepresentation (Fin 6)) (image F W) (actor e X hX).range
  let C : Subgroup G := ((D.comap (coordinate F)).toAddSubgroup.toSubgroup').map U.subtype
  have hcU : ⁅W, X⁆ ≤ U := (commutator_mono hW le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp (hX.trans a.normalizes))
  have hc : ⁅W, X⁆ ≤ C := by
    apply commutator_le.mpr
    intro w hw x hx
    let u : U := ⟨w, hW hw⟩
    let t : H := inclusion hX ⟨x, hx⟩
    have hm : naturalRepresentation (Fin 6) (actor e X hX ⟨x, hx⟩)
        (coordinate F (Additive.ofMul u)) - coordinate F (Additive.ofMul u) ∈ D :=
      Submodule.subset_span ⟨_, ⟨⟨x, hx⟩, rfl⟩, _,
        (mem_image F W _).mpr ⟨u, hw, rfl⟩, rfl⟩
    dsimp only [actor, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hm
    rw [← coordinate_conjugation a e F hF t u, ← map_sub] at hm
    have he : (⟨⁅w,x⁆,hcU (commutator_mem_commutator hw hx)⟩ : U) =
        (U.normalizerMonoidHom ⟨t,a.normalizes t.property⟩ u * u⁻¹)⁻¹ := by
      apply Subtype.ext
      simp only [commutatorElement_def, coe_inv, coe_mul]
      change w * x * w⁻¹ * x⁻¹ = (x * w * x⁻¹ * w⁻¹)⁻¹
      group
    refine ⟨⟨⁅w,x⁆,hcU (commutator_mem_commutator hw hx)⟩, ?_, rfl⟩
    change coordinate F (Additive.ofMul _) ∈ D
    rw [he]
    simpa only [ofMul_inv, ofMul_mul, ← sub_eq_add_neg, map_neg] using D.neg_mem hm
  apply le_antisymm
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := (mem_image F ⁅W,X⁆ v).mp hv
    obtain ⟨w, hw, he⟩ := hc hu
    have he' : w = u := Subtype.ext he
    exact he' ▸ hw
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨x, rfl⟩, v, hv, rfl⟩
    obtain ⟨u, hu, rfl⟩ := (mem_image F W v).mp hv
    dsimp only [actor, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← coordinate_conjugation a e F hF (inclusion hX x) u, ← map_sub]
    apply (mem_image F ⁅W,X⁆ _).mpr
    refine ⟨U.normalizerMonoidHom ⟨inclusion hX x,a.normalizes (hX x.property)⟩ u * u⁻¹, ?_, ?_⟩
    · change ⁅(x : G), (u : G)⁆ ∈ ⁅W,X⁆
      rw [commutator_comm]
      exact commutator_mem_commutator x.property hu
    · simp only [ofMul_mul, ofMul_inv, sub_eq_add_neg]

include a e hF in
/-- In the marked natural module, full movement of a seed complement makes
its quotient irreducible for the same literal actor. -/
theorem natural_seed_interval (X W P D : Subgroup G)
    (hX : X ≤ H) (hW : W ≤ U) (hP : P ≤ U) (hZ : Z ≤ P)
    (hWP : W ⊔ Z = P) (hm : ⁅W, X⁆ = W)
    (hmark : (quotientSpace U Z P).map F.toLinearMap = canonicalPlane)
    (hDP : P ≤ D) (hDU : D ≤ U) (hn : X ≤ normalizer (D : Set G)) :
    D = P ∨ D = U := by
  have him : image F W = canonicalPlane := by
    change (binarySpace (SolvableExclusion.tildeImage U Z W)).map F.toLinearMap = _
    rw [← SolvableExclusion.Five.tildeImage_sup_denominator W hW (hZ.trans hP)]
    exact hWP ▸ hmark
  have hmoved : subspaceCommutator (naturalRepresentation (Fin 6)) canonicalPlane
      (actor e X hX).range = canonicalPlane := by
    rw [← him, ← image_commutator a e F hF X W hX hW, hm]
  have hi (x : X) : canonicalPlane.map (naturalRepresentation (Fin 6) (actor e X hX x)) =
      canonicalPlane := by
    rw [← him]
    apply image_invariant a e F hF X W hX
    exact le_normalizer_iff_commutator_le_left.mpr hm.le
  have hPD : canonicalPlane ≤ image F D := by
    rw [← hmark]
    exact Submodule.map_mono (fun v hv => by
      obtain ⟨u,hu,rfl⟩ := hv
      exact ⟨u,hDP hu,rfl⟩)
  rcases NaturalPlaneQuotient.invariant_interval (actor e X hX) hi hmoved
    (image F D) hPD (image_invariant a e F hF X D hX hn) with hd | hd
  · left
    apply le_antisymm ?_ hDP
    have he : quotientSpace U Z D ≤ quotientSpace U Z P := by
      apply (Submodule.map_le_map_iff_of_injective F.injective _ _).mp
      exact (hd.trans hmark.symm).le
    exact (le_sup_of_quotientSpace_le U Z D P hDU he).trans (sup_le le_rfl hZ)
  · right
    apply le_antisymm hDU
    have he : quotientSpace U Z U ≤ quotientSpace U Z D := by
      apply (Submodule.map_le_map_iff_of_injective F.injective _ _).mp
      rw [show (quotientSpace U Z D).map F.toLinearMap = ⊤ from hd]
      exact le_top
    exact (le_sup_of_quotientSpace_le U Z U D le_rfl he).trans (sup_le le_rfl (hZ.trans hDP))

include a e hF in
/-- Centralizing the seed complement puts the same star image in the
literal pointwise fixer of the canonical plane. -/
theorem natural_seed_fixer (B W P : Subgroup G)
    (hW : W ≤ U) (hZ : Z ≤ U) (hWP : W ⊔ Z = P)
    (hmark : (quotientSpace U Z P).map F.toLinearMap = canonicalPlane)
    (hc : B ≤ centralizer (W : Set G)) :
    (Source.starImage H B).map e.toMonoidHom ≤ Theory.SpecificGroups.SymmetricSix.BinaryFlags.D := by
  have him : image F W = canonicalPlane := by
    change (binarySpace (SolvableExclusion.tildeImage U Z W)).map F.toLinearMap = _
    rw [← SolvableExclusion.Five.tildeImage_sup_denominator W hW hZ]
    exact hWP ▸ hmark
  rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
  apply (Representation.SixLetterRadicalDisplacement.natural_plane_fixer _).mp
  intro v hv
  obtain ⟨u, hu, rfl⟩ := (mem_image F W v).mp (him.symm ▸ hv)
  change naturalRepresentation (Fin 6) (e (QuotientGroup.mk' (pCore 2 H) b))
    (coordinate F (Additive.ofMul u)) = _
  rw [← coordinate_conjugation a e F hF b u]
  congr 2
  apply Subtype.ext
  change (b : G) * (u : G) * (b : G)⁻¹ = u
  have hcomm : (u : G) * (b : G) = (b : G) * (u : G) := hc hb u hu
  rw [← hcomm, mul_inv_cancel_right]

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33
