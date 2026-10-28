module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.DeletedSource
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.PointStabilizer
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis
public import Theory.GroupTheory.PrimeRankProduct

/-!
# The original tensor conjugate actor

The G.10 dimension bound forces the image of Wᵍ to have order at least
eight. The two-rank of S₃ × S₅ bounds it above by eight. The original
point-stabilizer normality then transports to the literal tensor action,
with the same central quotient, actor quotient and source conjugator.
No identification of U with O₂(H) is required.

Source: Aschbacher--Smith 14.4.2(5), 14.4.10, printed pp.1006,1010--1011.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative TensorProduct
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

namespace TensorGeometry
variable {F : InvariantFlag T V 3}

def linearCoordinates [IsElementaryAbelian 2 F.Uhat]
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) :
    Additive F.Uhat ≃ₗ[ZMod 2] (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] W) :=
  LinearEquiv.ofBijective (c.space.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) c.space.bijective

omit [Finite G] in
/-- Evaluation on the original central quotient. -/
theorem linearCoordinates_apply [IsElementaryAbelian 2 F.Uhat]
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) (w : Additive F.Uhat) :
    linearCoordinates c w = (c.space w.toMul).toAdd := by
  unfold linearCoordinates
  rfl

omit [Finite G] in
theorem coordinates_equivariant [IsElementaryAbelian 2 F.Uhat]
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) (a : F.H) (v : Additive F.Uhat) :
    linearCoordinates c
      (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) v) =
    sourceTensorAction c.constituent (c.actor (QuotientGroup.mk' (pCore 2 F.H) a))
      (linearCoordinates c v) := by
  obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective (center F.U) v.toMul
  have hv : v = Additive.ofMul (QuotientGroup.mk' (center F.U) w) :=
    (congrArg Additive.ofMul hw).symm
  rw [hv]
  change (c.space (F.uhatAction a (QuotientGroup.mk' (center F.U) w))).toAdd = _
  rw [F.uhatAction_apply_mk]
  exact congrArg Multiplicative.toAdd (c.equivariant a w)

omit [Finite G] in
/-- The linear coordinates send the literal quotient image to its tensor image. -/
theorem image_eq_map [IsElementaryAbelian 2 F.Uhat]
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) (A : Subgroup G) :
    c.image A = (hatSpace F A).map (linearCoordinates c).toLinearMap := by
  ext v
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩

end TensorGeometry

/-- The original tensor conjugate actor is elementary abelian of order eight.
The upper bound is the two-rank of S₃ × S₅, and G.10 supplies the lower bound. -/
theorem source_tensor_actor_card (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) :
    IsElementaryAbelian 2 (star F.H (F.X g)) ∧
      Nat.card (star F.H (F.X g)) = 8 := by
  obtain ⟨heU, hx, B, v, hyp⟩ :=
    source_terminal_hypothesis F d earlier hq chosen structural alternatives hne g hgP hgH
  let := heU
  let := hx
  let f : F.TerminalHdot ≃* coreQuotient F.H :=
    QuotientGroup.quotientMulEquivOfEq
      (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)
  have hm : (F.terminalDot (F.X g)).map f.toMonoidHom = star F.H (F.X g) := by
    rw [terminalDot, map_map]
    rfl
  have he : IsElementaryAbelian 2 (star F.H (F.X g)) := by
    rw [← hm]
    exact IsElementaryAbelian.map f.toMonoidHom
  let := he
  let e := TensorGeometry.linearCoordinates c
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 8 := by
    rw [e.finrank_eq, Module.finrank_tensorProduct, BinaryPermutation.finrank_core,
      Fintype.card_fin, c.constituent_model.finrank_four]
  have hr := (Group.rank_le_of_surjective
    (QuotientGroup.mk' ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (QuotientGroup.mk'_surjective _)).trans
    (IsElementaryAbelian.rank_le_finrank (p:=2) (F.terminalDot (F.X g)))
  have hb := hyp.dimension_bound.1
  rw [hd] at hb
  have hl : 3 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by omega
  have hpow : Nat.card (star F.H (F.X g)) =
      2 ^ finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
    rw [← hm, card_map_of_injective f.injective, Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive (F.terminalDot (F.X g)))
  have hD : primeRank 2 D ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 2 D.subtype D.subtype_injective).trans
      Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
  have hprod : primeRank 2 (Three × D) ≤ 3 := by
    rw [primeRank_prod_eq_add]
    have h3 := Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricThree_primeRank_le_one
    change primeRank 2 Three ≤ 1 at h3
    omega
  have hu := (primeRank_le_iff_elementary_card_le (Three × D)).mp hprod
    ((star F.H (F.X g)).map c.actor.toMonoidHom) (IsElementaryAbelian.map c.actor.toMonoidHom)
  rw [card_map_of_injective c.actor.injective] at hu
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hl
  exact ⟨he, le_antisymm hu (by simpa only [← hpow] using hp)⟩

/-- Relative normality holds in the whole tensor point centralizer, on the
original quotient maps and the original conjugator. -/
theorem source_tensor_actor_normal (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) :
    c.actorImage (F.X g) ≤ c.pointCentralizer (F.Vi 2) ∧
      ((c.actorImage (F.X g)).subgroupOf (c.pointCentralizer (F.Vi 2))).Normal := by
  obtain ⟨heU, hx, B, v, hyp, hline, hfix⟩ :=
    source_terminal_marked_hypothesis F d earlier hq chosen structural alternatives hne g hgP hgH
  let := heU
  let e := TensorGeometry.linearCoordinates c
  let f : F.TerminalHdot ≃* Three × D :=
    (QuotientGroup.quotientMulEquivOfEq
      (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).trans c.actor
  have hm (A : Subgroup G) : (F.terminalDot A).map f.toMonoidHom = c.actorImage A := by
    rw [terminalDot, map_map]
    change (A.subgroupOf F.H).map _ =
      ((A.subgroupOf F.H).map (QuotientGroup.mk' _)).map c.actor.toMonoidHom
    rw [map_map]
    rfl
  have ha (a : F.TerminalHdot) (w : Additive F.Uhat) :
      e (F.terminalRepresentation a w) = sourceTensorAction c.constituent (f a) (e w) := by
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact TensorGeometry.coordinates_equivariant c b w
  have hP : c.image (F.Vi 2) = Submodule.span (ZMod 2) {e v} := by
    rw [TensorGeometry.image_eq_map, ← hline, Submodule.map_span, Set.image_singleton]
    rfl
  have hpc : (ChapterG.Section10.pointCentralizer F.terminalRepresentation v).map
      f.toMonoidHom = c.pointCentralizer (F.Vi 2) := by
    ext b
    have hiff : b ∈ c.pointCentralizer (F.Vi 2) ↔
        sourceTensorAction c.constituent b (e v) = e v := by
      change (b ∈ (⊤ : Subgroup (Three × D)) ∧
        ∀ w ∈ c.image (F.Vi 2), sourceTensorAction c.constituent b w = w) ↔ _
      simp only [Subgroup.mem_top, true_and]
      rw [hP]
      constructor
      · intro hb
        exact hb _ (Submodule.mem_span_singleton_self _)
      · intro hb w hw
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [map_smul, hb]
    rw [hiff]
    constructor
    · rintro ⟨a, ha', rfl⟩
      exact (ha a v).symm.trans (congrArg e ha')
    · intro hb
      obtain ⟨a, rfl⟩ := f.surjective b
      exact ⟨a, e.injective ((ha a v).trans hb), rfl⟩
  obtain ⟨hRC, hRN⟩ := source_actor_normal_in_point_stabilizer d earlier hq chosen
    structural alternatives F hne hZ g hgP hgH v hyp.point_ne_zero hline
  have hle : c.actorImage (F.X g) ≤ c.pointCentralizer (F.Vi 2) := by
    rw [← hm, ← hpc]
    exact map_mono hRC
  refine ⟨hle, (normal_subgroupOf_iff_le_normalizer hle).mpr ?_⟩
  rw [← hpc, ← hm]
  exact (map_mono ((normal_subgroupOf_iff_le_normalizer hRC).mp hRN)).trans
    (le_normalizer_map f.toMonoidHom)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
