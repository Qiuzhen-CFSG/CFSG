module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Marked
public import Theory.GroupAction.SylowFixedElementaryDisplacement
public import Theory.SpecificGroups.SL2.NaturalStabilizer

/-!
# Centralizers of noncentral Sylow-center involutions in a natural L₂(8) block

Let z belong to Ω₁(Z(S)) in a short natural block D. Faithfulness of the
actual natural module puts z in O₂(D), hence in Z(O₂(D)). Its odd conjugacy
orbit has a central product b congruent to z modulo U(D). Thus z/b belongs
to U(D) and has the same centralizer as z. If z is noncentral, z/b has nonzero
image in the actual natural module U(D)/C_U(D)(D).

The centralizer therefore maps into a nonzero-vector stabilizer in SL₂(8),
a two-group. The kernel of that map is O₂(D), so the centralizer is itself
a two-group. This argument retains all central extensions permitted by
shortness and uses the specified equivariant model throughout.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), definitions
C.1.7 and C.1.12, printed pp.123–124, and the block model inspection in E.6.25,
printed p.256 (PDF p.267). The proof follows the field-four calculation in
`Hyperplanes.Enlargement.BlockInspection.BlockCase.NaturalCentralizers`;
the odd-orbit argument also appears in `L2Torus.Center.GlobalFixed`.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative commutatorElement

namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels
open L2Torus
universe u
variable {D F : Type*} [Group D] [Finite D] [Field F]
  {B : Subgroup D} (a : MarkedBlockModel D B F)

include a in
private theorem exists_central_factor (hshort : ChapterC.IsShort D)
    (S : Sylow 2 D) (z : D)
    (hz : z ∈ Stellmacher.omegaOneCenterAmbient (S : Subgroup D)) :
    ∃ b ∈ center D, z / b ∈ ChapterC.blockU D := by
  have hzS := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz
  have hzcore := a.omegaOneCenter_le_core hshort S hz
  let A : Subgroup D := pCore 2 D ⊓ centralizer (pCore 2 D : Set D)
  let : IsMulCommutative A := ⟨⟨fun x y => Subtype.ext
    (mem_centralizer_iff.mp x.property.2 y y.property.1).symm⟩⟩
  have hzA : z ∈ A := ⟨hzcore, mem_centralizer_iff.mpr fun x hx =>
    hzS.2.2 x (pCore_isPGroup.le_sylow_of_normal S hx)⟩
  let ρ : D →* MulAut A := A.normalizerMonoidHom.comp
    ((inclusion (show (⊤ : Subgroup D) ≤ normalizer (A : Set D) by
      rw [normalizer_eq_top])).comp topEquiv.symm.toMonoidHom)
  let : MulDistribMulAction D A := MulDistribMulAction.compHom A ρ
  let v : A := ⟨z, hzA⟩
  let f := QuotientGroup.mk' ((ChapterC.blockU D).subgroupOf A)
  have hf (l : D) : f (l • v) = f v := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (l * z * l⁻¹) / z ∈ ChapterC.blockU D
    have hc : ⁅l, z⁆ ∈ ChapterC.blockU D := by
      change ⁅l, z⁆ ∈ ⁅pCore 2 D, (⊤ : Subgroup D)⁆
      rw [commutator_comm]
      exact commutator_mem_commutator (mem_top l) hzcore
    simpa only [div_eq_mul_inv, commutatorElement_def] using hc
  obtain ⟨b, hb, he⟩ := Theory.GroupAction.exists_fixed_lift_of_sylow_fixed S v
    (Subtype.ext hzS.2.1) (fun s hs => Subtype.ext (by
      change s * z * s⁻¹ = z
      rw [hzS.2.2 s hs, mul_inv_cancel_right])) f hf
  refine ⟨b, mem_center_iff.mpr (fun l => ?_), ?_⟩
  · exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (hb l))
  · exact (QuotientGroup.eq_iff_div_mem
      (N := (ChapterC.blockU D).subgroupOf A)).mp he.symm

include a in
omit [Finite D] in
private theorem centralizer_block_element_isPGroup [CharP F 2]
    (u : ChapterC.blockU D) (hu : (u : D) ∉ center D) :
    IsPGroup 2 (centralizer ({(u : D)} : Set D)) := by
  let v := a.model.moduleIso (QuotientGroup.mk' (ChapterC.blockFixed D) u)
  have hv : Multiplicative.toAdd v ≠ 0 := by
    intro hv
    have hv1 : v = 1 := Multiplicative.toAdd.injective hv
    have he : QuotientGroup.mk' (ChapterC.blockFixed D) u = 1 :=
      (map_eq_one_iff _ a.model.moduleIso.injective).mp hv1
    exact hu ((QuotientGroup.eq_one_iff u).mp he)
  have hp := (Matrix.SL2.stabilizer_nonzero_isPGroup _ hv).comap_of_ker_isPGroup
    a.linearMap (by rw [a.linearMap_ker]; exact pCore_isPGroup)
  apply hp.to_le
  intro g hg
  change a.linearMap g • Multiplicative.toAdd v = Multiplicative.toAdd v
  have hc : ChapterC.blockConjugate D g u = u := by
    apply Subtype.ext
    change g * (u : D) * g⁻¹ = u
    rw [mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
  have he := a.model.intertwining g u
  rw [hc] at he
  exact (congrArg Multiplicative.toAdd he).symm

/-- In a natural L₂(8)-block, every noncentral Sylow omega-center element
has a two-group centralizer, including in the permitted central extensions. -/
theorem blockEightCentralizer_isPGroup {H : Type u} [Group H] [Finite H]
    (hH : ChapterC.IsL2EvenBlock H 3) (S : Sylow 2 H) (z : H)
    (hz : z ∈ Stellmacher.omegaOneCenterAmbient (S : Subgroup H))
    (hnz : z ∉ center H) : IsPGroup 2 (centralizer ({z} : Set H)) := by
  obtain ⟨_, hshort, F, _, _, hF, _, rho, ⟨model⟩, hlinear⟩ := hH
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hrho : rho = Matrix.SL2.naturalAction F := by
    ext g : 1
    ext v : 1
    exact Multiplicative.toAdd.injective (hlinear g v)
  subst rho
  let B := (Matrix.SpecialLinearGroup.rankOneBorel F).comap
    (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H)))
  let a : MarkedBlockModel H B F := ⟨model, rfl⟩
  obtain ⟨b, hb, hu⟩ := exists_central_factor a hshort S z hz
  have hnu : z / b ∉ center H := by
    intro hc
    exact hnz (by simpa only [div_mul_cancel] using (center H).mul_mem hc hb)
  apply (centralizer_block_element_isPGroup a ⟨z / b, hu⟩ hnu).to_le
  intro g hg
  apply mem_centralizer_singleton_iff.mpr
  change g * (z / b) = (z / b) * g
  rw [div_eq_mul_inv]
  exact (show Commute g z from mem_centralizer_singleton_iff.mp hg).mul_right
    (show Commute g b from mem_center_iff.mp hb g).inv_right

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels
