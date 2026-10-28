module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Center.Fixed
public import Theory.GroupAction.SylowFixedElementaryDisplacement

/-!
# Global centrality of the Borel-fixed Sylow center

For a marked natural L₂-block, a Borel-fixed element z of Ω₁(Z(S)) lies
in O₂(L) and centralizes it, since O₂(L) lies in S. Thus z belongs to the
abelian normal subgroup Z(O₂(L)). Its conjugates are equal modulo U(L),
and its conjugacy orbit has odd size because S fixes z. Multiplying that
orbit gives a globally central element b congruent to z modulo U(L).

The difference z / b is Borel-fixed in U(L), hence torus-fixed and therefore
central by the natural-module calculation in `Center.Fixed`. Consequently
z is central. The equality between torus-fixed and Borel-fixed elements
then identifies the torus-fixed part of Ω₁(Z(S)) with its global central part.

Source: Aschbacher–Smith, the L₂-block calculation in the proof of E.6.7,
printed p.246, with the short-group and natural-module definitions C.1.7
and C.1.12, printed pp.123–124. This step needs no covering-module input.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.ChapterE.Section06.L2Torus

variable {L F : Type*} [Group L] [Finite L] [Field F] [Finite F]
    {B : Subgroup L} {a : MarkedBlockModel L B F}

/-- A Borel-fixed element of the Sylow omega-center is globally central. -/
theorem DiagonalSection.omegaCenter_borel_fixed_le_center (d : DiagonalSection a)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (hshort : ChapterC.IsShort L) (S : Sylow 2 L) :
    Stellmacher.omegaOneCenterAmbient (S : Subgroup L) ⊓ centralizer (B : Set L) ≤
      center L := by
  rintro z ⟨hz, hzB⟩
  have hzS := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz
  have hzcore := a.omegaOneCenter_le_core hshort S hz
  -- The ambient image of Z(O₂(L)) is abelian and normal in L.
  let A : Subgroup L := pCore 2 L ⊓ centralizer (pCore 2 L : Set L)
  let : IsMulCommutative A := ⟨⟨fun x y => Subtype.ext
    (mem_centralizer_iff.mp x.property.2 y y.property.1).symm⟩⟩
  have hzA : z ∈ A := ⟨hzcore, mem_centralizer_iff.mpr fun x hx =>
    hzS.2.2 x (pCore_isPGroup.le_sylow_of_normal S hx)⟩
  let ρ : L →* MulAut A := A.normalizerMonoidHom.comp
    ((inclusion (show (⊤ : Subgroup L) ≤ normalizer (A : Set L) by
      rw [normalizer_eq_top])).comp topEquiv.symm.toMonoidHom)
  let : MulDistribMulAction L A := MulDistribMulAction.compHom A ρ
  let v : A := ⟨z, hzA⟩
  let f := QuotientGroup.mk' ((ChapterC.blockU L).subgroupOf A)
  -- Conjugation fixes the image of z modulo U(L) ∩ A.
  have hf (l : L) : f (l • v) = f v := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (l * z * l⁻¹) / z ∈ ChapterC.blockU L
    have hc : ⁅l, z⁆ ∈ ChapterC.blockU L := by
      change ⁅l, z⁆ ∈ ⁅pCore 2 L, (⊤ : Subgroup L)⁆
      rw [commutator_comm]
      exact commutator_mem_commutator (mem_top l) hzcore
    simpa only [div_eq_mul_inv, commutatorElement_def] using hc
  -- The odd orbit product gives an actual fixed lift of that image.
  obtain ⟨b, hb, he⟩ := Theory.GroupAction.exists_fixed_lift_of_sylow_fixed S v
    (Subtype.ext hzS.2.1) (fun s hs => Subtype.ext (by
      change s * z * s⁻¹ = z
      rw [hzS.2.2 s hs, mul_inv_cancel_right])) f hf
  have hbC : (b : L) ∈ center L := by
    apply mem_center_iff.mpr
    intro l
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (hb l))
  have huU : z / (b : L) ∈ ChapterC.blockU L :=
    (QuotientGroup.eq_iff_div_mem (N := (ChapterC.blockU L).subgroupOf A)).mp he.symm
  have huB : z / (b : L) ∈ centralizer (B : Set L) :=
    (centralizer (B : Set L)).div_mem hzB (center_le_centralizer _ hbC)
  have huC : z / (b : L) ∈ center L :=
    ((d.blockU_fixed_eq_center hn hF).le
      ⟨huU, centralizer_le d.torus_le_borel huB⟩).2
  simpa only [div_mul_cancel] using (center L).mul_mem huC hbC

/-- The torus-fixed part of the Sylow omega-center is its global central part. -/
theorem DiagonalSection.omegaCenter_fixed_eq_center [CharP F 2] (d : DiagonalSection a)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (hshort : ChapterC.IsShort L) (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B) :
    Stellmacher.omegaOneCenterAmbient (S : Subgroup L) ⊓ centralizer (d.torus : Set L) =
      Stellmacher.omegaOneCenterAmbient (S : Subgroup L) ⊓ center L := by
  rw [d.omegaCenter_fixed_eq_borel_fixed S hS]
  exact le_antisymm (le_inf inf_le_left (d.omegaCenter_borel_fixed_le_center hn hF hshort S))
    (inf_le_inf_left _ (center_le_centralizer _))

end CFSG.Quasithin.ChapterE.Section06.L2Torus
