module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus
public import CFSG.Quasithin.ChapterI.Section02.ModuleCovers.LinearTwo.CoverLift

/-!
# The source rank-one torus and its fixed elements

The proved natural-cover theorem I.2.3 discharges the earlier-source premise
of the intrinsic torus construction. Regularity then identifies the fixed
part of the Sylow center with the global central part. This formulation
retains the actual torus and its regular action for E.6.7 and E.6.11.

Source: Aschbacher–Smith, E.6.7 and E.6.11, printed pp.246 and 249.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06
open Subgroup
variable {L : Type*} [Group L] [Finite L]

/-- The intrinsic block calculation, with I.2.3 discharged. -/
theorem exists_rankOneBlockTorus {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n)
    (S : Sylow 2 L) {B : Subgroup L} (hS : (S : Subgroup L) ≤ B)
    (hB : L2BlockBorel L B n) : Nonempty (RankOneBlockTorus L S B n) :=
  exists_rankOneBlockTorus_of_I23 hL S hS hB
    (fun F _ _ _ => ChapterI.ModuleCovers.LinearTwo.Application.rankOneCoverTheorem F n)

omit [Finite L] in
/-- No noncentral part of the Sylow center is fixed by the actual torus. -/
theorem RankOneBlockTorus.fixed_le_center {S : Sylow 2 L} {B : Subgroup L} {n : ℕ}
    (d : RankOneBlockTorus L S B n) (hn : 1 < n) :
    Stellmacher.omegaOneCenterAmbient (S : Subgroup L) ⊓ centralizer (d.torus : Set L) ≤
      center L := by
  let Z := Stellmacher.omegaOneCenterAmbient (S : Subgroup L)
  let C := Z ⊓ center L
  let D := ⁅Z, d.torus⁆
  have hX : 1 < Nat.card d.torus := by
    rw [d.order]
    have hp : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    omega
  have hXne : d.torus ≠ ⊥ := by
    intro he
    simp [he] at hX
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXne
  let : C.Normal := ⟨fun a ha b => by
    rw [mem_center_iff.mp ha.2 b, mul_inv_cancel_right]
    exact ha⟩
  rintro z ⟨hz, hzX⟩
  have hz' : z ∈ C ⊔ D := by
    change z ∈ (Z ⊓ center L) ⊔ ⁅Z, d.torus⁆
    rw [← d.center_decomposition]
    exact hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_normal_left.mp hz'
  have hbX : b ∈ centralizer (d.torus : Set L) := by
    have haX : a ∈ centralizer (d.torus : Set L) :=
      mem_centralizer_iff.mpr (fun y _ => mem_center_iff.mp ha.2 y)
    exact (mul_mem_cancel_left haX).mp hzX
  have hb1 : b = 1 := by
    by_contra hb1
    have hbD : (⟨b, hb⟩ : D) ≠ 1 := fun he => hb1 (congrArg Subtype.val he)
    obtain ⟨y, _, hy⟩ := d.regular.2 ⟨b, hb⟩ hbD ⟨b, hb⟩ hbD
    have hfix : (x : L) * b * (x : L)⁻¹ = b := by
      rw [mem_centralizer_iff.mp hbX x x.property, mul_inv_cancel_right]
    have hx1 := (hy x hfix).trans (hy 1 (by simp)).symm
    exact hx hx1
  rw [hb1, mul_one]
  exact ha.2

end CFSG.Quasithin.ChapterE.Section06
