module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionFixedLine

/-!
# Fusion through Sylow-central representatives

If every vector outside the fixed line is conjugate under M to a vector
centralized by the original Sylow T, two globally conjugate representatives
have T as a common centralizer Sylow. Sylow conjugacy adjusts their transporter
to N_G(T). The assumed containment N_G(T) ≤ M then gives M-fusion. The
already proved weak closure handles the fixed line.

This is the conjugator adjustment in Aschbacher–Smith 12.2.16, p.800.
The G₂ geometry constructing these representatives is supplied separately.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

theorem globalTI_of_sylow_central_representatives
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G)) {z : G}
    (hz : z ∈ V) (hz1 : z ≠ 1) (hzL : z ∈ centralizer (L : Set G))
    (hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z)
    (hcentral : ∀ x ∈ V, x ≠ 1 → x ≠ z →
      ∃ m ∈ normalizer (L : Set G),
        (T : Subgroup G) ≤ centralizer ({m * x * m⁻¹} : Set G)) : IsTISubgroup V := by
  apply globalTI_of_fusion h D structural hnone
  intro x y hx hy hx1 hy1 hxy
  have hc : IsConj x y := isConj_iff.mpr hxy
  by_cases hxz : x = z
  · subst x
    have hyz := fixed_line_weakly_closed h D structural hnone hz hz1 hzL hfixed hy hc
    exact ⟨1,one_mem _,by simp [hyz]⟩
  have hyz : y ≠ z := by
    intro he
    subst y
    exact hxz (fixed_line_weakly_closed h D structural hnone hz hz1 hzL hfixed hx hc.symm)
  obtain ⟨a,ha,hax⟩ := hcentral x hx hx1 hxz
  obtain ⟨b,hb,hby⟩ := hcentral y hy hy1 hyz
  let x' := a*x*a⁻¹
  let y' := b*y*b⁻¹
  let S := T.subtype hax
  have hST : (S : Subgroup (centralizer ({x'} : Set G))).map
      (centralizer ({x'} : Set G)).subtype = (T : Subgroup G) := by
    exact map_subgroupOf_eq_of_le hax
  have hxy' : IsConj x' y' :=
    (isConj_iff.mpr ⟨a,rfl⟩).symm.trans (hc.trans (isConj_iff.mpr ⟨b,rfl⟩))
  obtain ⟨c,hcN,he⟩ := exists_normalizer_conjugator_of_centralizer_sylow x' y' S
    (hST ▸ hby) hxy'
  rw [hST] at hcN
  refine ⟨b⁻¹*c*a,mul_mem (mul_mem (inv_mem hb) (hNT hcN)) ha,?_⟩
  have he' : c*(a*x*a⁻¹)*c⁻¹ = b*y*b⁻¹ := he
  calc
    (b⁻¹*c*a)*x*(b⁻¹*c*a)⁻¹ = b⁻¹*(c*(a*x*a⁻¹)*c⁻¹)*b := by group
    _ = b⁻¹*(b*y*b⁻¹)*b := by rw [he']
    _ = y := by group

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
