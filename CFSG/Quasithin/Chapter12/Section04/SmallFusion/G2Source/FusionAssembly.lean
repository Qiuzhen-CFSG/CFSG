module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Fusion
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Representatives
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion

/-!
# Original binary G₂ fusion and its commutator consumer

The original fixed-involution setup and the Weyl calculation give weak closure
of the fixed line in the whole chosen module.  Sylow conjugacy then gives
normalizer control of fusion.  The second theorem applies the weak-closure
conclusion to the literal 12.4.9 commutator obstruction.

The source inclusion `N_G(T) ≤ N_G(L)` and the B.4.6 commutator geometry
remain explicit.  Neither the contrary 12.2.13 `NoEscape` hypothesis nor a
vanishing assertion for the natural quotient is used.

Source: Aschbacher--Smith 12.4.3, 12.4.7 and 12.4.9, pp.813--816.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02
open ChapterB.QuasisimpleSource

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The fixed-line and fusion conclusions of original 12.4.7 in the binary
G₂ Weyl row, conditional only on the source Sylow-normalizer inclusion. -/
theorem source_g2_fusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)))
    (hne : fixedSubgroup L V ≠ ⊥)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ z : G, orderOf z = 2 ∧ fixedSubgroup L V = zpowers z ∧
      centralizer ({z} : Set G) ≤ normalizer (V : Set G) ∧
      (∀ g : G, MulAut.conj g z ∈ V → MulAut.conj g z = z) ∧
      ∀ x ∈ V, ∀ y ∈ V, IsConj x y →
        ∃ m ∈ normalizer (L : Set G), MulAut.conj m x = y := by
  classical
  obtain ⟨z, hz, hzgen, hM, hMV, hzOmega, _⟩ :=
    exists_fixed_involution_setup h D structural e hne
  have hz1 : z ≠ 1 := by
    intro he
    simp [he] at hz
  have hzfixed : z ∈ fixedSubgroup L V := by
    change z ∈ V ⊓ centralizer (L : Set G)
    rw [hzgen]
    exact mem_zpowers z
  have hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z := by
    intro w hwV hwL
    have hw : w ∈ zpowers z := by
      rw [← hzgen]
      exact ⟨hwV, hwL⟩
    rw [mem_zpowers_iff_mem_range_orderOf, hz] at hw
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hw
    have hnlt : n < 2 := Finset.mem_range.mp hn
    interval_cases n <;> simp
  have hcentral := exists_sylow_central_representatives h D structural e
    hzfixed.1 hz1 hzfixed.2 hfixed hM
  have hweak := weakly_closed_of_sylow_central_representatives hNT
    hzfixed.1 hz1 hM hzOmega hcentral
  exact ⟨z, hz, hzgen, hM.symm.le.trans hMV.le, hweak,
    fusion_of_sylow_central_representatives hNT hzfixed.1 hz1 hweak hcentral⟩

/-- The literal 12.4.9 consumer with its G₂ weak-closure premise discharged.
The fixed-line containment and conjugation symmetry are precisely the remaining
B.4.6 module calculations. -/
theorem lemma_12_4_9_of_g2_weyl
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)))
    (hne : fixedSubgroup L V ≠ ⊥)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (g : G)
    (hA : V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G))
    (hfixed : fixedSubgroup L V ≤ ⁅V, V.map (MulAut.conj g).toMonoidHom⁆)
    (hsymmetry : (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map
      (MulAut.conj g).toMonoidHom = ⁅V, V.map (MulAut.conj g).toMonoidHom⁆)
    (hcomm : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  let _ := D.elementary
  obtain ⟨z, _, hzgen, hcent, hweak, _⟩ :=
    source_g2_fusion h D structural e hne hNT
  have hzfixed : z ∈ fixedSubgroup L V := by
    rw [hzgen]
    exact mem_zpowers z
  have hL : L ≤ centralizer ({z} : Set G) := by
    intro l hl
    exact mem_centralizer_singleton_iff.mpr (hzfixed.2 l hl)
  apply SmallFusion.lemma_12_4_9 hL hA _ hcent (hfixed hzfixed) hsymmetry hcomm
  intro a ha
  exact ⟨1, L.one_mem, by simpa using hweak a ha⟩

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
