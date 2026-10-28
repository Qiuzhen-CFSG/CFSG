module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.HeadPlane
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.MiddleParabolic.Center
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.SylowFlags

/-!
# The source Sylow flag with its marked head plane

A Sylow two-subgroup of GL₄(2) determines a full flag. Its invariant
subspaces are exactly the cuts, so its invariant two-plane is the prescribed
image of V₃. An invariant line is likewise the first cut. The group and
head coordinates stay fixed: this constructs the missing hyperplane and
identifies the literal Sylow image with the full flag stabilizer.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed pp.961–962 (PDF pp.978–979).
These flag statements do not identify Uα* with the Sylow center.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking
open Subgroup ChiefFactors
open BinaryLinear.MiddleParabolic BinaryLinear.InvariantNodeActions

/-- The prescribed invariant two-plane is retained in a full Sylow flag. -/
theorem exists_flag_through_plane {H : Type*} [Group H] [Finite H]
    (eH : H ≃* BinaryLinear.GL NaturalSpace)
    (T : Sylow 2 H) (P : Submodule (ZMod 2) NaturalSpace)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hTP : (T : Subgroup H).map eH.toMonoidHom ≤ BinaryLinear.parabolic P) :
    ∃ L F : Submodule (ZMod 2) NaturalSpace,
      L ≤ P ∧ P ≤ F ∧ Module.finrank (ZMod 2) L = 1 ∧
      Module.finrank (ZMod 2) F = 3 ∧
      (T : Subgroup H).map eH.toMonoidHom = borel L P F := by
  let S := T.mapSurjective (f := eH.toMonoidHom) eH.surjective
  obtain ⟨b, hb⟩ := sylow_eq_cutStabilizer (m := 3) S
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hP
    omega
  have hP1 : P ≠ ⊤ := by
    intro h
    rw [h, finrank_top] at hP
    norm_num [NaturalSpace] at hP
  have hSP : cutStabilizer b Set.univ ≤ BinaryLinear.parabolic P := by
    rw [← hb]
    exact hTP
  obtain ⟨i, hi⟩ := fullFlag_invariant_subspace b P hP0 hP1 hSP
  have hi1 : i = 1 := by
    have hd := cutSpace_finrank b i
    rw [← hi, hP] at hd
    exact Fin.ext (by omega)
  have hPeq : P = cutSpace b 1 := hi1 ▸ hi
  refine ⟨cutSpace b 0, cutSpace b 2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hPeq]
    exact cutSpace_mono b (by decide : (0 : Fin 3) ≤ 1)
  · rw [hPeq]
    exact cutSpace_mono b (by decide : (1 : Fin 3) ≤ 2)
  · exact cutSpace_finrank b 0
  · exact cutSpace_finrank b 2
  · change (S : Subgroup (BinaryLinear.GL NaturalSpace)) = _
    rw [hb, hPeq]
    ext x
    rw [mem_cutStabilizer]
    change (∀ i ∈ (Set.univ : Set (Fin 3)), ∀ v,
      x v ∈ cutSpace b i ↔ v ∈ cutSpace b i) ↔
      ((∀ v, x v ∈ cutSpace b 0 ↔ v ∈ cutSpace b 0) ∧
       (∀ v, x v ∈ cutSpace b 2 ↔ v ∈ cutSpace b 2)) ∧
       (∀ v, x v ∈ cutSpace b 1 ↔ v ∈ cutSpace b 1)
    constructor
    · intro hx
      exact ⟨⟨hx 0 (Set.mem_univ _), hx 2 (Set.mem_univ _)⟩, hx 1 (Set.mem_univ _)⟩
    · rintro ⟨⟨h0, h2⟩, h1⟩ i _
      fin_cases i
      · exact h0
      · exact h1
      · exact h2

/-- The one-space can also be prescribed; it is the unique first cut of the Sylow flag. -/
theorem exists_flag_through_line_plane {H : Type*} [Group H] [Finite H]
    (eH : H ≃* BinaryLinear.GL NaturalSpace)
    (T : Sylow 2 H) (L P : Submodule (ZMod 2) NaturalSpace)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hTL : (T : Subgroup H).map eH.toMonoidHom ≤ BinaryLinear.parabolic L)
    (hTP : (T : Subgroup H).map eH.toMonoidHom ≤ BinaryLinear.parabolic P) :
    ∃ F : Submodule (ZMod 2) NaturalSpace,
      L ≤ P ∧ P ≤ F ∧ Module.finrank (ZMod 2) F = 3 ∧
      (T : Subgroup H).map eH.toMonoidHom = borel L P F := by
  obtain ⟨L', F, hLP, hPF, hL', hF, hT⟩ := exists_flag_through_plane eH T P hP hTP
  let S := T.mapSurjective (f := eH.toMonoidHom) eH.surjective
  obtain ⟨b, hb⟩ := sylow_eq_cutStabilizer (m := 3) S
  have first_cut (J : Submodule (ZMod 2) NaturalSpace)
      (hJ : Module.finrank (ZMod 2) J = 1)
      (hTJ : (T : Subgroup H).map eH.toMonoidHom ≤ BinaryLinear.parabolic J) :
      J = cutSpace b 0 := by
    have hJ0 : J ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hJ
      omega
    have hJ1 : J ≠ ⊤ := by
      intro h
      rw [h, finrank_top] at hJ
      norm_num [NaturalSpace] at hJ
    obtain ⟨i, hi⟩ := fullFlag_invariant_subspace b J hJ0 hJ1 (by rw [← hb]; exact hTJ)
    have hi0 : i = 0 := by
      have hd := cutSpace_finrank b i
      rw [← hi, hJ] at hd
      exact Fin.ext (by omega)
    exact hi0 ▸ hi
  have he : L' = L := (first_cut L' hL' (by rw [hT]; exact inf_le_left.trans inf_le_left)).trans
    (first_cut L hL hTL).symm
  exact ⟨F, he ▸ hLP, hPF, hF, he ▸ hT⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking
