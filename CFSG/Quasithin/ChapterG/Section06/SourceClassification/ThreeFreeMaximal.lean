module
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.MinimalParabolicComparison

/-!
# Three-free maximal subgroups exclude the natural S₅ row

A Sylow two-subgroup of S₅ fixes a point in the five-letter action.
The point stabilizer has order twenty-four and is proper. Unique maximality
therefore places its inverse image in the original minimal-parabolic maximal
subgroup, forcing a factor of three. This excludes the S₅ row of the exact
G.6.4 action whenever that maximal subgroup has order prime to three.

Source: Aschbacher–Smith, 10.2.1, printed p.743, using G.6.4.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section06
variable {G : Type*} [Group G] [Finite G]

/-- The unique maximal Sylow overgroup in an S₅ actor has a cubic divisor. -/
theorem three_dvd_minimalParabolicMax_of_symmetricFive
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (e : G ≃* Equiv.Perm (Fin 5)) :
    3 ∣ Nat.card (ChapterB.minimalParabolicMax T hP) := by
  let P := T.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨i,hi⟩ := P.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card (Fin 5) (by simp)
  let B := MulAction.stabilizer (Equiv.Perm (Fin 5)) i
  have hPB : (P : Subgroup (Equiv.Perm (Fin 5))) ≤ B := fun g hg => hi ⟨g,hg⟩
  have hBi : B.index = 5 := by
    rw [MulAction.index_stabilizer,MulAction.orbit_eq_univ]
    simp
  have hBc : Nat.card B = 24 := by
    have hh := B.card_mul_index
    have hS : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    rw [hBi,hS] at hh
    omega
  have hB : B ≠ ⊤ := by intro he; rw [he,index_top] at hBi; omega
  let K := B.comap e.toMonoidHom
  have hK : K ≠ ⊤ := by
    intro he
    have hh := congrArg (map e.toMonoidHom) he
    rw [map_comap_eq_self_of_surjective e.surjective,
      map_top_of_surjective e.toMonoidHom e.surjective] at hh
    exact hB hh
  have hTK : (T : Subgroup G) ≤ K := map_le_iff_le_comap.mp hPB
  have hKM : K ≤ ChapterB.minimalParabolicMax T hP := hP.1.le_maximal
    ⟨(ChapterB.minimalParabolicMax_spec T hP).2,
      (ChapterB.minimalParabolicMax_spec T hP).1.covBy_top⟩ hTK
    (lt_top_iff_ne_top.mpr hK)
  have hKc : Nat.card K = 24 := by
    rw [←card_map_of_injective (f:=e.toMonoidHom) e.injective,
      map_comap_eq_self_of_surjective e.surjective,hBc]
  exact (show 3 ∣ Nat.card K by rw [hKc]; decide).trans (card_dvd_of_le hKM)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {a : G}

/-- A three-free maximal subgroup excludes the literal natural-five model. -/
theorem not_symmetricFive_model_of_three_free_maximal
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hthree : Nat.Coprime 3 (Nat.card (ChapterB.minimalParabolicMax T hP)))
    (W : Submodule (ZMod 2) V) :
    ¬ HasModelOn ρ ⊤ W (BinaryPermutation.naturalRepresentation (Fin 5)) := by
  rintro ⟨e,_,_,_⟩
  have hd := three_dvd_minimalParabolicMax_of_symmetricFive T hP (topEquiv.symm.trans e)
  have hh := hthree.coprime_dvd_right hd
  norm_num at hh

/-- The one-factor source catalogue is the binary plane when the original
unique maximal subgroup has order prime to three. -/
theorem one_factor_binary_plane_of_three_free_maximal
    (h : OneFactor ρ a) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hthree : Nat.Coprime 3 (Nat.card (ChapterB.minimalParabolicMax T hP))) :
    HasModelOn ρ ⊤ ⊤ (binaryLinearAction 2) :=
  (one_factor_minimal_parabolic_models h T hP).resolve_right
    (not_symmetricFive_model_of_three_free_maximal T hP hthree ⊤)

end CFSG.Quasithin.ChapterG.Section06
