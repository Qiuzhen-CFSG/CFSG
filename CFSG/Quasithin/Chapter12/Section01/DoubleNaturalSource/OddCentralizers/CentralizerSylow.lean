module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.Generation
public import Theory.GroupTheory.CharacteristicCentralizerSylow

/-!
# The relative Sylow promotion in 12.1.9

Let Q=C_T(W). Every two-subgroup S containing Q has the same zeroth weak
closure as T. Hence N_G(S) lies in M. If S is Sylow in M∩C_G(U), the
finite two-group normalizer condition promotes S to Sylow in C_G(U).
No assumption that C_T(U) is already Sylow is made: that placement must
first be obtained inside M, as in the source.

Source: Aschbacher--Smith, 12.1.9, p.793, using E.3.15 and E.3.34(2).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)

include D h in
/-- Weak closure controls the normalizer of every relative two-overgroup of Q. -/
theorem doubledOrbit_relative_normalizer_le_of_many
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hw : (1 : ℕ∞) < globalW (componentOrbit V (T : Subgroup G)) T)
    (S : Subgroup G) (hS : IsPGroup 2 S)
    (hQS : (T : Subgroup G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ≤ S) :
    normalizer (S : Set G) ≤ normalizer (L : Set G) := by
  let := D.doubledOrbit_elementary h
  have hw0 : (0 : ℕ∞) < globalW (componentOrbit V (T : Subgroup G)) T :=
    lt_trans (by decide) hw
  have he := SourceContainment.weakClosure_eq_of_centralizer_le T hS hQS hw0
  apply (normalizer_le_weakClosure_normalizer _ S 0).trans
  rw [← he]
  exact SourceContainment.normalizer_weakClosure_zero_le (D.doubledOrbit_E322 h) hw0
    (D.doubledOrbit_centralizer_unique h)

include D h in
/-- The source local Sylow promotes to the full centralizer, with precisely
the same ambient subgroup; no conjugation or quotient change is hidden. -/
theorem doubledOrbit_centralizer_sylow_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hw : (1 : ℕ∞) < globalW (componentOrbit V (T : Subgroup G)) T)
    (U : Subgroup G)
    (S : Sylow 2 ↥(normalizer (L : Set G) ⊓ centralizer (U : Set G)))
    (hQS : (T : Subgroup G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ≤
      (S : Subgroup ↥(normalizer (L : Set G) ⊓ centralizer (U : Set G))).map
        (normalizer (L : Set G) ⊓ centralizer (U : Set G)).subtype) :
    ∃ R : Sylow 2 (centralizer (U : Set G)),
      (R : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype =
      (S : Subgroup ↥(normalizer (L : Set G) ⊓ centralizer (U : Set G))).map
        (normalizer (L : Set G) ⊓ centralizer (U : Set G)).subtype := by
  let C := centralizer (U : Set G)
  let M := normalizer (L : Set G)
  let P := (S : Subgroup ↥(M ⊓ C)).map (M ⊓ C).subtype
  have hP : IsPGroup 2 P := S.isPGroup'.map _
  have hPC : P ≤ C := (map_subtype_le _).trans inf_le_right
  have hN : normalizer (P : Set G) ≤ M :=
    D.doubledOrbit_relative_normalizer_le_of_many h hmany hw P hP hQS
  have hmax (A : Subgroup G) (hA : IsPGroup 2 A) (hPA : P ≤ A)
      (hAC : A ≤ C) (hAM : A ≤ M) : A = P := by
    have hAP := S.is_maximal' (hA.comap_subtype (K := M ⊓ C))
      (map_le_iff_le_comap.mp hPA)
    have hh := congrArg (Subgroup.map (M ⊓ C).subtype) hAP
    change (A.subgroupOf (M ⊓ C)).map (M ⊓ C).subtype = P at hh
    rwa [map_subgroupOf_eq_of_le (le_inf hAM hAC)] at hh
  obtain ⟨R, hPR⟩ := (hP.comap_subtype (K := C)).exists_le_sylow
  have hPR' : P ≤ (R : Subgroup C).map C.subtype := by
    rw [← map_subgroupOf_eq_of_le hPC]
    exact map_mono hPR
  exact ⟨R, prime_overgroup_eq_of_normalizer_control P C M hN hmax _
    (R.isPGroup'.map _) hPR' (map_subtype_le _)⟩

include D h in
/-- Every U≤W has a full centralizer Sylow containing the original Q and
lying in M. This supplies the relative placement needed by the odd actor
construction without assuming C_T(U) is Sylow. -/
theorem doubledOrbit_exists_centralizer_sylow_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hw : (1 : ℕ∞) < globalW (componentOrbit V (T : Subgroup G)) T)
    (U : Subgroup G) (hUW : U ≤ componentOrbit V (T : Subgroup G)) :
    ∃ R : Sylow 2 (centralizer (U : Set G)),
      (T : Subgroup G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ≤
        (R : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype ∧
      (R : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype ≤
        normalizer (L : Set G) := by
  let Q := (T : Subgroup G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G)
  let MU := normalizer (L : Set G) ⊓ centralizer (U : Set G)
  have hQ : IsPGroup 2 Q := T.isPGroup'.to_inf_left
  have hQM : Q ≤ MU := le_inf (inf_le_left.trans D.sylow_normalizes_component)
    (inf_le_right.trans (centralizer_le hUW))
  obtain ⟨S, hQS⟩ := (hQ.comap_subtype (K := MU)).exists_le_sylow
  have hQS' : Q ≤ (S : Subgroup MU).map MU.subtype := by
    rw [← map_subgroupOf_eq_of_le hQM]
    exact map_mono hQS
  obtain ⟨R, hR⟩ := D.doubledOrbit_centralizer_sylow_of_many h hmany hw U S hQS'
  exact ⟨R, hQS'.trans_eq hR.symm, hR.le.trans ((map_subtype_le _).trans inf_le_left)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
