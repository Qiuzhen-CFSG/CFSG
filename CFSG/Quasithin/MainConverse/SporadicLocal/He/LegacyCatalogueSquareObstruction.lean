module

public import Theory.SpecificGroups.Held.TwoLocalCandidates
public import Theory.GroupTheory.SylowContainingTwoLocal

/-!
# The square obstruction to the legacy Held catalogue

The literal ATLAS max3, max4 and max5 candidates each contain an element
whose square is not the identity.  An elementary abelian two-subgroup,
even after embedding and conjugating, cannot equal any of these candidates.
Every Held Sylow two-subgroup has a nontrivial characteristic elementary
subgroup, namely the image of Ω₁ of its center, so the old universally
quantified catalogue premise is impossible as well.

This diagnoses the legacy subgroup-equality premise in `He.Coverage`;
it makes no assertion about the corrected catalogue of maximal normalizers.
Sources: the unchanged ATLAS max3/max4/max5 words in `TwoLocalCandidates`
and GLS3 Table 5.3p; Aschbacher–Smith, condition E, printed pp.3 and 481.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.HeCoverage.LegacyCatalogueSquareObstruction

open Subgroup

private theorem localWord_sq_ne_one (i : Bool) :
    Held.LocalPairs.PairCoverage.localWord i ^ 2 ≠ (1 : Held.He) := by
  cases i
  · intro h
    have hh := congrArg Held.representation h
    rw [map_pow, map_one] at hh
    exact (by decide +kernel : Held.representation
      (Held.LocalPairs.PairCoverage.localWord false) ^ 2 ≠
      (1 : Equiv.Perm (Fin 2058))) hh
  · intro h
    have hh := congrArg Held.representation h
    rw [map_pow, map_one] at hh
    exact (by decide +kernel : Held.representation
      (Held.LocalPairs.PairCoverage.localWord true) ^ 2 ≠
      (1 : Equiv.Perm (Fin 2058))) hh

private theorem max5Second_sq_ne_one :
    Held.TwoLocalCandidates.max5Second ^ 2 ≠ (1 : Held.He) := by
  intro h
  have hh := congrArg Held.representation h
  rw [map_pow, map_one] at hh
  exact (by decide +kernel : Held.representation Held.TwoLocalCandidates.max5Second ^ 2 ≠
    (1 : Equiv.Perm (Fin 2058))) hh

private theorem candidate_has_nontrivial_square (i : Fin 3) :
    ∃ x ∈ Held.TwoLocalCandidates.subgroup i, x ^ 2 ≠ (1 : Held.He) := by
  fin_cases i
  · exact ⟨_, Held.LocalPairs.PairCoverage.localWord_mem_localOvergroup false,
      localWord_sq_ne_one false⟩
  · exact ⟨_, Held.LocalPairs.PairCoverage.localWord_mem_localOvergroup true,
      localWord_sq_ne_one true⟩
  · exact ⟨_, Held.TwoLocalCandidates.max5Second_mem, max5Second_sq_ne_one⟩

/-- No elementary image equals a conjugate of any literal candidate, regardless
of normality or nontriviality of the elementary subgroup. -/
public theorem elementary_image_ne_candidate_conjugate
    (T : Subgroup Held.He) (R : Subgroup T) (he : IsElementaryAbelian 2 R)
    (i : Fin 3) (g : Held.He) :
    R.map T.subtype ≠
      (Held.TwoLocalCandidates.subgroup i).map (MulAut.conj g).toMonoidHom := by
  let _ := he
  intro h
  obtain ⟨x, hx, hsq⟩ := candidate_has_nontrivial_square i
  have hm : (MulAut.conj g) x ∈ R.map T.subtype := by
    rw [h]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨r, hr, hrg⟩ := Subgroup.mem_map.mp hm
  have hr2 : r ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian r hr
  have hx2 : ((MulAut.conj g) x) ^ 2 = 1 := by
    calc
      ((MulAut.conj g) x) ^ 2 = (T.subtype r) ^ 2 := congrArg (· ^ 2) hrg.symm
      _ = T.subtype (r ^ 2) := (map_pow T.subtype r 2).symm
      _ = 1 := by rw [hr2, map_one]
  apply hsq
  apply (MulAut.conj g).injective
  simpa only [map_pow, map_one] using hx2

/-- The old catalogue premise fails for every actual Sylow two-subgroup of
Held: apply the square obstruction to Ω₁ of its nontrivial center. -/
public theorem not_legacy_catalogue (T : Sylow 2 Held.He) :
    ¬ (∀ R : Subgroup T, R ≠ ⊥ → R.Normal → IsElementaryAbelian 2 R →
      ∃ (i : Fin 3) (g : Held.He),
        R.map (T : Subgroup Held.He).subtype =
          (Held.TwoLocalCandidates.subgroup i).map (MulAut.conj g).toMonoidHom) := by
  intro hcatalogue
  have hdiv : 2 ∣ Nat.card Held.He := by
    rw [← Held.orderOf_a]
    exact orderOf_dvd_natCard Held.a
  let _ : Nontrivial T :=
    (Subgroup.nontrivial_iff_ne_bot (T : Subgroup Held.He)).mpr (T.ne_bot_of_dvd_card hdiv)
  let _ : Nontrivial (center T) := T.isPGroup'.center_nontrivial
  let O := omega₁ (center T) (p := 2)
  let _ : O.Characteristic := omega₁_characteristic _
  let _ : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let R := O.map (center T).subtype
  have hRn : R.Normal := inferInstance
  have hRe : IsElementaryAbelian 2 R := IsElementaryAbelian.map_subtype
  have hcdiv : 2 ∣ Nat.card (center T) :=
    (T.isPGroup'.to_subgroup (center T)).card_eq_or_dvd.resolve_left
      (by have := Finite.one_lt_card (α := center T); omega)
  have hR : R ≠ ⊥ := omega₁_map_subtype_ne_bot (center T) 2 hcdiv
  obtain ⟨i, g, h⟩ := hcatalogue R hR hRn hRe
  exact elementary_image_ne_candidate_conjugate (T : Subgroup Held.He) R hRe i g h

end CFSG.Quasithin.MainConverse.SporadicLocal.HeCoverage.LegacyCatalogueSquareObstruction
