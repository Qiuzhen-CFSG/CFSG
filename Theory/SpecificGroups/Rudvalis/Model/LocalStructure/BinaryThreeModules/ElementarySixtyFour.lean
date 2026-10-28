module

public import Theory.SpecificGroups.Rudvalis.Model.LocalStructure.BinaryThreeModules.ElementarySixtyFourData
public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix

/-!
# Native elementary subgroups of order sixty-four in Rudvalis

The literal Sylow candidate has four possible elementary subgroups of order
sixty-four. The finite point-action certificate forces every involutory,
commuting collection of that size into one of the four rows; Sylow conjugacy
then gives the same placement for every native elementary subgroup.

This is the elementary placement used by the Ru local inspection in
Aschbacher--Smith 4.4.3, printed pp.622--623. The action of the row normalizers
is established separately.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Rudvalis.BinaryThreeModules.ElementarySixtyFour
open TwoRankSix
open SylowOvergroups.RadicalCoverage.SylowCertificate
open SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder

@[expose] def row (j : Fin 4) : Subgroup Model :=
  closure (Set.range (fun c : Fin 64 => candidateNormalForm (rowIndex j c)))

private theorem pointCommute_of_commute (m n : Fin 16384)
    (h : Commute (candidateNormalForm m) (candidateNormalForm n)) : pointCommute m n := by
  have hp (x : Fin 4060) : normalMap m (normalMap n x) = normalMap n (normalMap m x) := by
    have he := congrArg (fun g : Model => g • x) h.eq
    simpa only [mul_smul,normal_smul] using he
  exact ⟨hp 0,hp 1⟩

/-- Every elementary subgroup of order sixty-four in the literal Sylow candidate
is one of four explicitly generated native subgroups. -/
theorem candidate_eq_row (E : Subgroup Model) (hE : E ≤ candidate)
    [IsElementaryAbelian 2 E] (hcard : Nat.card E = 64) :
    ∃ j : Fin 4, E = row j := by
  classical
  let n : E → Fin 16384 := fun x =>
    Classical.choose (exists_candidateNormalForm (hE x.property))
  have hn (x : E) : candidateNormalForm (n x) = (x : Model) :=
    Classical.choose_spec (exists_candidateNormalForm (hE x.property))
  have hsq (x : E) : candidateNormalForm (n x) ^ 2 = 1 := by
    rw [hn]
    exact elemPow_eq_one_of_isElementaryAbelian _ x.property
  have hco (x y : E) : Commute (candidateNormalForm (n x)) (candidateNormalForm (n y)) := by
    rw [hn,hn]
    exact setLike_mul_comm x.property y.property
  have hp (x y : E) : pointCommute (n x) (n y) := pointCommute_of_commute _ _ (hco x y)
  have hi : Function.Injective (fun x : E => label (n x)) := by
    intro x y hxy
    apply Subtype.ext
    have he := index_eq_of_commute_of_label_eq (n x) (n y) (hsq x) (hsq y) (hco x y) hxy
    rw [←hn x,←hn y,he]
  have hs : Function.Surjective (fun x : E => label (n x)) :=
    (hi.bijective_of_nat_card_le (by rw [Nat.card_fin,hcard])).2
  have he (x : E) : entry (label (n x)) (slot (n x)) = n x :=
    entry_of_square_eq_one _ (hsq x)
  obtain ⟨z,hz⟩ := hs 1
  change label (n z) = 1 at hz
  have hz' : n z = 6144 := by
    rw [←he z,hz]
    exact forced_first _
  obtain ⟨v,hv⟩ := hs 36
  change label (n v) = 36 at hv
  obtain ⟨j,hj⟩ := branch_entry (slot (n v))
  have hj' : n v = branchSeed j := by
    rw [←he v,hv]
    exact hj
  obtain ⟨w,hw⟩ := hs 4
  change label (n w) = 4 at hw
  have hw' : n w = supportSeed j := by
    have hc := forced_fourth j (slot (n w))
    rw [←hw,he w] at hc
    rcases hc with hc | hc | hc
    · exact hc
    · exact (hc (hz' ▸ hp w z)).elim
    · exact (hc (hj' ▸ hp w v)).elim
  have hrow (x : E) : n x = rowIndex j (label (n x)) := by
    have hc := row_restriction j (label (n x)) (slot (n x))
    rw [he x] at hc
    rcases hc with hc | hc | hc | hc
    · exact hc
    · exact (hc (hz' ▸ hp x z)).elim
    · exact (hc (hj' ▸ hp x v)).elim
    · exact (hc (hw' ▸ hp x w)).elim
  refine ⟨j,le_antisymm ?_ ?_⟩
  · intro x hx
    have hnx := hn ⟨x,hx⟩
    rw [hrow] at hnx
    change candidateNormalForm (rowIndex j (label (n ⟨x,hx⟩))) = x at hnx
    rw [←hnx]
    exact subset_closure (Set.mem_range_self _)
  · apply (closure_le _).2
    rintro x ⟨c,rfl⟩
    obtain ⟨x,hx⟩ := hs c
    change label (n x) = c at hx
    have hnx := hn x
    rw [hrow,hx] at hnx
    change candidateNormalForm (rowIndex j c) ∈ E
    rw [hnx]
    exact x.property

/-- Every native elementary sixty-four subgroup is conjugate to one of the
four certified rows, without a Sylow-normality or odd-index hypothesis. -/
theorem exists_conjugate_row (E : Subgroup Model)
    [IsElementaryAbelian 2 E] (hcard : Nat.card E = 64) :
    ∃ g : Model, ∃ j : Fin 4, E.map (MulAut.conj g).toMonoidHom = row j := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hodd : ¬ 2 ∣ candidate.index := by
    intro hi
    apply not_two_pow_fifteen_dvd_card_model
    rw [←candidate.card_mul_index,candidate_card]
    exact Nat.mul_dvd_mul_left 16384 hi
  let P : Sylow 2 Model := candidate_isTwoGroup.toSylow hodd
  obtain ⟨S,hES⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model S P
  let f := (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 (E.map f) := IsElementaryAbelian.map f
  have hEP : E.map f ≤ candidate := by
    have hh := map_mono (f := f) hES
    change E.map f ≤ (g • S : Sylow 2 Model) at hh
    rw [hg] at hh
    exact hh
  have hc : Nat.card (E.map f) = 64 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,hcard]
  obtain ⟨j,hj⟩ := candidate_eq_row (E.map f) hEP hc
  exact ⟨g,j,hj⟩

end Rudvalis.BinaryThreeModules.ElementarySixtyFour
