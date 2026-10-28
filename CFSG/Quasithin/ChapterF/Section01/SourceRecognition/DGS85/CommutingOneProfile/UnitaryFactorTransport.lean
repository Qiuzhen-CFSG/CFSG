module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NonElementaryMarkedProfile
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Basic

/-!
# Original factors beneath the marked unitary source actors

The actual PSU₃/SU₃ Sylow order is 2^(3m). It rules out the two strict
source enlargements, whose quotient orders are twenty and 144 and whose
Sylow orders are four and sixteen. Thus every unitary marking, including
fixed-field degree one and both covers, identifies the enlargement with
the original starred endpoint. The square-field linear marking at alpha
makes the original alpha parabolic nonsolvable and gives the same equality.

FullNonElementaryMarkedProfile uses these equalities to transport the
source actor markings to the literal original factors. Neither equality
asserts an unrestricted exclusion of the order-144 source alternative.
Source: DGS, Groups and Graphs (1985), (6.1), pp.118--119,
(11.8), pp.175--177; Aschbacher--Smith F.1.9, pp.261--262.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Reduction BenderSuzuki.MatrixGroups
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem unitary_sylow_order {D : Type*} [Group D] [Finite D]
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU D 3 (2^m) ∨ IsSU D 3 (2^m))
    (T : Sylow 2 D) : Nat.card T = 2^(3*m) := by
  have count {H : Type} [Group H] (R : Subgroup H)
      (ho : Nat.card (omegaCenterIn R) = 2^m)
      (hi : (omegaCenterIn R).relIndex R = (2^m)^2) : Nat.card R = 2^(3*m) := by
    have he := relIndex_mul_relIndex (⊥ : Subgroup H) (omegaCenterIn R) R bot_le (map_subtype_le _)
    simp only [relIndex_bot_left,ho,hi] at he
    calc
      Nat.card R = (2^m)^3 := he.symm.trans (by ring)
      _ = 2^(3*m) := by rw [←pow_mul,Nat.mul_comm m 3]
  rcases mark with ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩ | ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩
  · have hi := HermitianForm.SylowOmegaIndex.projective J hm hcard hconj
      (T.mapSurjective (f := e.toMonoidHom) e.surjective)
    have hh := count _ hi.1 hi.2
    change Nat.card ((T : Subgroup D).map e.toMonoidHom) = _ at hh
    rwa [card_map_of_injective (f := e.toMonoidHom) e.injective] at hh
  · have hi := HermitianForm.SylowOmegaIndex.special J hm hcard hconj
      (T.mapSurjective (f := e.toMonoidHom) e.surjective)
    have hh := count _ hi.1 hi.2
    change Nat.card ((T : Subgroup D).map e.toMonoidHom) = _ at hh
    rwa [card_map_of_injective (f := e.toMonoidHom) e.injective] at hh

private theorem unitary_order_exclusions {D : Type*} [Group D]
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU D 3 (2^m) ∨ IsSU D 3 (2^m)) :
    Nat.card D ≠ 20 ∧ Nat.card D ≠ 144 := by
  let : Finite D := (mark.elim (.projective_unitary m hm) (.special_unitary m hm) : IsRankOneModel D).finite
  let T : Sylow 2 D := Classical.choice inferInstance
  have hc := unitary_sylow_order hm mark T
  constructor
  · intro he
    have ht : Nat.card T = 2^2 := by rw [T.card_eq_multiplicity,he]; decide +kernel
    have hp := Nat.pow_right_injective (by decide : 1 < (2:ℕ)) (hc.symm.trans ht)
    omega
  · intro he
    have ht : Nat.card T = 2^4 := by rw [T.card_eq_multiplicity,he]; decide +kernel
    have hp := Nat.pow_right_injective (by decide : 1 < (2:ℕ)) (hc.symm.trans ht)
    omega

/-- An actual unitary marking rules out both strict enlargements, including
at degree one. Equality retains the original starred subgroup. -/
theorem unitary_enlargedEndpoint_eq_starred (h : HypothesisF11 L S)
    (i : Fin 2) {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) 3 (2^m) ∨
      IsSU (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) 3 (2^m)) :
    enlargedEndpoint L S i = starredParabolic L S i := by
  have hx := unitary_order_exclusions hm mark
  cases h.quotient i with
  | linear n hn hi =>
    obtain ⟨k,hF,hfin,hcard,⟨e⟩⟩ := hi
    let : Fintype k := Fintype.ofFinite k
    let : CharP k 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact reduced_enlargedEndpoint_eq_starred_of_linear h i e
  | suzuki n he =>
    exact reduced_enlargedEndpoint_eq_starred_of_suzuki_all h i n he.some
  | projective_unitary n hn hi =>
    obtain ⟨k,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hi
    by_cases hn2 : 2 ≤ n
    · exact reduced_enlargedEndpoint_eq_starred_of_projective_unitary h i J hn2 hcard hconj e
    · have hn1 : n = 1 := by omega
      subst n
      exact (original_small_projective_enlargement_alternatives h i J
        (by simpa using hcard) (by simpa using hconj) e).resolve_right hx.2
  | special_unitary n hn hi =>
    obtain ⟨k,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hi
    by_cases hn2 : 2 ≤ n
    · exact reduced_enlargedEndpoint_eq_starred_of_special_unitary h i J hn2 hcard hconj e
    · have hn1 : n = 1 := by omega
      subst n
      exact original_small_special_enlargement h i J
        (by simpa using hcard) (by simpa using hconj) e
  | dihedral he =>
    apply (reduced_dihedral_enlargement_alternatives h i he.some).resolve_right
    rintro ⟨e⟩
    apply hx.1
    exact (Nat.card_congr e.toEquiv).trans
      ((Nat.card_congr FiveFour.suzukiZeroEquiv.toEquiv).symm.trans FiveFour.card)

private theorem square_linear_not_solvable {D : Type*} [Group D]
    {m : ℕ} (hm : 0 < m) (mark : ClassicalGroup.IsPSL D 2 (2^(2*m))) :
    ¬ Group.IsSolvable D := by
  obtain ⟨k,hF,hfin,hcard,⟨e⟩⟩ := mark
  let : Fintype k := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hk : 2 < Nat.card k := by
    rw [hcard]
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (show 2 ≤ 2*m by omega)
    norm_num at hh ⊢
    omega
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_perfect hk
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple hk
  intro hs
  let := hs
  let f := e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm
  exact Group.IsPerfect.not_isSolvable SL(2,k)
    (Group.isSolvable_of_surjective (f := f.toMonoidHom) f.surjective)

/-- The square-field linear alpha marking makes its original parabolic
nonsolvable, and hence identifies its enlargement with its starred subgroup. -/
theorem square_linear_enlargedEndpoint_eq_starred (h : HypothesisF11 L S)
    (i : Fin 2) {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSL (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) 2 (2^(2*m))) :
    enlargedEndpoint L S i = starredParabolic L S i := by
  apply nonsolvable_enlargedEndpoint_eq_starred h i
  intro hs
  let := hs
  have hle : enlargedEndpoint L S i ≤ parabolic L S i := by
    exact sup_le (starredParabolic_le i) ((pCoreIn_le 2 (commonBorel L S)).trans
      (commonBorel_le_parabolic (L := L) (S := S) i))
  let : Group.IsSolvable (enlargedEndpoint L S i) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hle)
  exact square_linear_not_solvable hm mark inferInstance

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
