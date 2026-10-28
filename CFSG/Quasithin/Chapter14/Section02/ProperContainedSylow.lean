module
public import CFSG.Quasithin.Chapter14.Section02.ProperOutsideSylow
public import Theory.SpecificGroups.RankTwoCoreSolvableSylow
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic

/-!
# The rank-two quotient cases in the proper completion

Put L=O∞(K₁YS) and R=O₂(YS). If Y is outside L, the cubic residual
argument makes R Sylow in LR. If Y≤L and the actual quotient L/O₂(L)
is PSL₃, SL₃, Sp₄ or G₂ over a field of order at least four, the solved
Borel calculations make Y normalize S∩L. This puts S∩L in R, again
making R Sylow in LR. The literal C.1.29 consumer then contradicts the
proved exclusion of a χ₀ containing component.

The final theorem derives every Sylow, Borel and quasisimplicity condition
from the specified quotient witness. It retains the earlier characteristic-two
and quotient-selection conclusions: it does not assert the FF-model selection.
Source: Aschbacher--Smith 14.2.15, printed pp.985--986.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The source Borel implication in its exact group-theoretic form: Y normalizes
 the actual Sylow intersection of L. -/
theorem core_sylow_of_residual_normalizes_intersection
    (X L Y S : Subgroup G) (hLX : L ≤ X) (hYX : Y ≤ X) (hSX : S ≤ X)
    (hLN : X ≤ normalizer (L : Set G))
    (hsub : (L.subgroupOf X).IsSubnormal)
    (hs : Chapter1.IsSylowIn 2 S X)
    (hYN : Y ≤ normalizer ((S ⊓ L : Subgroup G) : Set G)) :
    Chapter1.IsSylowIn 2 ((Y ⊔ S).pCoreIn 2)
      (L ⊔ (Y ⊔ S).pCoreIn 2) := by
  let B := Y ⊔ S
  let R := B.pCoreIn 2
  have hBX : B ≤ X := sup_le hYX hSX
  have hSN : S ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    (le_inf S.le_normalizer (hSX.trans hLN)).trans inf_normalizer_le_normalizer_inf
  have hBN : B ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) := sup_le hYN hSN
  have hSLR : S ⊓ L ≤ R := le_pCoreIn_of_normalizes
    ((Chapter1.isSylowIn_iff.mp hs).1.to_le inf_le_left)
    (inf_le_left.trans le_sup_right)
    hBN
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hs hLX hsub
  exact (isPGroup_pCoreIn 2 B).exists_sylow_sup_of_coprime_index L R
    (((pCoreIn_le 2 B).trans hBX).trans hLN) P P.not_dvd_index (hP ▸ hSLR)


private theorem core_sylow_of_contained_residual_of_solvable_overgroups
    (X L Y S : Subgroup G) (hLX : L ≤ X) (hYX : Y ≤ X) (hSX : S ≤ X)
    (hLN : X ≤ normalizer (L : Set G))
    (hsub : (L.subgroupOf X).IsSubnormal)
    (hs : Chapter1.IsSylowIn 2 S X)
    (hYL : Y ≤ L) (hsol : Group.IsSolvable (Y ⊔ S : Subgroup G))
    (hmodel : ∀ (P : Sylow 2 L) (B : Subgroup L), Group.IsSolvable B →
      (P : Subgroup L) ≤ B → B ≤ normalizer (P : Set L)) :
    Chapter1.IsSylowIn 2 ((Y ⊔ S).pCoreIn 2)
      (L ⊔ (Y ⊔ S).pCoreIn 2) := by
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hs hLX hsub
  let B := Y ⊔ (S ⊓ L)
  have hBL : B ≤ L := sup_le hYL inf_le_right
  have hBB : B ≤ Y ⊔ S := sup_le_sup_left inf_le_left Y
  let _ := hsol
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective hBB)
  let : Group.IsSolvable (B.subgroupOf L) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hBL).toMonoidHom) (subgroupOfEquivOfLe hBL).injective
  have hPL : (P : Subgroup L) ≤ B.subgroupOf L := by
    intro x hx
    exact mem_sup_right (hP ▸ mem_map_of_mem L.subtype hx)
  have hnorm := hmodel P (B.subgroupOf L) inferInstance hPL
  have hBnorm : B ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    rw [←map_subgroupOf_eq_of_le hBL,←hP]
    exact (map_mono hnorm).trans ((P : Subgroup L).le_normalizer_map L.subtype)
  exact core_sylow_of_residual_normalizes_intersection X L Y S hLX hYX hSX hLN hsub hs
    (le_sup_left.trans hBnorm)


theorem source_proper_completion_false_of_rankTwo_core_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hgen : K ⊔ (T : Subgroup G) = H)
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : (K ⊔ sourceResidual M Mc ⊔ S).pCoreIn 2 ≠ ⊥)
    (hs : Chapter1.IsSylowIn 2 S (K ⊔ sourceResidual M Mc ⊔ S))
    (hXe : (K ⊔ sourceResidual M Mc ⊔ S) ∈ Chapter1.He G)
    {F : Type*} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    (Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.symplecticGroup (Fin 2) F) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.G2.Model F)) → False := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  let Y := sourceResidual M Mc
  let R := (Y ⊔ S).pCoreIn 2
  change (Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) ∨
    Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F) ∨
    Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.symplecticGroup (Fin 2) F) ∨
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.G2.Model F)) → False
  intro he
  have hfour : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn)
  obtain ⟨hq,hmodel⟩ : IsQuasisimple (L ⧸ pCore 2 L) ∧
      (∀ (P : Sylow 2 L) (B : Subgroup L), Group.IsSolvable B →
        (P : Subgroup L) ≤ B → B ≤ normalizer (P : Set L)) := by
    rcases he with he | he | he | he
    · obtain ⟨eL⟩ := he
      exact ⟨IsQuasisimple.of_mulEquiv eL.symm,
        solvable_overgroup_normalizes_of_pslThree_twoCore_quotient hn hF eL⟩
    · obtain ⟨eL⟩ := he
      exact ⟨IsQuasisimple.of_mulEquiv eL.symm,
        solvable_overgroup_normalizes_of_slThree_twoCore_quotient hn hF eL⟩
    · obtain ⟨eL⟩ := he
      let : IsQuasisimple (Matrix.symplecticGroup (Fin 2) F) :=
        Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.quasisimple hfour
      exact ⟨IsQuasisimple.of_mulEquiv eL.symm,
        solvable_overgroup_normalizes_of_spFour_twoCore_quotient hn hF eL⟩
    · obtain ⟨eL⟩ := he
      let : Group.IsPerfect (Atlas.G2.Model F) := Atlas.G2.isPerfect hfour
      let : IsSimpleGroup (Atlas.G2.Model F) := Atlas.G2.isSimple hfour
      have hc : center (Atlas.G2.Model F) = ⊥ := by
        rcases (inferInstance : (center (Atlas.G2.Model F)).Normal).eq_bot_or_eq_top with h | h
        · exact h
        · exact (Group.IsPerfect.not_isMulCommutative (Atlas.G2.Model F)
            (center_eq_top_iff.mp h)).elim
      let : IsQuasisimple (Atlas.G2.Model F) := {
        simple := ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup }
      exact ⟨IsQuasisimple.of_mulEquiv eL.symm,
        solvable_overgroup_normalizes_of_gTwo_twoCore_quotient hn hF eL⟩
  have hsR : Chapter1.IsSylowIn 2 R (L ⊔ R) := by
    by_cases hYL : Y ≤ L
    · obtain ⟨hL,_,_⟩ := source_proper_completion_component hG T hempty hM hu hmany
        hcard e K S hST hK hSN hcore hs
      have hLN : X ≤ normalizer (L : Set G) := by
        have hh := (solvableResidual X).le_normalizer_map X.subtype
        rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
      let : Group.IsSolvable (Y ⊔ (T : Subgroup G) : Subgroup G) :=
        source_residualSylow_solvable hG T hempty hM hu hmany hcard e
      have hsol : Group.IsSolvable (Y ⊔ S : Subgroup G) :=
        Group.isSolvable_of_isSolvable_injective
          (inclusion_injective (sup_le_sup_left hST Y))
      exact core_sylow_of_contained_residual_of_solvable_overgroups X L Y S
        (map_subtype_le _) (le_sup_right.trans le_sup_left) le_sup_right hLN hL.2.subnormal
        hs hYL hsol hmodel
    · exact source_proper_core_sylow_of_residual_not_le hG T hempty hM hu hmany hcard e
        K S hST hK hSN hcore hs hYL
  exact source_proper_completion_sylow_core_false hG T hempty hM hu hmany hcard e H hH
    K S hST hi hgen hK hSN hcore hs hXe hq hsR

end CFSG.Quasithin.Chapter14.Section02
