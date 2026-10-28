module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.ThompsonAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.SymmetricFactors

/-!
# Selection in the quasisimple and symmetric-three branches

The B.5.1 action clauses supply generation by the quasisimple generalized
Fitting subgroup and every Sylow two-subgroup. Intersecting the ambient
Sylow subgroup with the normal Thompson image therefore selects an outside
ordinary component in B.5.6(1).

For an S₃ subgroup with at most two conjugates, its normalizer is normal
and contains every two-perfect subgroup. The Sylow intersection in that
normalizer is a Sylow subgroup there. Applying the residual-containment-or-
centralization lemma in this precise overgroup places the S₃ in N(Y).
The bound on the number of conjugates is an explicit input to this helper;
it is not asserted for unclassified factors.

The final adapters use the actual star map. Theta generation supplies
two-perfectness of Y₊*, and the genuine Y₊/O₂(Y₊) three-group quotient
supplies its solvability. No exponent assertion is made about Y₊ itself.
The mixed-product and outer-extension alternatives remain for final assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1 and
B.5.6, printed pp.99 and 105, and 15.3.15(2)/26(2), pp.1125 and 1130.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.QuotientSelection
variable {A : Type*} [Group A] [Finite A]
variable {D : Type*} [Group D] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Every B.5.1 action branch gives the Sylow supplement on the original actor. -/
theorem quasisimple_sup_sylow (ρ : Representation (ZMod 2) D V)
    {L : Subgroup D} (h : QuasisimpleSourceConclusion ρ L) (P : Sylow 2 D) :
    L ⊔ (P : Subgroup D) = ⊤ := by
  cases h.clause_one with
  | irreducible _ _ _ _ he =>
    rcases he with ht | ⟨hs, _⟩
    · rw [ht, top_sup_eq]
    · exact hs P
  | doubleThree _ ht _ _ _ => rw [ht, top_sup_eq]
  | naturalDual _ _ ht _ => rw [ht, top_sup_eq]
  | repeatedNatural _ _ _ _ _ ht _ => rw [ht, top_sup_eq]

/-- The escaping normal actor has an escaping generalized-Fitting component in B.5.6(1). -/
theorem exists_component_outside_of_quasisimple
    (N M : Subgroup A) [N.Normal] (S : Sylow 2 A)
    (hSM : (S : Subgroup A) ≤ M) (hNM : ¬ N ≤ M)
    (ρ : Representation (ZMod 2) N V)
    (hq : IsQuasisimple (generalizedFitting N))
    (h : QuasisimpleSourceConclusion ρ (generalizedFitting N)) :
    ∃ E : Subgroup N, IsComponent N E ∧ ¬ E.map N.subtype ≤ M := by
  refine ⟨generalizedFitting N,
    ⟨(inferInstance : (generalizedFitting N).Normal).isSubnormal, hq⟩, ?_⟩
  intro he
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal N
  have hgen := congrArg (fun E : Subgroup N => E.map N.subtype)
    (quasisimple_sup_sylow ρ h P)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype,
    hP, subgroupOf_map_subtype] at hgen
  exact hNM (hgen ▸ sup_le he (inf_le_left.trans hSM))

/-- Place an S₃ using its actual normalizer and the Sylow intersection there. -/
theorem symmetricThree_le_of_small_normalizer_index
    (L Y M : Subgroup A) (e : L ≃* Equiv.Perm (Fin 3)) (S : Sylow 2 A)
    (hindex : (normalizer (L : Set A)).index ≤ 2)
    (hY : IsPPerfect 2 Y) (hSM : (S : Subgroup A) ≤ M)
    (hN : normalizer (Y : Set A) = M) : L ≤ M := by
  let P := normalizer (L : Set A)
  have hpos := P.index_ne_zero_of_finite
  have hcases : P.index = 1 ∨ P.index = 2 := by change P.index ≤ 2 at hindex; omega
  let hPn : P.Normal := by
    rcases hcases with h | h
    · rw [index_eq_one.mp h]; infer_instance
    · exact normal_of_index_eq_two h
  have hYP : Y ≤ P := ComponentIntersection.normalizes_of_index_le_two
    (I := ⊤) le_top hY (by simpa using hindex)
  have hLP : L ≤ P := L.le_normalizer
  let eL := subgroupOfEquivOfLe hLP
  have hYL : IsPPerfect 2 (Y.subgroupOf P) :=
    hY.of_surjective (subgroupOfEquivOfLe hYP).symm.toMonoidHom
      (subgroupOfEquivOfLe hYP).symm.surjective
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal P
  have hSY : (T : Subgroup P) ≤ normalizer (Y.subgroupOf P : Set P) := by
    rw [hT, ← subgroupOf_normalizer_eq hYP]
    exact comap_mono (hSM.trans_eq hN.symm)
  have hL := StarSelection.symmetricThree_le_normalizer
    (L.subgroupOf P) (eL.trans e) T (Y.subgroupOf P) hYL hSY
  rw [← subgroupOf_normalizer_eq hYP] at hL
  intro x hx
  rw [← hN]
  exact hL (show (⟨x, hLP hx⟩ : P) ∈ L.subgroupOf P from hx)


omit [Finite A] in
/-- A component which normalizes a solvable subgroup centralizes it. -/
theorem component_centralizes_of_le_normalizer
    (E Y : Subgroup A) (hE : IsComponent A E) [Group.IsSolvable Y]
    (hn : E ≤ normalizer (Y : Set A)) : E ≤ centralizer (Y : Set A) := by
  rcases hE.commutator_dichotomy Y with hz | he
  · exact commutator_eq_bot_iff_le_centralizer.mp hz
  · have hEY : E ≤ Y := (le_iSup_conjugates E Y).trans
      (he ▸ le_normalizer_iff_commutator_le_right.mp hn)
    let _ := hE.2
    let _ : IsSimpleGroup (E ⧸ center E) := hE.2.simple
    let _ : Nontrivial E := (QuotientGroup.mk'_surjective (center E)).nontrivial
    exact (Group.IsPerfect.not_isSolvable E
      (Group.isSolvable_of_isSolvable_injective (inclusion_injective hEY))).elim

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.QuotientSelection

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
open StarSelection.QuotientSelection
variable {G : Type*} [Group G] [Finite G] (d : LocalData G)

/-- The given Sylow subgroup maps to a Sylow subgroup of the literal star quotient. -/
theorem exists_starSylow {I : Subgroup G} (hS : Chapter1.IsSylowIn 2 d.S I) :
    ∃ P : Sylow 2 (d.Star I), (P : Subgroup (d.Star I)) = d.starImage I d.S := by
  obtain ⟨P, hP⟩ := hS
  refine ⟨P.mapSurjective (QuotientGroup.mk'_surjective (localActionKernel d.Z I)), ?_⟩
  have he : (P : Subgroup I) = d.S.subgroupOf I := by
    rw [← hP]
    exact (comap_map_eq_self_of_injective I.subtype_injective _).symm
  rw [Sylow.coe_mapSurjective, he]
  rfl

/-- The earlier theta identity makes the actual star image two-perfect. -/
theorem starYplus_twoPerfect {I : Subgroup G} (hI : I ∈ d.Hplus)
    (hθ : theta (d.MI I) = d.Yplus) : IsPPerfect 2 (d.starImage I d.Yplus) := by
  have hYI : d.Yplus ≤ I := le_sup_left.trans hI.1.2
  have hp : IsPPerfect 2 d.Yplus := hθ ▸ ComponentIntersection.theta_isPPerfect (d.MI I)
  have hpI := hp.of_surjective (subgroupOfEquivOfLe hYI).symm.toMonoidHom
    (subgroupOfEquivOfLe hYI).symm.surjective
  exact hpI.of_surjective ((d.starMap I).subgroupMap (d.Yplus.subgroupOf I))
    ((d.starMap I).subgroupMap_surjective _)

/-- Solvability descends from the genuine quotient by the intrinsic two-core. -/
theorem starYplus_solvable {I : Subgroup G} (hI : I ∈ d.Hplus)
    (hY : IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus)) :
    Group.IsSolvable (d.starImage I d.Yplus) := by
  let _ : Group.IsNilpotent (pCore 2 d.Yplus) := pCore_isNilpotent
  let _ : Group.IsNilpotent (d.Yplus ⧸ pCore 2 d.Yplus) := hY.isNilpotent
  let _ : Group.IsSolvable d.Yplus :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 d.Yplus)).mpr
      ⟨inferInstance, inferInstance⟩
  have hYI : d.Yplus ≤ I := le_sup_left.trans hI.1.2
  let _ : Group.IsSolvable (d.Yplus.subgroupOf I) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hYI).toMonoidHom) (subgroupOfEquivOfLe hYI).injective
  exact Group.isSolvable_of_surjective ((d.starMap I).subgroupMap_surjective _)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Select an ordinary component of J(I)* in the complete quasisimple source branch. -/
theorem exists_star_component_of_quasisimple {I : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 d.S I)
    (hJ : ¬ d.thompsonStar I ≤ d.starImage I d.M)
    (ρ : Representation (ZMod 2) (d.thompsonStar I) V)
    (hq : IsQuasisimple (generalizedFitting (d.thompsonStar I)))
    (ha : QuasisimpleSourceConclusion ρ (generalizedFitting (d.thompsonStar I))) :
    ∃ E : Subgroup (d.thompsonStar I), IsComponent (d.thompsonStar I) E ∧
      ¬ E.map (d.thompsonStar I).subtype ≤ d.starImage I d.M := by
  obtain ⟨P, hP⟩ := d.exists_starSylow hS
  apply exists_component_outside_of_quasisimple (d.thompsonStar I)
    (d.starImage I d.M) P _ hJ ρ hq ha
  rw [hP]
  exact map_mono (comap_mono (inf_le_left.trans d.sylow_le))

/-- The exact star normalizer and escaping image exclude B.5.6(2). -/
theorem thompsonStar_not_symmetricThree {I : Subgroup G}
    (hI : I ∈ d.Hplus) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hθ : theta (d.MI I) = d.Yplus)
    (hN : normalizer (d.starImage I d.Yplus : Set (d.Star I)) = d.starImage I d.M)
    (hJ : ¬ d.thompsonStar I ≤ d.starImage I d.M)
    (e : d.thompsonStar I ≃* Equiv.Perm (Fin 3)) : False := by
  obtain ⟨P, hP⟩ := d.exists_starSylow hS
  apply hJ
  apply StarSelection.symmetricThree_le_of_normalizer_eq (d.thompsonStar I) e P
    (d.starImage I d.Yplus) (d.starImage I d.M) (d.starYplus_twoPerfect hI hθ) _ hN
  rw [hP]
  exact map_mono (comap_mono (inf_le_left.trans d.sylow_le))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
