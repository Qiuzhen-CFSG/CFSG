module
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.ThreeSylowContainment
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.Parabolics
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.SeedGeneration
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.SeedGeneration
public import Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics.Placement.Bruhat
public import Theory.GroupTheory.CComponent.SylowPairSolvableGeneration
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.SolvableSylowControl.Marked
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry

/-!
# Odd solvable supplements to normal Ree C-components

The original exceptional fixed group has the positive Sylow, the full fixed
torus, and its actual two full root parabolics. Positive normal generation
in both fixed seeds and their generation of the fixed group discharge the
Bruhat enlargement argument. Thus every proper Sylow overgroup lies in
one of the two maximal parabolics, whose intersection is the solvable Borel.
The proved solvable-overgroup containment gives intrinsic Sylow control.

C-component minimality, already supplied by the source, then excludes an
odd solvable supplement to a proper invariant nonsolvable subgroup. No
simplicity certification or unspecified geometric premise is needed.
The exponent m is the Ree convention q = 2^(2*m+1); m ≥ 1 excludes the
separate binary and Tits endpoints.

Source: Aschbacher--Smith 5.1.13 and 5.2.2, pp.636 and 648; GLS3
2.3.4--5 and 2.6.5--7 for the fixed Bruhat and root-parabolic geometry.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace ReeF4.OddSupplement
open LargeLocalSeeds Parabolics SectionGeometry.BNPair
open MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
attribute [local instance] borel_inf_normalizerWords_normal
variable {G : Type*} [Group G] [Finite G]

private def sylowBruhat (m : ℕ) : SylowBruhatData (borel m) := by
  have hTB : fixedTorus m ≤ borel m := comap_mono le_sup_right
  refine {
    sylow := ThreeSylowContainment.positiveSylow m
    cartan := fixedTorus m
    monomial := normalizerWords m
    borel_eq := ?_
    cartan_normalizes := ?_
    monomial_normalizes := ?_
    factorization := ?_
    normal_generates := ?_ }
  · rw [ThreeSylowContainment.positiveSylow_coe]
    exact Parabolics.borel_eq_unipotent_sup_fixedTorus m
  · change fixedTorus m ≤ normalizer ((ThreeSylowContainment.positiveSylow m : Subgroup (Model m)) : Set (Model m))
    rw [ThreeSylowContainment.positiveSylow_coe]
    exact hTB.trans (borel_le_unipotent_normalizer m)
  · have hn := borel_inf_normalizerWords_normal m
    rw [borel_inf_normalizerWords] at hn
    exact (normal_subgroupOf_iff_le_normalizer (fixedTorus_le_normalizerWords m)).mp hn
  · intro g
    obtain ⟨u,hu,n,hn,v,hv,he⟩ := Overlap.exists_fixed_normal_form m g
    refine ⟨u,?_,n,hn,v,?_,he⟩
    all_goals rwa [ThreeSylowContainment.positiveSylow_coe]
  · change normalClosure ((ThreeSylowContainment.positiveSylow m : Subgroup (Model m)) : Set (Model m)) = ⊤
    rw [ThreeSylowContainment.positiveSylow_coe]
    let N := normalClosure (unipotent m : Set (Model m))
    have hseed (s : Side) : seed m s ≤ N := by
      have hn : normalClosure ((unipotent m).subgroupOf (seed m s) : Set (seed m s)) ≤
          N.subgroupOf (seed m s) := by
        apply normalClosure_le_normal
        intro x hx
        exact subset_normalClosure hx
      rw [positive_normalClosure_eq_top] at hn
      exact subgroupOf_eq_top.mp (top_le_iff.mp hn)
    apply top_unique
    rw [← Parabolics.OuterLocal.LargeAutomorphisms.seed_sup_eq_top m]
    exact sup_le (hseed .suzuki) (hseed .linear)

/-- The actual fixed Borel is solvable by its positive normal subgroup
and its two-field-unit torus. -/
theorem borel_isSolvable (m : ℕ) : Group.IsSolvable (borel m) := by
  have ht : Group.IsSolvable (fixedTorus m) := by
    rw [← ConverseParabolics.FullLeviRepresentation.torusHom_range]
    exact Group.isSolvable_of_surjective (ConverseParabolics.FullLeviRepresentation.torusHom m).rangeRestrict_surjective
  let := ht
  let : Group.IsNilpotent (unipotent m) := (unipotent_isPGroup m).isNilpotent
  rw [Parabolics.borel_eq_unipotent_sup_fixedTorus]
  exact Group.isSolvable_sup_of_normalizes _ _
    ((show fixedTorus m ≤ borel m from comap_mono le_sup_right).trans
      (borel_le_unipotent_normalizer m))

private theorem proper_borel_le_parabolic (m : ℕ) (hm : 1 ≤ m)
    (J : Subgroup (Model m)) (hB : borel m ≤ J) (hJ : J ≠ ⊤) :
    ∃ s : Side, J ≤ ConverseParabolics.parabolic m s := by
  let T := titsSystem m
  have hclass := T.subgroup_eq_standardParabolic_simpleIndices J hB
  have hI := T.simpleIndices_subset J
  change T.simpleIndices J ⊆ simpleReflections m at hI
  rw [simpleReflections_eq_pair] at hI
  rcases Set.subset_pair_iff_eq.mp hI with he | he | he | he
  · refine ⟨.linear,?_⟩
    rw [hclass,he,T.standardParabolic_empty]
    change borel m ≤ ConverseParabolics.parabolic m .linear
    rw [parabolic_eq_rootParabolic]
    exact borel_le_parabolic m .linear
  · refine ⟨.linear,?_⟩
    rw [hclass,he]
    exact (standardParabolic_singleton_eq_parabolic m hm .linear).le
  · refine ⟨.suzuki,?_⟩
    rw [hclass,he]
    exact (standardParabolic_singleton_eq_parabolic m hm .suzuki).le
  · have hi : T.simpleIndices J = T.S := he.trans (simpleReflections_eq_pair m).symm
    exact (hJ (hclass.trans ((congrArg T.standardParabolic hi).trans T.standardParabolic_S))).elim

/-- Proper overgroups of the full positive Sylow lie in a genuine root parabolic. -/
theorem le_parabolic (m : ℕ) (hm : 1 ≤ m)
    (J : Subgroup (Model m)) (hU : unipotent m ≤ J) (hJ : J ≠ ⊤) :
    ∃ s : Side, J ≤ ConverseParabolics.parabolic m s := by
  obtain ⟨Q,hBQ,hJQ,hQ⟩ := (sylowBruhat m).exists_proper_borel_overgroup J
    (by simpa only [sylowBruhat, ThreeSylowContainment.positiveSylow_coe] using hU) hJ
  obtain ⟨s,hs⟩ := proper_borel_le_parabolic m hm Q hBQ hQ
  exact ⟨s,hJQ.trans hs⟩

/-- Both full root parabolics are maximal in the actual fixed group. -/
theorem parabolic_isCoatom (m : ℕ) (hm : 1 ≤ m) (s : Side) :
    IsCoatom (ConverseParabolics.parabolic m s) := by
  cases s with
  | suzuki =>
    rw [← titsSystem_suzukiParabolic m hm]
    exact (titsSystem m).standardParabolic_isCoatom (simpleReflection_mem m .linear)
  | linear =>
    rw [parabolic_eq_rootParabolic,← titsSystem_linearParabolic m hm]
    exact (titsSystem m).standardParabolic_isCoatom (simpleReflection_mem m .suzuki)

/-- Solvable overgroups normalize their prescribed Sylow subgroup. -/
theorem solvable_sylow_control (m : ℕ) (hm : 1 ≤ m) : SolvableSylowControl 2 (Model m) := by
  apply SolvableSylowControl.of_standard (ThreeSylowContainment.positiveSylow m) (borel m)
  · change normalizer ((ThreeSylowContainment.positiveSylow m : Subgroup (Model m)) : Set (Model m)) = _
    rw [ThreeSylowContainment.positiveSylow_coe]
    exact unipotent_normalizer_eq_borel m
  · intro J hsol hU
    rw [ThreeSylowContainment.positiveSylow_coe] at hU
    exact ThreeSylowContainment.le_borel_of_solvable hm J hsol hU

/-- The two actual parabolics and their solvable overlap transport to every marking. -/
theorem two_sylow_overgroups_of_equiv (m : ℕ) (hm : 1 ≤ m)
    (e : G ≃* Model m) (S : Sylow 2 G) :
    ∃ P Q : Subgroup G, IsCoatom P ∧ IsCoatom Q ∧
      (S : Subgroup G) ≤ P ∧ (S : Subgroup G) ≤ Q ∧
      Group.IsSolvable (P ⊓ Q : Subgroup G) ∧
      ∀ J : Subgroup G, (S : Subgroup G) ≤ J → J ≠ ⊤ → J ≤ P ∨ J ≤ Q := by
  obtain ⟨_,a,_,hS⟩ := SolvableSylowControl.exists_aligned_equiv
    e S (ThreeSylowContainment.positiveSylow m)
  rw [ThreeSylowContainment.positiveSylow_coe] at hS
  let P := (ConverseParabolics.parabolic m .linear).comap a.toMonoidHom
  let Q := (ConverseParabolics.parabolic m .suzuki).comap a.toMonoidHom
  have hu (s : Side) : unipotent m ≤ ConverseParabolics.parabolic m s := by
    rw [parabolic_eq_rootParabolic]
    exact (unipotent_le_borel m).trans (borel_le_parabolic m s)
  have hUP : (S : Subgroup G) ≤ P := map_le_iff_le_comap.mp (by rw [hS]; exact hu .linear)
  have hUQ : (S : Subgroup G) ≤ Q := map_le_iff_le_comap.mp (by rw [hS]; exact hu .suzuki)
  refine ⟨P,Q,isCoatom_comap_of_surjective a.surjective (parabolic_isCoatom m hm .linear),
    isCoatom_comap_of_surjective a.surjective (parabolic_isCoatom m hm .suzuki),
    hUP,hUQ,?_,?_⟩
  · let : Group.IsSolvable (borel m) := borel_isSolvable m
    let f : (P ⊓ Q : Subgroup G) →* borel m :=
      (a.toMonoidHom.comp (P ⊓ Q).subtype).codRestrict (borel m)
        (fun x => (MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.parabolic_inf_eq_borel m hm) ▸ x.property)
    exact Group.isSolvable_of_isSolvable_injective (f := f) (by
      intro x y hxy
      exact Subtype.ext (a.injective (congrArg Subtype.val hxy)))
  · intro J hSJ hJ
    have hj : J.map a.toMonoidHom ≠ ⊤ := by
      intro he
      apply hJ
      apply map_injective (f := a.toMonoidHom) a.injective
      rw [he,map_top_of_surjective _ a.surjective]
    obtain ⟨b,hb⟩ := le_parabolic m hm (J.map a.toMonoidHom) (hS ▸ map_mono hSJ) hj
    cases b with
    | linear => exact Or.inl (map_le_iff_le_comap.mp hb)
    | suzuki => exact Or.inr (map_le_iff_le_comap.mp hb)

/-- The source C-component property suffices for the Ree odd-supplement
exclusion, with no separate simplicity hypothesis on the model. -/
theorem no_odd_solvable_supplement (m : ℕ) (hm : 1 ≤ m)
    (S : Sylow 2 G) (K R D : Subgroup G) [K.Normal] (hK : K.IsCComponent)
    (e : K ≃* Model m) (hRK : R < K) (hRns : ¬ Group.IsSolvable R)
    (hSR : (S : Subgroup G) ≤ normalizer (R : Set G))
    (ho : Odd (Nat.card D)) (hsol : Group.IsSolvable ((S : Subgroup G) ⊔ D : Subgroup G))
    (hgen : R ⊔ (S : Subgroup G) ⊔ D = ⊤) : False := by
  apply cComponent_no_solvable_odd_supplement_of_two_sylow_overgroups S K R D hK hRK hRns hSR ho hsol hgen
  · exact SolvableSylowControl.of_equiv e (solvable_sylow_control m hm)
  · exact two_sylow_overgroups_of_equiv m hm e
end ReeF4.OddSupplement
