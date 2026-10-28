module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import Theory.GroupTheory.ComponentLocalOrbitCore

public import CFSG.Quasithin.Chapter1.Section01
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.TwoLocalUniqueness
public import Theory.GroupTheory.PGroup.Omega
public import Theory.Quasithin.Rank

/-!
# Nonsolvable uniqueness from the earlier source results

This module proves all four conclusions of Aschbacher–Smith Theorem 1.2.7
for a finite simple QTKE group, its Sylow two-subgroup T, and a member L of
the canonical family LStar. The sufficient inputs are the universal
containment assertion of A.3.12, the normal-or-index-two part of A.3.8(3),
and 1.1.4(6). The original full-model input record remains unchanged.
The characteristic-two inheritance of 1.1.3(1) is already proved in Theory.

The local quotient is SQTK by QT, K, and the odd-prime rank bound for a
quotient by a normal two-group. Containment and maximality make L a relative
C-component in every eligible overgroup. The one-or-two-conjugate alternative
makes the actual T-orbit L₀ normal in those overgroups. Characteristic two
provides its nontrivial two-core, so maximal two-locality identifies N_G(L₀).
The elementary centralizer argument then proves the last intersection clause.
Throughout, L₀ is the conjugate-generated subgroup, distinct from L₀ sup T.

`nonsolvable_uniqueness_of_earlier` is a complete conditional deduction. The
section owner must instantiate `UniquenessEarlierResults` before advertising
an unconditional numbered source theorem. No centre–Frattini assertion is used.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Theorem 1.2.7 and its proof, printed p.506; earlier
results on pp.500–505 and Appendix A, Section 3.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem orbit_normal (B : Subgroup G) (S : Sylow 2 G)
    (hB : B.Normal ∨ (normalizer (B : Set G)).index = 2) :
    (componentOrbit B (S : Subgroup G)).Normal := by
  rcases hB with hn | hi
  · let := hn
    have he : componentOrbit B (S : Subgroup G) = B := by
      apply le_antisymm _ (le_componentOrbit B _)
      apply iSup_conjugates_le_of_le_normalizer B _ B le_rfl
      rw [normalizer_eq_top]
      exact le_top
    rw [he]
    exact hn
  · have hs : ¬ (S : Subgroup G) ≤ normalizer (B : Set G) := by
      intro hs
      have hd := index_dvd_of_le hs
      rw [hi] at hd
      exact S.not_dvd_index hd
    obtain ⟨s, hs, hsn⟩ := Set.not_subset.mp hs
    have hconj (g : G) : B.map (MulAut.conj g).toMonoidHom ≤
        componentOrbit B (S : Subgroup G) := by
      by_cases hg : g ∈ normalizer (B : Set G)
      · exact (show B.map (MulAut.conj g).toMonoidHom = B from
          mem_normalizer_iff_map_conj_eq.mp hg).le.trans (le_componentOrbit B _)
      have hsg : s⁻¹ * g ∈ normalizer (B : Set G) :=
        (mul_mem_iff_of_index_two hi).mpr (iff_of_false (by simpa using hsn) hg)
      have he : B.map (MulAut.conj g).toMonoidHom = B.map (MulAut.conj s).toMonoidHom := by
        calc
          _ = (B.map (MulAut.conj (s⁻¹ * g)).toMonoidHom).map
              (MulAut.conj s).toMonoidHom := by
            rw [map_map]
            congr 1
            ext x
            simp [MulAut.conj_apply, mul_assoc]
          _ = _ := congrArg (map (MulAut.conj s).toMonoidHom)
            (show B.map (MulAut.conj (s⁻¹ * g)).toMonoidHom = B from
              mem_normalizer_iff_map_conj_eq.mp hsg)
      rw [he]
      exact le_iSup (fun a : (S : Subgroup G) => B.map (MulAut.conj (a : G)).toMonoidHom) ⟨s, hs⟩
    have he : componentOrbit B (S : Subgroup G) = componentOrbit B ⊤ := by
      apply le_antisymm
      · apply iSup_le
        intro s
        exact le_iSup (fun a : (⊤ : Subgroup G) => B.map (MulAut.conj (a : G)).toMonoidHom)
          ⟨s, mem_top _⟩
      · exact iSup_le fun g => hconj g
    rw [he, ← normalizer_eq_top_iff]
    apply top_unique
    simpa only [sup_top_eq] using
      (normal_subgroupOf_iff_le_normalizer (componentOrbit_le_sup B ⊤)).mp
        (componentOrbit_normal_subgroupOf_sup B ⊤)

private theorem orbit_normal_in {H B : Subgroup G} (T : Sylow 2 G)
    (hBH : B ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hB : (B.subgroupOf H).Normal ∨
      (normalizer (B.subgroupOf H : Set H)).index = 2) :
    ((componentOrbit B (T : Subgroup G)).subgroupOf H).Normal := by
  let S := T.subtype hTH
  let D := componentOrbit (B.subgroupOf H) (S : Subgroup H)
  have hn : D.Normal := orbit_normal _ S hB
  have he : D.map H.subtype = componentOrbit B (T : Subgroup G) := by
    rw [map_componentOrbit]
    simp only [S, Sylow.coe_subtype, map_subgroupOf_eq_of_le hBH,
      map_subgroupOf_eq_of_le hTH]
  have hd : (D.map H.subtype).subgroupOf H = D :=
    comap_map_eq_self_of_injective H.subtype_injective D
  rw [← he, hd]
  exact hn


/-- The SQTK hypotheses on the actual local quotient follow from QT and K.
The quotient rank bound uses its normal two-group kernel. -/
theorem uniqueness_local_quotient_sqtk {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G) {H : Subgroup G} (hH : H ∈ Chapter1.H G) :
    IsSQTK κ (H ⧸ pCore 2 H) := by
  let R := H.pCoreIn 2
  let N := normalizer (R : Set G)
  have hHN : H ≤ N := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hN : IsTwoLocal N := ⟨R, hH, isPGroup_pCoreIn 2 H, rfl⟩
  have hlocal : IsSQTK κ H := by
    have hh := (hG.twoLocal_sqtk hN).subgroup (H.subgroupOf N)
    exact ⟨hh.stronglyQuasithin.of_injective
      (subgroupOfEquivOfLe hHN).symm.toMonoidHom (subgroupOfEquivOfLe hHN).symm.injective,
      hh.isKGroup.of_injective
        (subgroupOfEquivOfLe hHN).symm.toMonoidHom (subgroupOfEquivOfLe hHN).symm.injective⟩
  refine ⟨?_, hlocal.isKGroup.quotient _⟩
  intro p hp ho
  let _ : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hlocal.stronglyQuasithin p hp ho)

/-- Universal earlier-source inputs for the nonsolvable uniqueness deduction.
There are no conclusions about the chosen local subgroup among these premises.
The 1.1.3(1) inheritance step is already proved in
`Subgroup.subnormal_core_selfCentralizing`. -/
structure UniquenessEarlierResults (κ : GroupClass.{u}) : Prop where
  containment : ∀ (X : Type u) [Group X] [Finite X],
    IsSQTK κ X → pCore 2 X = ⊥ → ∀ (S : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents S →
      ∃! K : Subgroup X, K.IsCComponent ∧ B ≤ K
  conjugates : ∀ (X : Type u) [Group X] [Finite X],
    IsSQTK κ X → pCore 2 X = ⊥ → ∀ B : Subgroup X, B.IsCComponent →
      B.Normal ∨ (normalizer (B : Set X)).index = 2 ∧ NonnormalCComponentModel B
  characteristicTwo : ∀ (X : Type u) [Group X] [Finite X], IsSimpleQTKE κ X →
    ∀ S : Sylow 2 X, HOver X (S : Set X) ⊆ He X

/-- The four source conclusions, with relative C-components and the actual
T-conjugate closure. The overgroup and properness fields also record that the
normalizer is a proper overgroup of the required join. -/
structure NonsolvableUniquenessConclusion (T : Sylow 2 G) (L : Subgroup G) : Prop where
  component : ∀ H : Subgroup G,
    H ∈ HOver G ((L ⊔ (T : Subgroup G) : Subgroup G) : Set G) →
      (L.subgroupOf H).IsCComponent
  generalizedFitting_eq_pCore : generalizedFitting L = pCore 2 L
  normalizer_maximal :
    IsMaximalTwoLocal (normalizer (componentOrbit L (T : Subgroup G) : Set G))
  normalizer_contains : L ⊔ (T : Subgroup G) ≤
    normalizer (componentOrbit L (T : Subgroup G) : Set G)
  normalizer_proper : normalizer (componentOrbit L (T : Subgroup G) : Set G) ≠ ⊤
  normalizer_unique : ∀ M : Subgroup G, IsMaximalTwoLocal M →
    L ⊔ (T : Subgroup G) ≤ M →
      M = normalizer (componentOrbit L (T : Subgroup G) : Set G)
  centralizer_intersection : ∀ g : G,
    g ∉ normalizer (componentOrbit L (T : Subgroup G) : Set G) →
      let Z := ((omega₁ (center T) (p := 2)).map (center T).subtype).map
        (T : Subgroup G).subtype
      (Z ⊓ centralizer (componentOrbit L (T : Subgroup G) : Set G)) ⊓
        (Z ⊓ centralizer (componentOrbit L (T : Subgroup G) : Set G)).map
          (MulAut.conj g).toMonoidHom = ⊥

private theorem component_in_eligible_overgroup
    {κ : GroupClass.{u}}
    (hContainment : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK κ X → pCore 2 X = ⊥ → ∀ (S : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents S →
      ∃! K : Subgroup X, K.IsCComponent ∧ B ≤ K)
    (hG : IsSimpleQTKE κ G) {T : Sylow 2 G} {L H : Subgroup G}
    (hL : L ∈ LStar G (T : Subgroup G))
    (hH : H ∈ HOver G ((L ⊔ (T : Subgroup G) : Subgroup G) : Set G)) :
    (L.subgroupOf H).IsCComponent := by
  have hLH : L ≤ H := le_sup_left.trans hH.2
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.2
  have hHT : H ∈ HOver G (T : Set G) := ⟨hH.1, hTH⟩
  have hB : L.subgroupOf H ∈ Chapter1.L H ((T.subtype hTH) : Subgroup H) :=
    (mem_LIn_iff_subgroupOf hTH hLH).mp ⟨hLH, hL.1⟩
  have hc := lemma_1_2_4_containment_of_A_3_12 hContainment
    (uniqueness_local_quotient_sqtk hG hH.1) (T.subtype hTH) hB
  obtain ⟨K, ⟨hK, hLK⟩, _⟩ := (existsUnique_cComponentsIn_iff hLH).mp hc
  have he : K = L := hL.2 K ((lemma_1_2_6 T hHT).1 hK).2 hLK
  exact he ▸ hK.2

/-- All conclusions of Theorem 1.2.7 from universal containment,
normal-or-index-two orbits, and characteristic two. No component-model
classification is needed for this uniqueness deduction. The orbit assertion
is transported through the actual local quotient by its two-core. -/
theorem nonsolvable_uniqueness_of_orbit_inputs
    {κ : GroupClass.{u}}
    (hContainment : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK κ X → pCore 2 X = ⊥ → ∀ (S : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents S →
      ∃! K : Subgroup X, K.IsCComponent ∧ B ≤ K)
    (hOrbits : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK κ X → pCore 2 X = ⊥ → ∀ B : Subgroup X, B.IsCComponent →
        B.Normal ∨ (normalizer (B : Set X)).index = 2)
    (hCharacteristicTwo : ∀ (X : Type u) [Group X] [Finite X],
      IsSimpleQTKE κ X → ∀ S : Sylow 2 X, HOver X (S : Set X) ⊆ He X)
    (hG : IsSimpleQTKE κ G) (T : Sylow 2 G) {L : Subgroup G}
    (hL : L ∈ LStar G (T : Subgroup G)) : NonsolvableUniquenessConclusion T L := by
  let L₀ := componentOrbit L (T : Subgroup G)
  let J := L ⊔ (T : Subgroup G)
  have hchar : HasCharacteristicTwo J := mem_He_iff.mp
    (hCharacteristicTwo G hG T ⟨hL.1.2.2, fun x hx => (le_sup_right : (T : Subgroup G) ≤ J) hx⟩)
  have inherit (B : Subgroup G) (hBJ : B ≤ J) (hn : (B.subgroupOf J).IsSubnormal) :
      HasCharacteristicTwo B :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hBJ)).mp
      (subnormal_core_selfCentralizing hchar _ hn)
  have hF : generalizedFitting L = pCore 2 L :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2 (inherit L le_sup_left hL.1.1.subnormal)
  have hLne : L ≠ ⊥ := by
    intro he
    apply mem_L_not_isSolvable hL.1
    rw [he]
    infer_instance
  have hL0ne : L₀ ≠ ⊥ := fun he => hLne (bot_unique (he ▸ le_componentOrbit L _))
  have hc0 := inherit L₀ (componentOrbit_le_sup L _) (componentOrbit_normal_subgroupOf_sup L _).isSubnormal
  have hcore0 : pCore 2 L₀ ≠ ⊥ := by
    intro he
    have ht : (⊤ : Subgroup L₀) ≤ ⊥ := by
      intro x _
      rw [← he]
      apply hc0
      intro y hy
      have hy1 : y = 1 := mem_bot.mp (he ▸ hy)
      simp only [hy1, one_mul, mul_one]
    apply hL0ne
    apply bot_unique
    intro x hx
    exact congrArg Subtype.val (mem_bot.mp (ht (show (⟨x, hx⟩ : L₀) ∈ ⊤ from mem_top _)))
  have hnormal (H : Subgroup G)
      (hH : H ∈ HOver G ((L ⊔ (T : Subgroup G) : Subgroup G) : Set G)) :
      (L₀.subgroupOf H).Normal := by
    apply orbit_normal_in T (le_sup_left.trans hH.2) (le_sup_right.trans hH.2)
    have hB := component_in_eligible_overgroup hContainment hG hL hH
    let := pCore_isNilpotent (p := 2) (G := H)
    apply cComponent_normal_or_index_two_of_quotient hB (pCore 2 H)
    exact hOrbits _ (uniqueness_local_quotient_sqtk hG hH.1)
      (pCore_quotient_pCore_eq_bot 2) _ (hB.map_quotient _)
  have hT0 : (T : Subgroup G) ≤ normalizer (L₀ : Set G) := le_normalizer_componentOrbit L _
  obtain ⟨hmax, hset⟩ := unique_maximalTwoLocal_overgroup_of_normal L₀ (T : Subgroup G) hT0
    (exists_twoLocal_overgroup_normalizer L₀ (pCore 2 L₀) hcore0 pCore_isPGroup)
    (fun M hM hLM => hnormal M ⟨mem_H_of_isTwoLocal hM.1, by
      change L ⊔ (T : Subgroup G) ≤ M
      simpa only [L₀, componentOrbit_sup] using hLM⟩)
  have hu : ∀ M : Subgroup G, IsMaximalTwoLocal M → L₀ ⊔ (T : Subgroup G) ≤ M →
      M = normalizer (L₀ : Set G) := by
    intro M hM hLM
    have hm : M ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L₀ ⊔ (T : Subgroup G) ≤ N} := ⟨hM, hLM⟩
    rw [hset] at hm
    exact Set.mem_singleton_iff.mp hm
  have hproper : normalizer (L₀ : Set G) ≠ ⊤ := by
    let _ := hG.simple
    exact twoLocal_ne_top_of_nonabelian_simple hG.nonabelian hmax.1
  refine ⟨fun H hH => component_in_eligible_overgroup hContainment hG hL hH, hF, hmax,
    sup_le ((le_componentOrbit L _).trans L₀.le_normalizer) hT0, hproper, ?_, ?_⟩
  · intro M hM hLM
    exact hu M hM (by simpa only [L₀, componentOrbit_sup] using hLM)
  · intro g hg
    let Z := ((omega₁ (center T) (p := 2)).map (center T).subtype).map (T : Subgroup G).subtype
    have hZT : Z ≤ centralizer ((T : Subgroup G) : Set G) := by
      intro z hz
      obtain ⟨z', hz', rfl⟩ := mem_map.mp hz
      obtain ⟨z'', _, rfl⟩ := mem_map.mp hz'
      exact mem_centralizer_iff.mpr fun t ht =>
        congrArg Subtype.val (mem_center_iff.mp z''.property ⟨t, ht⟩)
    have hZ : ∀ z ∈ Z, z ^ 2 = 1 := by
      intro z hz
      obtain ⟨z', hz', rfl⟩ := mem_map.mp hz
      obtain ⟨z'', hz'', rfl⟩ := mem_map.mp hz'
      let _ : IsElementaryAbelian 2 (omega₁ (center T)) :=
        IsElementaryAbelian.omega₁_of_isMulCommutative _
      have hp : (z'' : center T) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian z'' hz''
      exact congrArg ((T : Subgroup G).subtype.comp (center T).subtype) hp
    apply inf_conjugate_eq_bot_of_unique_maximalTwoLocal
      (H := L₀ ⊔ (T : Subgroup G)) (Z := Z ⊓ centralizer (L₀ : Set G)) hmax hu
      (sup_le (le_centralizer_iff.mpr inf_le_right)
        (le_centralizer_iff.mpr (inf_le_left.trans hZT))) (fun z hz => hZ z hz.1) hg

/-- Complete deduction of Theorem 1.2.7 from the universal earlier results
A.3.12 (containment), A.3.8(3), and 1.1.4(6). All local quotient, normality,
core, properness and centralizer-intersection obligations are discharged here.
Instantiating the universal earlier theorems remains with the section owner. -/
theorem nonsolvable_uniqueness_of_earlier
    {κ : GroupClass.{u}} (earlier : UniquenessEarlierResults κ)
    (hG : IsSimpleQTKE κ G) (T : Sylow 2 G) {L : Subgroup G}
    (hL : L ∈ LStar G (T : Subgroup G)) : NonsolvableUniquenessConclusion T L := by
  apply nonsolvable_uniqueness_of_orbit_inputs earlier.containment
    (fun X _ _ hX hO B hB => (earlier.conjugates X hX hO B hB).imp_right And.left)
    earlier.characteristicTwo hG T hL

end CFSG.Quasithin.Chapter1.Section02
