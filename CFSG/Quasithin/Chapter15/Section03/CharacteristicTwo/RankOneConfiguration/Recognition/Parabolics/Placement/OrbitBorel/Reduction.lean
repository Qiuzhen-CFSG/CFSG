module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.Residual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.ThompsonAction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives
public import Theory.Quasithin.Rank

/-!
# The nonnormal component orbit in the rank-one branch

Simple QTKE in the ambient group and the nontrivial local two-core imply
SQTK for I and its two-core quotient. Transfer the selected C-component
from J(I) to I and apply the universal A.3.8 orbit theorem. Its normalizer
has index two. A Sylow two-subgroup cannot lie in that normalizer, and its
two cosets exhaust the component orbit. Source 1.2.2 then identifies the
S-span with the embedded prime-to-three residual; positive three-rank
verifies its divisibility premise after removing the two-core.

The actual subgroup Y₊ consequently lies in this span, is S-invariant and
solvable, and has Sylow three-subgroups of order three. The genuine
Thompson representation satisfies every FF hypothesis: its SQTK cover
comes from the ambient setup, and its nontriviality follows from the
outside component and the earlier action-kernel containment.

Only universal earlier source implications occur in EarlierOrbitResults
and CompleteClassificationInput. The specialized model comparison,
L₃(2) exclusion and L₂(2^n) Borel construction are not asserted here.
ComponentModelAlternatives specifies the remaining comparison using
actual isomorphisms for both the intrinsic quotient and star image.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 1.2.1(3)
and 1.2.2, printed pp.503–504; B.5.3/6, pp.104–105; 15.3.11/26/27,
pp.1123 and 1130–1131 (PDF pp.1140 and 1147–1148).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel
open Chapter1.Section02
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The precise universal source inputs A.3.8(3) and 1.2.2(a).
The latter retains the simple QTKE ambient setup, arbitrary odd prime,
relative orbit index, and the intrinsic two-core quotient. -/
structure EarlierOrbitResults (K : GroupClass.{u}) : Prop where
  conjugates : ∀ (X : Type u) [Group X] [Finite X],
    IsSQTK K X → pCore 2 X = ⊥ → ∀ B : Subgroup X, B.IsCComponent →
    B.Normal ∨ (normalizer (B : Set X)).index = 2 ∧ NonnormalCComponentModel B
  residual : ∀ (X : Type u) [Group X] [Finite X], IsSimpleQTKE K X →
    ∀ H : Subgroup X, H ∈ Chapter1.H X → ∀ B : Subgroup X, B ≤ H →
    (B.subgroupOf H).IsCComponent →
    (normalizer (B : Set X)).relIndex H = 2 →
    ∀ p : ℕ, p.Prime → Odd p → p ∣ Nat.card (B ⧸ pCore 2 B) →
    (primeToResidual p H).map H.subtype = localSpan B H

/-- Recover SQTK from the genuine ambient setup, by embedding I in the
two-local normalizer of its nontrivial two-core. -/
theorem local_sqtk {K : GroupClass.{u}} (hG : IsSimpleQTKE K G)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus) : IsSQTK K I := by
  let R := I.pCoreIn 2
  let N := normalizer (R : Set G)
  have hIN : I ≤ N := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hN : IsTwoLocal N := ⟨R, hI.1.1, isPGroup_pCoreIn 2 I, rfl⟩
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hIN)).mp
    ((hG.twoLocal_sqtk hN).subgroup (I.subgroupOf N))

/-- The quotient by O₂(I) remains SQTK: its odd-prime ranks do not increase. -/
theorem local_quotient_sqtk {K : GroupClass.{u}} (hG : IsSimpleQTKE K G)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus) :
    IsSQTK K (I ⧸ pCore 2 I) := by
  have h := local_sqtk hG d hI
  refine ⟨?_, h.isKGroup.quotient _⟩
  intro p hp ho
  let _ : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (h.stronglyQuasithin p hp ho)

/-- Relative nonnormality selects the index-two alternative of 1.2.1(3).
The actual quotient model is transported through the subgroup equivalence. -/
theorem component_orbit_index_and_model {K : GroupClass.{u}}
    (earlier : EarlierOrbitResults K) (hG : IsSimpleQTKE K G)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hn : ¬ (c.L.subgroupOf I).Normal) :
    (normalizer (c.L : Set G)).relIndex I = 2 ∧
      NonnormalCComponentModel (c.L ⧸ pCore 2 c.L) := by
  have hc := LocalData.thompson_component_in c.le_thompson c.component
  obtain ⟨hi, hm⟩ := (proposition_1_2_1_three_index_of_A_3_8
    earlier.conjugates (local_quotient_sqtk hG d hI) hc).resolve_left hn
  refine ⟨?_, ?_⟩
  · rw [← subgroupOf_normalizer_eq (component_le c)] at hi
    exact hi
  · let e := (subgroupOfEquivOfLe (component_le c)).symm
    exact hm.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))

/-- The Sylow two-subgroup moves the component, since its index is odd
while the component normalizer has index two. -/
theorem component_moved_by_sylow (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hi : (normalizer (c.L : Set G)).relIndex I = 2) :
    c.L < localSpan c.L d.S := by
  apply lt_of_le_of_ne (le_conjugateSpanBy c.L d.S)
  intro he
  have hn : d.S ≤ normalizer (c.L : Set G) :=
    he ▸ le_normalizer_conjugateSpanBy c.L d.S
  obtain ⟨P, hP⟩ := hS
  have hPN : (P : Subgroup I) ≤ (normalizer (c.L : Set G)).subgroupOf I := by
    intro x hx
    exact hn (hP ▸ mem_map_of_mem I.subtype hx)
  have hd := index_dvd_of_le hPN
  change (normalizer (c.L : Set G)).relIndex I ∣ _ at hd
  rw [hi] at hd
  exact P.not_dvd_index hd

/-- Positive three-rank survives at the level of order divisibility
after removing the two-core, as required by 1.2.2(a). -/
theorem component_three_divides_quotient (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) : 3 ∣ Nat.card (c.L ⧸ pCore 2 c.L) := by
  have hd : 3 ∣ Nat.card c.L := by
    by_contra hn
    have hz : primeRank 3 c.L = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr hn
    have hp := c.rank_pos
    omega
  have hcop : Nat.Coprime 3 (Nat.card (pCore 2 c.L)) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := c.L)).exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 c.L)] at hd
  exact (Nat.prime_three.dvd_mul.mp hd).resolve_right
    (Nat.prime_three.coprime_iff_not_dvd.mp hcop)

/-- Apply 1.2.2(a) at p = 3 and identify its I-span with the source S-span.
This is O^{3′}, not the two-residual or the three-prime core. -/
theorem component_orbit_residual {K : GroupClass.{u}}
    (earlier : EarlierOrbitResults K) (hG : IsSimpleQTKE K G)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hn : ¬ (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I) :
    (primeToResidual 3 I).map I.subtype = localSpan c.L d.S := by
  have hi := (component_orbit_index_and_model earlier hG d hI c hn).1
  have he := Candidates.localSpan_eq_of_nontrivial_orbit
    (Chapter1.isSylowIn_iff.mp hS).2.1 (component_moved_by_sylow d c hS hi) hi.le
  exact (earlier.residual G hG I hI.1.1 c.L (component_le c)
    (LocalData.thompson_component_in c.le_thompson c.component) hi 3 Nat.prime_three
    (by decide) (component_three_divides_quotient d c)).trans he

/-- The actual conjugacy family inside I has exactly two elements. -/
theorem component_orbit_card {K : GroupClass.{u}}
    (earlier : EarlierOrbitResults K) (hG : IsSimpleQTKE K G)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hn : ¬ (c.L.subgroupOf I).Normal) :
    (Set.range fun i : I => (c.L.subgroupOf I).map
      (MulAut.conj i).toMonoidHom).ncard = 2 := by
  rw [ncard_conjugates_eq_index_normalizer,
    ← subgroupOf_normalizer_eq (component_le c)]
  exact (component_orbit_index_and_model earlier hG d hI c hn).1

/-- Every I-conjugate is an S-conjugate. The proof constructs representatives
using the two cosets of the relative component normalizer. -/
theorem component_orbit_exhausted_by_sylow (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hi : (normalizer (c.L : Set G)).relIndex I = 2) :
    (Set.range fun i : I => c.L.map (MulAut.conj (i : G)).toMonoidHom) =
      (Set.range fun s : d.S => c.L.map (MulAut.conj (s : G)).toMonoidHom) := by
  classical
  have hSI : d.S ≤ I := (Chapter1.isSylowIn_iff.mp hS).2.1
  have hs : ∃ s ∈ d.S, s ∉ normalizer (c.L : Set G) := by
    by_contra! hn
    exact (component_moved_by_sylow d c hS hi).not_ge (conjugateSpanBy_le le_rfl hn)
  obtain ⟨s, hs, hsN⟩ := hs
  apply Set.Subset.antisymm
  · rintro B ⟨i, rfl⟩
    by_cases hiN : (i : G) ∈ normalizer (c.L : Set G)
    · refine ⟨1, ?_⟩
      change c.L.map (MulAut.conj (1 : G)).toMonoidHom = _
      have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
        ext x
        simp
      rw [hid, map_id]
      exact (mem_normalizer_iff_map_conj_eq.mp hiN).symm
    · let N := (normalizer (c.L : Set G)).subgroupOf I
      have hn : s⁻¹ * (i : G) ∈ normalizer (c.L : Set G) := by
        have hs' : (⟨s, hSI hs⟩ : I)⁻¹ ∉ N := by
          simpa only [inv_mem_iff] using
            (show (⟨s, hSI hs⟩ : I) ∉ N from hsN)
        exact (N.mul_mem_iff_of_index_two hi).mpr (iff_of_false hs' hiN)
      refine ⟨⟨s, hs⟩, ?_⟩
      have he : c.L.map (MulAut.conj (s⁻¹ * (i : G))).toMonoidHom = c.L :=
        mem_normalizer_iff_map_conj_eq.mp hn
      calc
        c.L.map (MulAut.conj s).toMonoidHom =
            (c.L.map (MulAut.conj (s⁻¹ * (i : G))).toMonoidHom).map
              (MulAut.conj s).toMonoidHom := by rw [he]
        _ = c.L.map (MulAut.conj (i : G)).toMonoidHom := by
          rw [map_map]
          congr 1
          ext x
          simp [MulAut.conj_apply, mul_assoc]
  · rintro B ⟨s, rfl⟩
    exact ⟨⟨s, hSI s.property⟩, rfl⟩

/-- The residual identity of 15.3.26(1) places Y₊ in the constructed orbit span. -/
theorem orbit_contains_yplus {K : GroupClass.{u}}
    (earlier : EarlierOrbitResults K) (hG : IsSimpleQTKE K G)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hn : ¬ (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I) (h : RankOneFacts d I) :
    d.Yplus ≤ localSpan c.L d.S :=
  yplus_le_orbit_of_residual d c h (component_orbit_residual earlier hG d hI c hn hS)

/-- The orbit span is contained in I and normal relative to I. -/
theorem orbit_normal_and_le (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hi : (normalizer (c.L : Set G)).relIndex I = 2) :
    localSpan c.L d.S ≤ I ∧ ((localSpan c.L d.S).subgroupOf I).Normal := by
  have hSI := (Chapter1.isSylowIn_iff.mp hS).2.1
  have he := Candidates.localSpan_eq_of_nontrivial_orbit hSI
    (component_moved_by_sylow d c hS hi) hi.le
  rw [← he]
  exact ⟨conjugateSpanBy_le_self (component_le c),
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy c.L I)⟩

omit [Finite G] in
/-- The escaping component forces its Thompson image outside M_I*.
The required preimage calculation uses precisely 15.3.11(2). -/
theorem thompsonStar_not_le_intersection (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (hC : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I) :
    ¬ d.thompsonStar I ≤ d.starImage I d.M := by
  intro hJ
  have hL : d.starImage I c.L ≤ d.starImage I d.M :=
    (map_mono (comap_mono c.le_thompson)).trans hJ
  have hker : (d.starMap I).ker ≤ d.M.subgroupOf I := by
    rw [show (d.starMap I).ker = localActionKernel d.Z I from QuotientGroup.ker_mk' _]
    exact fun x hx => (hC ⟨x.property, hx⟩).1
  have hle := map_le_iff_le_comap.mp hL
  change c.L.subgroupOf I ≤ ((d.M.subgroupOf I).map (d.starMap I)).comap
    (d.starMap I) at hle
  rw [comap_map_eq, sup_eq_left.mpr hker] at hle
  apply c.outside
  intro l hl
  exact hle (show (⟨l, component_le c hl⟩ : I) ∈ c.L.subgroupOf I from hl)

/-- Construct both the complete B.5.3 hypothesis and a nontrivial FF witness
for the actual Thompson action. Elementary abelianness follows from
characteristic two and the source Sylow arrangement. -/
theorem thompson_ff_of_ambient {K : GroupClass.{u}}
    (hG : IsSimpleQTKE K G) (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hVT : d.V ≤ (d.T : Subgroup G))
    (hC : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I) :
    let _ := d.UI_subgroupOf_elementary hS (d.Z_le_S hVT) hf
    let ρ := d.thompsonStarAction I ((d.Z_le_S hVT).trans (le_sup_right.trans hI.1.2))
    FFHypothesis K ρ ∧ Representation.BinaryOffender.IsFFModule ρ := by
  let _ := d.UI_subgroupOf_elementary hS (d.Z_le_S hVT) hf
  exact ⟨d.thompsonStarFFHypothesis (local_sqtk hG d hI) _ hS (d.Z_le_S hVT),
    d.thompsonStarAction_isFFModule I _ (thompsonStar_not_le_intersection d c hC)⟩

omit [Finite G] in
/-- The literal prime-to-three residual is characteristic in M_I;
hence M_I normalizes Y₊. -/
theorem yplus_normalized_by_intersection (d : LocalData G) {I : Subgroup G}
    (h : RankOneFacts d I) : d.MI I ≤ normalizer (d.Yplus : Set G) := by
  rw [h.residual]
  exact (d.MI I).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (d.MI I) (primeToResidual 3 (d.MI I)))

/-- The actual S₃ shadow and its two-group kernel make Y₊S solvable. -/
theorem yplus_join_solvable (d : LocalData G) {I : Subgroup G}
    (h : RankOneFacts d I) : Group.IsSolvable (d.Yplus ⊔ d.S : Subgroup G) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  have hs : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  let := hs
  obtain ⟨e⟩ := h.shadow
  let : Group.IsSolvable ((d.Yplus ⊔ d.S : Subgroup G) ⧸
      pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsNilpotent (pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient
    (pCore 2 (d.Yplus ⊔ d.S : Subgroup G))).mpr ⟨inferInstance, inferInstance⟩

/-- Every subgroup between Y₊ and M_I has Sylow three-subgroups of
order exactly three. Rank one supplies divisibility; the shadow supplies
the upper bound. -/
theorem intersection_overgroup_sylow_three_card (d : LocalData G)
    {I H : Subgroup G} (h : RankOneFacts d I) (hr : primeRank 3 d.Yplus = 1)
    (hYH : d.Yplus ≤ H) (hHM : H ≤ d.MI I) (P : Sylow 3 H) : Nat.card P = 3 := by
  have hYP : 3 ∣ Nat.card d.Yplus := by
    by_contra hn
    have hz : primeRank 3 d.Yplus = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr hn
    omega
  have hP := P.dvd_card_of_dvd_card
    (hYP.trans (card_dvd_of_injective (inclusion hYH) (inclusion_injective hYH)))
  have hbound := three_subgroup_card_le_three d h ((map_subtype_le (P : Subgroup H)).trans hHM)
    (P.isPGroup'.map H.subtype)
  rw [card_map_of_injective H.subtype_injective] at hbound
  exact le_antisymm hbound (Nat.le_of_dvd (Nat.card_pos) hP)

/-- Construct the S-invariant solvable subgroup of the orbit span used
in the L₃(2) exclusion. Its Sylow three-order is proved, not assumed. -/
theorem yplus_invariant_three_subgroup {K : GroupClass.{u}}
    (earlier : EarlierOrbitResults K) (hG : IsSimpleQTKE K G)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hn : ¬ (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I) (h : RankOneFacts d I)
    (hr : primeRank 3 d.Yplus = 1) :
    d.Yplus ≤ localSpan c.L d.S ∧ d.S ≤ normalizer (d.Yplus : Set G) ∧
      Group.IsSolvable d.Yplus ∧ ∀ P : Sylow 3 d.Yplus, Nat.card P = 3 := by
  have hSM : d.S ≤ d.MI I :=
    le_inf (inf_le_left.trans d.sylow_le) (le_sup_right.trans hI.1.2)
  have hYM : d.Yplus ≤ d.MI I := h.residual ▸ map_subtype_le _
  let _ := yplus_join_solvable d h
  exact ⟨orbit_contains_yplus earlier hG d hI c hn hS h,
    hSM.trans (yplus_normalized_by_intersection d h),
    Group.isSolvable_of_isSolvable_injective
      (inclusion_injective (show d.Yplus ≤ d.Yplus ⊔ d.S from le_sup_left)),
    intersection_overgroup_sylow_three_card d h hr le_rfl hYM⟩

/-- The actual model alternatives still to be constructed by the comparison
of 1.2.1(3) and B.5.6. Both quotient conventions retain genuine isomorphisms. -/
def ComponentModelAlternatives (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSL (c.L ⧸ pCore 2 c.L) 2 (2 ^ n) ∧
    ClassicalGroup.IsPSL (d.starImage I c.L) 2 (2 ^ n)) ∨
  (ClassicalGroup.IsPSL (c.L ⧸ pCore 2 c.L) 3 2 ∧
    ClassicalGroup.IsPSL (d.starImage I c.L) 3 2)

/-- Apply the universal complete B.5.6 implication to the actual faithful
Thompson representation after verifying its source hypotheses. -/
theorem thompson_classification_of_ambient {K : GroupClass.{u}}
    (classification : FFAlternatives.CompleteClassificationInput.{u,u} K)
    (hG : IsSimpleQTKE K G) (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hVT : d.V ≤ (d.T : Subgroup G)) :
    let _ := d.UI_subgroupOf_elementary hS (d.Z_le_S hVT) hf
    FFAlternatives.SourceAlternative
      (d.thompsonStarAction I ((d.Z_le_S hVT).trans (le_sup_right.trans hI.1.2))) := by
  let _ := d.UI_subgroupOf_elementary hS (d.Z_le_S hVT) hf
  exact d.thompsonStar_sourceAlternative classification (local_sqtk hG d hI)
    _ hS (d.Z_le_S hVT)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel
