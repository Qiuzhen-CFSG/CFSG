module

public import Stellmacher.Recognition.Parrott.NormalizerFusionFromLocalData
public import Stellmacher.Recognition.Parrott.LocalInputs
public import Stellmacher.Recognition.Parrott.NormalizerCoreSolvable
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreCenter
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreThreeFixed
public import Stellmacher.Recognition.Parrott.LocalNormalizer.ElementaryFusion
public import Stellmacher.Recognition.Parrott.LocalNormalizer.OuterFusion

/-!
# The actual second normalizer from local inputs

These calculations retain the supplied second elementary subgroup and Sylow.
The original derived-core normalizer identity and solvability of the actual
second normalizer replace the ambient N₂ assumption. All subgroup images,
centers, omega subgroups and conjugators are the original literal ones.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.677–678. This is the local-input extension of `NormalizerFusionFromLocalData`.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem involution_eq_of_mem_zpowers {v w : G}
    (hv : orderOf v = 2) (hw : orderOf w = 2) (hm : w ∈ zpowers v) : w = v := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hv] at hm
  obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hm
  have hnlt := Finset.mem_range.mp hn
  interval_cases n
  · have hw1 : w = 1 := by simpa using heq.symm
    simp [hw1] at hw
  · simpa using heq.symm

/-- Every involution in the original derived core is reached from z or the
prescribed fixed involution by a conjugator in the join of the two normalizers. -/
public theorem derived_involution_fusion_in_join_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let L := H ⊔ normalizer (d.F : Set G)
    ¬ IsConj z v ∧ ∀ u : G, u ∈ E → orderOf u = 2 →
      ∃ l : L, (l : G) * z * (l : G)⁻¹ = u ∨ (l : G) * v * (l : G)⁻¹ = u := by
  intro H J E L
  obtain ⟨t, w, ht, hw, _, hw2, htz, _, _, _, ⟨q, hq⟩, hwC, _, _, hnc⟩ :=
    d.exists_normalizer_three_fixed_generators_of_local_inputs h hlocal hproper Q
  have hwv : w = v := involution_eq_of_mem_zpowers hv hw2 (hfix ▸ ⟨hw.2, hwC⟩)
  subst w
  have hzt : IsConj z t := isConj_iff.mpr ⟨((q : normalizer (d.F : Set G)) : G), hq⟩
  have htv : ¬ IsConj t v := fun hh => hnc (hzt.trans hh)
  have hvz : v ∉ zpowers z := by
    intro hh
    have heq := involution_eq_of_mem_zpowers h.involution hv hh
    apply hnc
    rw [heq]
  refine ⟨hnc, ?_⟩
  intro u hu hu2
  by_cases huz : u ∈ zpowers z
  · have heq := involution_eq_of_mem_zpowers h.involution hu2 huz
    exact ⟨1, Or.inl (by simpa using heq.symm)⟩
  rcases derived_fusion_of_distinct_representatives h t v ht.1 htz hw.1 hvz htv
      u hu huz with ⟨a, ha⟩ | ⟨a, ha⟩
  · let qL : L := ⟨((q : normalizer (d.F : Set G)) : G),
      mem_sup_right (q : normalizer (d.F : Set G)).property⟩
    let aL : L := ⟨(a : G), mem_sup_left a.property⟩
    refine ⟨aL * qL, Or.inl ?_⟩
    change ((a : G) * ((q : normalizer (d.F : Set G)) : G)) * z *
      ((a : G) * ((q : normalizer (d.F : Set G)) : G))⁻¹ = u
    rw [mul_inv_rev]
    calc
      _ = (a : G) * (((q : normalizer (d.F : Set G)) : G) * z *
          ((q : normalizer (d.F : Set G)) : G)⁻¹) * (a : G)⁻¹ := by group
      _ = u := by rw [hq, ha]
  · exact ⟨⟨(a : G), mem_sup_left a.property⟩, Or.inr ha⟩

/-- The two remaining local branches suffice for both Sylow fusion with
conjugators in the join and the ambient two-class assertion. -/
public theorem involution_fusion_of_core_and_outer_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let L := H ⊔ normalizer (d.F : Set G)
    (∀ u : G, u ∈ J.map H.subtype → u ∉ E → orderOf u = 2 →
      ∃ l : L, (l : G) * v * (l : G)⁻¹ = u) →
    (∀ u : G, u ∈ (d.sylow : Subgroup G) → u ∉ J.map H.subtype → orderOf u = 2 →
      ∃ l : L, (l : G) * u * (l : G)⁻¹ ∈ E) →
    ¬ IsConj z v ∧
      (∀ u : G, u ∈ (d.sylow : Subgroup G) → orderOf u = 2 →
        ∃ l : L, (l : G) * z * (l : G)⁻¹ = u ∨ (l : G) * v * (l : G)⁻¹ = u) ∧
      (∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj v u) := by
  intro H J E L hcore houter
  obtain ⟨hnc, hderived⟩ := d.derived_involution_fusion_in_join_of_local_inputs h hlocal hproper Q v hv hfix
  have hfusion (u : G) (huT : u ∈ (d.sylow : Subgroup G)) (hu2 : orderOf u = 2) :
      ∃ l : L, (l : G) * z * (l : G)⁻¹ = u ∨ (l : G) * v * (l : G)⁻¹ = u := by
    by_cases huE : u ∈ E
    · exact hderived u huE hu2
    by_cases huJ : u ∈ J.map H.subtype
    · obtain ⟨l, hl⟩ := hcore u huJ huE hu2
      exact ⟨l, Or.inr hl⟩
    obtain ⟨a, ha⟩ := houter u huT huJ hu2
    have hau2 : orderOf ((a : G) * u * (a : G)⁻¹) = 2 :=
      ((MulAut.conj (a : G)).orderOf_eq u).trans hu2
    obtain ⟨b, hb | hb⟩ := hderived _ ha hau2
    · refine ⟨a⁻¹ * b, Or.inl ?_⟩
      change ((a : G)⁻¹ * (b : G)) * z * ((a : G)⁻¹ * (b : G))⁻¹ = u
      calc
        _ = (a : G)⁻¹ * ((b : G) * z * (b : G)⁻¹) * (a : G) := by group
        _ = u := by rw [hb]; group
    · refine ⟨a⁻¹ * b, Or.inr ?_⟩
      change ((a : G)⁻¹ * (b : G)) * v * ((a : G)⁻¹ * (b : G))⁻¹ = u
      calc
        _ = (a : G)⁻¹ * ((b : G) * v * (b : G)⁻¹) * (a : G) := by group
        _ = u := by rw [hb]; group
  exact ⟨hnc, hfusion, d.involution_classes_of_sylow_fusion v hfusion⟩



/-- Every core involution outside the derived core can be moved into the
supplied elementary subgroup, still outside the derived core, inside H. -/
public theorem core_involution_transport_to_elementary_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ u : G, u ∈ J.map H.subtype → u ∉ E → orderOf u = 2 →
      ∃ a : H, (a : G) * u * (a : G)⁻¹ ∈ d.F ∧
        (a : G) * u * (a : G)⁻¹ ∉ E := by
  intro H J E u hu huE hu2
  obtain ⟨uH, huJ, rfl⟩ := hu
  let DH := (commutator J).map J.subtype
  have huDH : uH ∉ DH := by
    intro hh
    apply huE
    have hm := mem_map_of_mem H.subtype hh
    rwa [map_map] at hm
  have huH2 : orderOf uH = 2 := (Subgroup.orderOf_coe uH).symm.trans hu2
  obtain ⟨e, he⟩ := parrott_second_elementary_of_core_involution z h uH huJ huH2 huDH
  have huF : (uH : G) ∈ e.F := by
    rw [e.fixed_join, he]
    exact mem_sup_left (mem_zpowers (uH : G))
  obtain ⟨a, ha⟩ := e.exists_conjugate_fixed_join d h
  have haN : (a : G) ∈ normalizer (E : Set G) := by
    rw [hlocal.derived_normalizer]
    exact a.property
  refine ⟨a, ?_, ?_⟩
  · rw [← ha]
    exact mem_map.mpr ⟨(uH : G), huF, rfl⟩
  · exact fun hh => huE ((mem_normalizer_iff.mp haN (uH : G)).mpr hh)

/-- Fusion of F outside the central four-group supplies the entire original
core branch. The inverse transporter keeps the resulting conjugator in the join. -/
public theorem core_involution_fusion_of_elementary_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) (v : G) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let ZK := (center K).map (N.subtype.comp K.subtype)
    let L := H ⊔ N
    (∀ u : G, u ∈ d.F → u ∉ ZK → orderOf u = 2 →
      ∃ l : L, (l : G) * v * (l : G)⁻¹ = u) →
    ∀ u : G, u ∈ J.map H.subtype → u ∉ E → orderOf u = 2 →
      ∃ l : L, (l : G) * v * (l : G)⁻¹ = u := by
  intro H J E N K ZK L hF u hu huE hu2
  obtain ⟨a, haF, haE⟩ := d.core_involution_transport_to_elementary_of_local_inputs h hlocal u hu huE hu2
  have haZ : (a : G) * u * (a : G)⁻¹ ∉ ZK :=
    fun hh => haE ((d.normalizer_core_center_le_inf_of_local_inputs h hlocal hproper hh).1)
  have ha2 : orderOf ((a : G) * u * (a : G)⁻¹) = 2 :=
    ((MulAut.conj (a : G)).orderOf_eq u).trans hu2
  obtain ⟨b, hb⟩ := hF _ haF haZ ha2
  let aL : L := ⟨(a : G), mem_sup_left a.property⟩
  refine ⟨aL⁻¹ * b, ?_⟩
  change ((a : G)⁻¹ * (b : G)) * v * ((a : G)⁻¹ * (b : G))⁻¹ = u
  calc
    _ = (a : G)⁻¹ * ((b : G) * v * (b : G)⁻¹) * (a : G) := by group
    _ = u := by rw [hb]; group

/-- Every involution of the original core outside its derived subgroup belongs
to the prescribed fixed involution's class, with a conjugator in H∨N. -/
public theorem core_involution_fusion_in_join_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    let L := H ⊔ N
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    ∀ u : G, u ∈ J.map H.subtype → u ∉ E → orderOf u = 2 →
      ∃ l : L, (l : G) * v * (l : G)⁻¹ = u := by
  intro H J E N X D A L hCD v hv hfix
  have hF := (d.normalizer_elementary_fusion_in_join_of_local_inputs h hlocal hproper Q hCD v hv hfix).2
  exact d.core_involution_fusion_of_elementary_of_local_inputs h hlocal hproper v
    (fun u hu huZ _ => hF u hu huZ)

/-- Parrott's two involution classes and finer local fusion for the supplied
normalizer data. The Sylow, elementary, and original-core assertions retain
actual conjugators in H∨N; Sylow conjugacy gives ambient completeness.
Normalizer growth and the derived-centralizer containment are the only local
inputs still to be discharged by the unconditional realization theorem. -/
public theorem normalizer_involution_fusion_from_local_data_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X := K.map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    let ZK := (center K).map (N.subtype.comp K.subtype)
    let L := H ⊔ N
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    ¬ IsConj z v ∧
      (∀ u : G, u ∈ (d.sylow : Subgroup G) → orderOf u = 2 →
        ∃ l : L, (l : G) * z * (l : G)⁻¹ = u ∨ (l : G) * v * (l : G)⁻¹ = u) ∧
      (∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj v u) ∧
      (∀ u : G, u ∈ ZK → orderOf u = 2 →
        ∃ l : L, (l : G) * z * (l : G)⁻¹ = u) ∧
      (∀ u : G, u ∈ d.F → u ∉ ZK →
        ∃ l : L, (l : G) * v * (l : G)⁻¹ = u) ∧
      (∀ u : G, u ∈ J.map H.subtype → u ∉ E → orderOf u = 2 →
        ∃ l : L, (l : G) * v * (l : G)⁻¹ = u) := by
  intro H J E N K X D A ZK L hCD v hv hfix
  have hcore := d.core_involution_fusion_in_join_of_local_inputs h hlocal hproper Q hCD v hv hfix
  obtain ⟨hnc, hSylow, hG⟩ := d.involution_fusion_of_core_and_outer_of_local_inputs h hlocal hproper Q v hv hfix
    hcore (d.outer_involution_transport_of_local_inputs h hlocal hproper Q hCD v hv hfix)
  obtain ⟨hZK, hF⟩ := d.normalizer_elementary_fusion_in_join_of_local_inputs h hlocal hproper Q hCD v hv hfix
  exact ⟨hnc, hSylow, hG, hZK, hF, hcore⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
