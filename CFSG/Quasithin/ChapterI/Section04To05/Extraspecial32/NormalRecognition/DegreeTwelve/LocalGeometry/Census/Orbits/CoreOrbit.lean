module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.LocalData
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Fusion.Count
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Fusion.Count.LocalOrbit

/-!
# The complementary twelve-element core orbit

The quaternion factors identify the nonzero singular central cosets with a
three-by-three grid. The checked local action has a three-element orbit;
its complement has six elements and is one orbit. Each noncentral coset
lifts to two inner conjugates. The common-centralizer candidate theorem
and the fusion-eight hypothesis identify these twelve lifts with the literal
involutions of the core outside the fusion subgroup.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), 31–47, Lemmas 2.3(2)(b) and 2.7(1)–(2).
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.Census
open Subgroup Theory.GroupTheory FusionCount.LocalOrbit
variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem center_mem_iff (h : Hypotheses z) (x : Core z) :
    x ∈ center (Core z) ↔ ((x : Centralizer z) : G) = 1 ∨
      ((x : Centralizer z) : G) = z := by
  classical
  constructor
  · intro hx
    have hm := mem_map_of_mem (Core z).subtype hx
    rw [h.core_center_image, mem_zpowers_iff_mem_range_orderOf, h.distinguished_order] at hm
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · exact Or.inl (by simpa using congrArg (fun a : Centralizer z => (a : G)) he.symm)
    · have hz : (x : Centralizer z) = distinguished z := by
        simpa only [pow_one, Subgroup.subtype_apply] using he.symm
      exact Or.inr (congrArg (fun a : Centralizer z => (a : G)) hz)
  · rintro (hx | hx)
    · have he : x = 1 := Subtype.ext (Subtype.ext hx)
      rw [he]
      exact (center (Core z)).one_mem
    · have hm : (x : Centralizer z) ∈ (center (Core z)).map (Core z).subtype := by
        rw [h.core_center_image, show (x : Centralizer z) = distinguished z from Subtype.ext hx]
        exact mem_zpowers _
      obtain ⟨y, hy, he⟩ := hm
      exact (Subtype.ext he : y = x) ▸ hy

private theorem candidate_mem_fusion (h : Hypotheses z) (hn : QuaternionSubgroupsNormal z)
    {x : G} (hx : x ∈ FusionCount.countCandidates z) : x ∈ fusionCore z := by
  apply Subgroup.subset_closure
  rw [h.fusion_set_eq_insert_countCandidates_of_transitive
    (h.countCandidates_transitive_of_quaternion_normal hn)]
  exact Set.mem_insert_of_mem z hx

private theorem points_card (h : Hypotheses z) :
    Nat.card (CentralInvolutionCosets (Core z)) = 9 := by
  obtain ⟨d⟩ := h.quaternionCentralProduct
  rw [← Nat.card_congr d.singularProduct, Nat.card_prod,
    d.factorPoints_card d.left (Or.inl rfl), d.factorPoints_card d.right (Or.inr rfl)]

private theorem complement_card (h : Hypotheses z)
    (S : Set (CentralInvolutionCosets (Core z))) (hS : S.ncard = 3) : Sᶜ.ncard = 6 := by
  rw [show Sᶜ = Set.univ \ S by ext; simp,
    Set.ncard_sdiff (Set.subset_univ _), Set.ncard_univ, points_card h, hS]

private theorem long_orbit_eq_compl (h : Hypotheses z)
    (S : Set (CentralInvolutionCosets (Core z))) (hS : S.ncard = 3)
    (hs : ∀ v ∈ S, cosetOrbit z v = S)
    (ho : ∀ v ∉ S, (cosetOrbit z v).ncard = 6)
    (v : CentralInvolutionCosets (Core z)) (hv : v ∉ S) :
    cosetOrbit z v = Sᶜ := by
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
  · rintro w ⟨a, rfl⟩ hw
    apply hv
    rw [← hs _ hw]
    refine ⟨a⁻¹, ?_⟩
    change (cosetAction z a⁻¹ * cosetAction z a) v = v
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  · rw [complement_card h S hS, ho v hv]

private theorem coreSecond_eq_image (h : Hypotheses z) (d : FusionEightData z)
    (hn : QuaternionSubgroupsNormal z)
    (S : Set (CentralInvolutionCosets (Core z))) (hS : S.ncard = 3)
    (hs : ∀ v ∈ S, cosetOrbit z v = S)
    (ho : ∀ v ∉ S, (cosetOrbit z v).ncard = 6) :
    {x : G | x ∈ coreInG z ∧ orderOf x = 2 ∧ x ∉ fusionCore z} =
      (fun x : Core z => ((x : Centralizer z) : G)) '' liftCosets z Sᶜ := by
  obtain ⟨q⟩ := h.quaternionCentralProduct
  have hp : CosetProfile z := ⟨S, hS, hs, ho⟩
  ext y
  constructor
  · rintro ⟨hyQ, hy2, hyF⟩
    obtain ⟨b, hb, rfl⟩ := hyQ
    let x : Core z := ⟨b, hb⟩
    have hx2 : x ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact hy2 ▸ pow_orderOf_eq_one (b : G)
    have hxZ : x ∉ center (Core z) := by
      intro hz
      rcases (center_mem_iff h x).mp hz with h1 | hz
      · exact hyF (by change ((x : Centralizer z) : G) ∈ fusionCore z; rw [h1]; exact (fusionCore z).one_mem)
      · exact hyF (by change ((x : Centralizer z) : G) ∈ fusionCore z; rw [hz]; exact h.involution_mem_fusionCore)
    let v := centralInvolutionCoset x hx2 hxZ
    have hv : v ∉ S := by
      intro hv
      apply hyF
      apply candidate_mem_fusion h hn
      apply (mem_countCandidates_iff_cosetOrbit_card h hp x hx2 hxZ).mpr
      rw [show centralInvolutionCoset x hx2 hxZ = v from rfl, hs v hv, hS]
    exact ⟨x, ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨v, hv, he⟩, rfl⟩
    have hxZ : x ∉ center (Core z) := by
      intro hz
      exact v.property.1 (he.symm.trans ((QuotientGroup.eq_one_iff x).mpr hz))
    obtain ⟨b, hb, hbe⟩ := v.property.2
    have hx2 : x^2 = 1 := (q.square_eq_of_quotient_eq x b (he.trans hbe.symm)).trans hb
    have hc := not_or.mp (mt (center_mem_iff h x).mpr hxZ)
    have hxord : orderOf ((x : Centralizer z) : G) = 2 :=
      orderOf_eq_prime (congrArg (fun x : Core z => ((x : Centralizer z) : G)) hx2) hc.1
    refine ⟨⟨x, x.property, rfl⟩, hxord, ?_⟩
    intro hxF
    have hmem := h.mem_countCandidates_of_isConj (fusionCore_le z hxF)
      (d.fusion _ hxF hc.1) hc.2
    have hcard := (mem_countCandidates_iff_cosetOrbit_card h hp x hx2 hxZ).mp hmem
    rw [show centralInvolutionCoset x hx2 hxZ = v from Subtype.ext he, ho v hv] at hcard
    omega

/-- The literal long core orbit has twelve elements and is transitive under H. -/
public theorem core_orbit_of_quaternion_normal (h : Hypotheses z) (hn : QuaternionSubgroupsNormal z)
    (d : FusionEightData z) :
    Nat.card (CoreSecond z) = 12 ∧
      ∀ x y : CoreSecond z, ∃ c : Centralizer z,
        MulAut.conj (c : G) (x : G) = (y : G) := by
  obtain ⟨S, hS, hs, ho⟩ := h.localOrbit_cosetProfile_of_quaternion_normal hn
  have he := coreSecond_eq_image h d hn S hS hs ho
  constructor
  · change ({x : G | x ∈ coreInG z ∧ orderOf x = 2 ∧ x ∉ fusionCore z} : Set G).ncard = 12
    rw [he, Set.ncard_image_of_injective _ (fun x y he => Subtype.ext (Subtype.ext he)),
      liftCosets_card h, complement_card h S hS]
  · intro x y
    have hx : (x : G) ∈ (fun x : Core z => ((x : Centralizer z) : G)) '' liftCosets z Sᶜ :=
      he ▸ x.property
    have hy : (y : G) ∈ (fun x : Core z => ((x : Centralizer z) : G)) '' liftCosets z Sᶜ :=
      he ▸ y.property
    obtain ⟨xx, ⟨v, hv, hex⟩, hxx⟩ := hx
    obtain ⟨yy, ⟨w, hw, hey⟩, hyy⟩ := hy
    obtain ⟨q⟩ := h.quaternionCentralProduct
    have hxxZ : xx ∉ center (Core z) := by
      intro hz
      exact v.property.1 (hex.symm.trans ((QuotientGroup.eq_one_iff xx).mpr hz))
    obtain ⟨b, hb, hbe⟩ := v.property.2
    have hxx2 : xx^2 = 1 := (q.square_eq_of_quotient_eq xx b (hex.trans hbe.symm)).trans hb
    have hmem : yy ∈ elementOrbit z xx := by
      rw [elementOrbit_eq_liftCosets h xx hxx2 hxxZ,
        show centralInvolutionCoset xx hxx2 hxxZ = v from Subtype.ext hex,
        long_orbit_eq_compl h S hS hs ho v hv]
      exact ⟨w, hw, hey⟩
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, ?_⟩
    rw [← hxx, ← hyy]
    exact congrArg (fun x : Core z => ((x : Centralizer z) : G)) hc
end CFSG.Quasithin.Extraspecial32.DegreeTwelve.Census
