module

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RudvalisNormalizer
public import Theory.GroupTheory.MovedCentralImageAction
public import Theory.AtlasPort.LinearGroups.G2.OrderChecks

/-!
# Sizes of the original Rudvalis normalizer and its point stabilizers

The central quotient is faithful on the whole source module. Full movement
reflects normalization through this quotient. Its conjugation image embeds
in the original ambient module automizer, which embeds in the natural G₂(2).
The previously identified E64 kernel therefore bounds the normalizer index
over the original residual by two. Orbit--stabilizer computes every point
stabilizer with the same index, retaining the original quotient marking.

The final theorem supplies these sizes in the actual escaping odd-actor pair.
Selecting index two, constructing the flag/quaternion intersection, excluding
J4 and discharging odd-normalizer control remain with qt-d-13316-source.
The earlier Structural1222 input retains final discharge with qt-theorem-d.
Source: Aschbacher--Smith 4.2.13 and 4.4.5--6, pp.611--612,620.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem unitary_automizer_card_dvd (s : Context T L V) :
    Nat.card (Automizer V) ∣ 12096 := by
  let I := inducedAutomizer V L
  obtain ⟨_,hNL⟩ := unitary_original_module_normalizers s.hypothesis s.maximal
    s.quotient s.chosen s.structural
  let : (L.subgroupOf (normalizer (V : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer s.chosen.normalizes).mpr hNL
  let : I.Normal := Subgroup.Normal.map inferInstance V.normalizerMonoidHom.rangeRestrict
    V.normalizerMonoidHom.rangeRestrict_surjective
  obtain ⟨j,hj,_,_⟩ := Atlas.G2.Natural.BinaryNormalizer.ambient_embedding
    (automizerRepresentation V) I s.actor s.coordinates s.equivariant
    (automizerRepresentation_injective V)
  have hd := card_dvd_of_injective j hj
  rwa [Atlas.G2.OrderChecks.binary_order] at hd

/-- The literal Rudvalis normalizer has at most the full G₂(2) action,
so its order is either 64·6048 or 64·12096. -/
theorem unitary_original_pushingUp_rudvalis_normalizer_sizes (s : Context T L V)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Rudvalis.Model)
    (c : sectionCentralizerIn (normalizer (L : Set G)) L)
    (hVW : V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let B := ((Y.subgroupOf H).subgroupOf K).map f
    let E := ((W.subgroupOf H).subgroupOf K).map f
    let N := normalizer (B : Set Rudvalis.Model)
    ∃ n : ℕ, (n = 1 ∨ n = 2) ∧ Nat.card N = 64 * 6048 * n ∧
      ∀ z : E, z ≠ 1 →
        Nat.card ((centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf N) =
          6144 * n := by
  let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let A := (Y.subgroupOf H).subgroupOf K
  let U := (W.subgroupOf H).subgroupOf K
  let C0 := ((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K
  let B := A.map f
  let E := U.map f
  let C := C0.map f
  have hfull := unitary_original_pushingUp_rudvalis_full_module s hcover hJH hc K hK e c hVW
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  have hM := h12.source_normalizer_maximal_unique s.structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer s.chosen.sylow_normalizes_component,hM.2⟩
  obtain ⟨hn,a,_⟩ := source_intersection_quotient h12.toHypothesis1221 hu hcover hJH
  have hYN := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp hn
  have hspan : conjugateSpanBy Y (H ⊓ normalizer (L : Set G)) = Y := hc.normalized_span_eq hYN
  have hYH : Y ≤ H := hc.component_le.trans hc.local_le
  have hYK : Y.subgroupOf H ≤ K := hc.ordinary_component_contains_original K hK
  have hWY : W ≤ Y := hc.module_le.trans hspan.le
  have hWH : W ≤ H := hWY.trans hYH
  have hWK : W.subgroupOf H ≤ K := (subgroupOf_mono H hWY).trans hYK
  have hm : U = ⁅U,A⁆ := by
    apply map_injective K.subtype_injective
    apply map_injective H.subtype_injective
    rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le hWK,
      map_subgroupOf_eq_of_le hYK,map_subgroupOf_eq_of_le hWH,
      map_subgroupOf_eq_of_le hYH]
    exact hc.module_commutator.trans (congrArg (fun X => ⁅W,X⁆) hspan)
  obtain ⟨hNC,hcore,hcent⟩ := unitary_original_pushingUp_rudvalis_normalizer
    s hcover hJH hc K hK e c hVW
  change normalizer (B : Set Rudvalis.Model) = C at hNC
  change C.pCoreIn 2 = E at hcore
  change C ⊓ centralizer (E : Set Rudvalis.Model) = E at hcent
  have hCE : C ≤ normalizer (E : Set Rudvalis.Model) := by
    rw [←hcore]
    exact C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hCA : C0 ≤ normalizer (A : Set K) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp (hYN hx) (y : G)
  have hk : f.ker ≤ center K := by
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mp
    exact e.injective (hx.trans (map_one e).symm)
  have hCU : C0 ≤ normalizer (U : Set K) :=
    normalizes_moved_of_central_image f U A C0 hk hm hCA hCE
  have hf : Function.Injective (f.comp U.subtype) := by
    have hi := (unitary_original_pushingUp_chosen_injective s hcover hJH hc K hK c hVW).1
    rw [←hfull] at hi
    exact e.injective.comp hi
  let α := E.normalizerMonoidHom.comp (inclusion hCE)
  have hα : Nat.card α.range ∣ Nat.card U.normalizerMonoidHom.range :=
    card_mapped_conjugation_range_dvd_automizer f U C0 hCU hf hCE
  let k : K →* G := H.subtype.comp K.subtype
  have hki : Function.Injective k := H.subtype_injective.comp K.subtype_injective
  obtain ⟨j,hj⟩ := U.exists_injective_automizer_map k hki
  have hUW : U.map k = W := by
    rw [←map_map,map_subgroupOf_eq_of_le hWK,map_subgroupOf_eq_of_le hWH]
  have hd : Nat.card U.normalizerMonoidHom.range ∣ Nat.card (Automizer W) := by
    have hd := card_dvd_of_injective j hj
    rwa [hUW] at hd
  have hWV : Nat.card (Automizer W) = Nat.card (Automizer V) := by
    rw [hfull]
    exact (Nat.card_congr (automizerMapEquiv V (MulAut.conj (c : G))).toEquiv).symm
  have hbound : Nat.card α.range ∣ 12096 := by
    rw [hWV] at hd
    exact (hα.trans hd).trans (unitary_automizer_card_dvd s)
  have hker : α.ker = E.subgroupOf C := by
    ext x
    change α x = 1 ↔ (x : Rudvalis.Model) ∈ E
    change inclusion hCE x ∈ E.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    change (x : Rudvalis.Model) ∈ centralizer (E : Set Rudvalis.Model) ↔ _
    constructor
    · intro hx
      exact hcent ▸ (show (x : Rudvalis.Model) ∈ C ⊓ centralizer (E : Set Rudvalis.Model) from
        ⟨x.property,hx⟩)
    · intro hx
      exact (show (x : Rudvalis.Model) ∈ C ⊓ centralizer (E : Set Rudvalis.Model) from hcent.symm ▸ hx).2
  have hE : Nat.card E = 64 := by
    dsimp only [E,f]
    rw [←map_map,card_map_of_injective e.injective]
    exact hc.unitary_ordinary_rudvalis_module_card (a.trans s.quotient) K hK e
  have hEC : E ≤ C := hcore ▸ pCoreIn_le 2 C
  have hkerCard : Nat.card α.ker = 64 := by
    rw [hker,Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv,hE]
  have hcard : Nat.card C = 64 * Nat.card α.range := by
    have hh := α.ker.card_mul_index
    rw [index_ker,hkerCard] at hh
    exact hh.symm
  have hdiv : Nat.card C ∣ 64 * 12096 := hcard ▸ Nat.mul_dvd_mul_left 64 hbound
  have hB : Nat.card B = 64 * 6048 :=
    (unitary_original_pushingUp_rudvalis_module_and_points s hcover hJH hc K hK e c hVW).2.1
  have hBC : B ≤ C := hNC ▸ B.le_normalizer
  obtain ⟨n,hn⟩ := hB ▸ card_dvd_of_le hBC
  have hn0 : n ≠ 0 := by
    intro he
    rw [he,mul_zero] at hn
    exact Nat.card_pos.ne' hn
  have hn2 : n ∣ 2 := by
    rw [hn] at hdiv
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 64*6048)).mp hdiv
  have hnle := Nat.le_of_dvd (by decide : 0 < 2) hn2
  have hnCases : n = 1 ∨ n = 2 := by omega
  refine ⟨n,hnCases,?_,?_⟩
  · change Nat.card (normalizer (B : Set Rudvalis.Model)) = _
    rw [hNC]
    exact hn
  · intro z hz
    have ht : ∀ x ∈ E, ∀ y ∈ E, x ≠ 1 → y ≠ 1 → ∃ b ∈ C, b*x*b⁻¹ = y := by
      intro x hx y hy hx1 hy1
      obtain ⟨u,hu,rfl⟩ := hx
      obtain ⟨v,hv,rfl⟩ := hy
      have hu1 : (u : G) ≠ 1 := by
        intro hh
        have hh' : u = 1 := K.subtype_injective (H.subtype_injective hh)
        exact hx1 (hh' ▸ map_one f)
      have hv1 : (v : G) ≠ 1 := by
        intro hh
        have hh' : v = 1 := K.subtype_injective (H.subtype_injective hh)
        exact hy1 (hh' ▸ map_one f)
      obtain ⟨l,hl,he⟩ := unitary_original_pushingUp_rudvalis_fusion s hcover hJH hc K hK e c hVW
        u hu v hv hu1 hv1
      let k : K := ⟨⟨l,hYH hl⟩,hYK hl⟩
      refine ⟨f k,hBC (mem_map_of_mem f (show k ∈ A from hl)),?_⟩
      have he' : k*u*k⁻¹ = v := K.subtype_injective (H.subtype_injective he)
      simpa only [map_mul,map_inv] using congrArg f he'
    have hh := Theory.GroupAction.centralizer_card_mul_pred_of_transitive C E hCE ht z hz
    rw [hE,hn] at hh
    change Nat.card ((centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf
      (normalizer (B : Set Rudvalis.Model))) = _
    rw [hNC]
    omega
/-- The actual escaping odd-actor pair, with the full local normalizer and
its module kernel and point-stabilizer sizes in the same Rudvalis marking. -/
theorem unitary_original_oddActorResidual_component_sizes (s : Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L))
      (c : sectionCentralizerIn (normalizer (L : Set G)) L),
      PushLE L (oddActorResidual L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      H ⊓ normalizer (L : Set G) < H ∧
      let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      let W := fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ normalizer (L : Set G))
        Y (J.pCoreIn 2) W ∧
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
        (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
      V.map (MulAut.conj (c : G)).toMonoidHom ≤ W ∧
      ∃ K : Subgroup H, IsComponent H K ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        (Nonempty (K ⧸ center K ≃* Janko4.Model) ∨
          ∃ e : K ⧸ center K ≃* Rudvalis.Model,
            W = V.map (MulAut.conj (c : G)).toMonoidHom ∧
            let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
            let B := ((Y.subgroupOf H).subgroupOf K).map f
            let E := ((W.subgroupOf H).subgroupOf K).map f
            let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
            normalizer (B : Set Rudvalis.Model) = C ∧
              C.pCoreIn 2 = E ∧ C ⊓ centralizer (E : Set Rudvalis.Model) = E ∧
              ∃ n : ℕ, (n = 1 ∨ n = 2) ∧ Nat.card C = 64 * 6048 * n ∧
                ∀ z : E, z ≠ 1 →
                  Nat.card ((centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf C) =
                    6144 * n) := by
  obtain ⟨J,H,S,hpush,hH,hJH,hlt,hc,_,_,⟨K,hK,hout,n,hn,⟨e⟩⟩,c,hcS,hcV⟩ :=
    unitary_original_oddActorResidual_escaping_component s A hAN hcomm hodd hAV hnot
  refine ⟨J,H,S,c,hpush,hH,hJH,hlt,hc,hcS,hcV,K,hK,hout,?_⟩
  rcases hn with rfl | rfl
  · exact Or.inl ⟨e⟩
  · apply Or.inr
    have hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G) := by
      have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
      obtain ⟨hcover,_,_,_⟩ := chosen_oddActorResidual_cover h12.toHypothesis1221 s.chosen
        A hAN hcomm hodd hAV
      have hi : oddActorResidual L A ≤ J :=
        ((le_inf le_rfl ((oddActorResidual_le L A).trans inf_le_left)).trans hpush.2).trans
          inf_le_left
      exact hcover.subset.trans (Set.mul_subset_mul hi Set.Subset.rfl)
    obtain ⟨hNC,hcore,hcentral⟩ := unitary_original_pushingUp_rudvalis_normalizer
      s hcover hJH hc K hK e c hcV
    have hsizes := unitary_original_pushingUp_rudvalis_normalizer_sizes
      s hcover hJH hc K hK e c hcV
    dsimp only at hsizes
    rw [hNC] at hsizes
    exact ⟨e,unitary_original_pushingUp_rudvalis_full_module s hcover hJH hc K hK e c hcV,
      hNC,hcore,hcentral,hsizes⟩
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
