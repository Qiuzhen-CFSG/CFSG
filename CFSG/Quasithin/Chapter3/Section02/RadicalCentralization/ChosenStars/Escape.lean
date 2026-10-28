module
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ChosenStars.SinglePrime
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Residual
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Rigidity
public import Theory.GroupTheory.CComponent.OrbitNormalized
/-!
# The actual escaping component without a universal embedding catalogue

Known-simple containment constructs a relatively normal C-component above
N_L(O₂(Ξ_p(L)T))^∞ in the normalizer of a nontrivial characteristic subgroup.
Radical rigidity makes Ξ_p(L) nonnormal in that component. Apply the proved
adequate 1.3.4 inside its join with the full Sylow. Component-orbit exhaustion
eliminates the swapped case; the noncyclic automizer eliminates the other
large-prime case. The surviving component is (S)L₃(p).

This applies separately to every canonical radical contained in the same
component. `Normalizer.lean` uses it twice in the Thompson two-prime case.
No characteristic-normalizer control or universal A.3.12 input is assumed.
Source: Aschbacher--Smith, 1.2.4, 1.3.4 and 1.3.8, pp.505,509--513.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3.RadicalCentralization.ChosenStars
open Chapter1 Chapter1.Section02 Chapter1.RadicalNormalizers Chapter1.RadicalActions
open Chapter1.RadicalNormalizers.Embedding Chapter1.XiEmbedding Chapter1.RadicalExclusions
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original characteristic normalizer contains a normal component above the residual. -/
theorem exists_normal_component_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (C : Subgroup (radicalCore p L T)) [C.Characteristic] (hC : C ≠ ⊥) :
    let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
    ∃ K : Subgroup G, K ∈ cComponentsIn N ∧
      normalizerResidual L (radicalCore p L T) ≤ K ∧
      (K.subgroupOf N).Normal ∧ (T : Subgroup G) ≤ normalizer (K : Set G) := by
  let h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  have h38 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ → ∀ B : Subgroup A,
      B.IsCComponent → B.Normal ∨ IsQuasisimple B :=
    fun _ _ _ hA hO _ hB => ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hA hO hB
  have hr := residual_normalizer_data_of_source h36 h38 hL
    (uniqueness_local_quotient_sqtk hG hL.1.2.2) hn ho hd
  let R := radicalCore p L T
  let N := normalizer (C.map R.subtype : Set G)
  let Y := normalizerResidual L R
  have hRN : normalizer (R : Set G) ≤ N :=
    normalizer_le_normalizer_characteristic_image R C
  have hTN : (T : Subgroup G) ≤ N := (t_le_normalizer_radicalCore p L T).trans hRN
  have hYN : Y ≤ N := (normalizerResidual_le_normalizer L R).trans hRN
  let S : Sylow 2 N := T.subtype hTN
  have hYL : Y.subgroupOf N ∈ Chapter1.L N S := by
    change Y.subgroupOf N ∈ Chapter1.L N ((T : Subgroup G).subgroupOf N)
    exact (mem_LIn_iff_subgroupOf hTN hYN).mp ⟨hYN,hr.Y_mem_L⟩
  have hSY : (S : Subgroup N) ≤ normalizer (Y.subgroupOf N : Set N) := by
    rw [← subgroupOf_normalizer_eq hYN]
    exact comap_mono hr.t_normalizes_Y
  obtain ⟨K₀,⟨hK₀,hYK₀,hn₀⟩,_⟩ := lemma_1_2_4_containment_normality_source
    (characteristic_normalizer_quotient_sqtk hG p L T C hC) S hYL hSY
  have hKm : (K₀.map N.subtype).subgroupOf N = K₀ :=
    comap_map_eq_self_of_injective N.subtype_injective _
  have hnormal : ((K₀.map N.subtype).subgroupOf N).Normal := hKm.symm ▸ hn₀
  refine ⟨K₀.map N.subtype,⟨map_subtype_le _,hKm.symm ▸ hK₀⟩,?_,hnormal,?_⟩
  · simpa only [map_subgroupOf_eq_of_le hYN] using map_mono (f := N.subtype) hYK₀
  · exact hTN.trans ((normal_subgroupOf_iff_le_normalizer (map_subtype_le K₀)).mp hnormal)

/-- A normal containing component in an escaping local is an odd linear-three
model at the prime of every canonical radical it contains. -/
theorem escaping_component_shape
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    {N K : Subgroup G} (hN : IsTwoLocal N) (hTN : (T : Subgroup G) ≤ N)
    (hK : K ∈ cComponentsIn N) (hKn : (K.subgroupOf N).Normal)
    (hXK : XiP p L ≤ K) (he : ¬ N ≤ normalizer (L : Set G))
    (P : Sylow p (XiP p L)) :
    Nonempty (((P : Subgroup (XiP p L)).map (XiP p L).subtype) ≃* Plane p) ∧
      LinearThreeModel p (XiQuotient K) := by
  let h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  have hQ := uniqueness_local_quotient_sqtk hG hL.1.2.2
  obtain ⟨hp3,hshape⟩ := XiP_oddQuotient_of_A36 h36 hL.1 hQ hn ho hd
  have hX := (Chapter13.Section01.XiP_mem_XiPlus_source hG T hL.1 hn ho hd).1
  obtain ⟨_,hNX,_⟩ := Chapter13.Section01.RadicalConjugateRigidity.maximal_radical_structure
    hG T hL hn ho hd
  have hNK := (normal_subgroupOf_iff_le_normalizer hK.1).mp hKn
  have hTK := hTN.trans hNK
  have hXN : ¬ ((XiP p L).subgroupOf K).Normal := by
    intro hnormal
    have hQK := hG.twoLocal_sqtk hN
    have hquot : IsSQTK KnownSimple.IsKnownSimple (XiQuotient N) := by
      refine ⟨?_,hQK.isKGroup.quotient _⟩
      intro q hq hqo
      let : Fact q.Prime := ⟨hq⟩
      exact (primeRank_quotient_le_of_isTwoGroup q hqo _ pCore_isPGroup).trans
        (hQK.stronglyQuasithin q hq hqo)
    have hc := proposition_1_2_1_four_earlier_conclusion h36 hquot hK.2
    let := Rigidity.characteristic_of_normal hp3 T hX hshape hXK hTK
      (componentQuotientEquiv hK.1 hK.2) hc hnormal
    have hh := normalizer_le_normalizer_characteristic_image K ((XiP p L).subgroupOf K)
    rw [map_subgroupOf_eq_of_le hXK] at hh
    exact he (hNX ▸ hNK.trans hh)
  let H := K ⊔ (T : Subgroup G)
  have hHN : H ≤ N := sup_le hK.1 hTN
  have hKH : (K.subgroupOf H).IsCComponent := hK.2.subgroupOf_of_le le_sup_left hHN
  have hHs : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp ((hG.twoLocal_sqtk hN).subgroup _)
  have hSyl : IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)⟩
  have hi := localInput_of_mem_Xi hX hSyl (sup_le_sup_right hXK _) ho hshape P
  rcases hi.adequate_knownSimple hHs hSyl with hnormal | ⟨B,hB,_,_,ha⟩
  · exact (hXN (normal_subgroupOf_of_le_normalizer
      (le_sup_left.trans ((normal_subgroupOf_iff_le_normalizer
        (hXK.trans le_sup_left)).mp hnormal)))).elim
  have hBK : B = K := by
    let U := (T : Subgroup G).subgroupOf H
    have hgenK : K.subgroupOf H ⊔ U = ⊤ := by
      rw [← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
    have hnormK : U ≤ normalizer (K.subgroupOf H : Set H) := by
      rw [← subgroupOf_normalizer_eq (show K ≤ H from le_sup_left)]
      exact comap_mono hTK
    obtain ⟨t,ht⟩ := hKH.conjugate_of_pGroup_generated hB.2 T.isPGroup'.comap_subtype hgenK
    have hkfix : (K.subgroupOf H).conjBy (t : H) = K.subgroupOf H :=
      mem_normalizer_iff_map_conj_eq.mp (hnormK t.property)
    change B.subgroupOf H = (K.subgroupOf H).conjBy (t : H) at ht
    have hm := congrArg (map H.subtype) (ht.trans hkfix)
    simpa only [map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le hB.1] using hm
  subst B
  rcases ha with ha | held
  · have hs := surviving_alternatives hp3
      (XiP_automizer_not_isCyclic_of_A36 h36 hL.1 hQ hn ho hd P) ha
    exact ⟨hs.1,(hs.2.resolve_left (fun hh => hh.1.1 hTK)).2⟩
  · have := held.1
    omega

/-- The model consequence is independent of the choice of Sylow radical. -/
theorem escaping_component_linearThree
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    {N K : Subgroup G} (hN : IsTwoLocal N) (hTN : (T : Subgroup G) ≤ N)
    (hK : K ∈ cComponentsIn N) (hKn : (K.subgroupOf N).Normal)
    (hXK : XiP p L ≤ K) (he : ¬ N ≤ normalizer (L : Set G)) :
    LinearThreeModel p (XiQuotient K) :=
  (escaping_component_shape hG T hL hn ho hd hN hTN hK hKn hXK he default).2

end CFSG.Quasithin.Chapter3.RadicalCentralization.ChosenStars
