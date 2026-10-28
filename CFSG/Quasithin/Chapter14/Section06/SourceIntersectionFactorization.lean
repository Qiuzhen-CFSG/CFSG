module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableNormalizer
public import CFSG.Quasithin.Chapter14.Section06.MaximalOvergroups
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import CFSG.Quasithin.ChapterA.Section04.Intersection
public import Theory.GroupTheory.PlaneIntersectionFactorization
public import Mathlib.GroupTheory.Nilpotent

/-!
# The original intersection factorizations and maximality alternatives

For a suitable involution u, the already proved original 14.6.3(3) gives a
nontrivial plane action from C_{O₂(Mc)}(u). When I ∩ M escapes Mc, the literal
M/C_M(V) action of I ∩ M is all of S₃. The residual of the conjugate span of
its core intersection covers the cubic L-image. The plane-intersection lemma
therefore gives L = O²(L ∩ I) O₂(L) and LT = O²(L ∩ I) (T ∩ I) O₂(LT).
All joins are transported from M back into G and converted to set products.

For I maximal under T-intersection, the two-group normalizer condition forces
each characteristic normalizer to lie in I ∩ Mc unless I ∩ M escapes Mc.
For a minimal such I, every proper overgroup of its Sylow intersection remains
in the literal H-family. The existing minimality lemma then makes I ∩ Mc the
unique maximal overgroup unless the same factorization applies.

These are original 14.6.6(3–5), Aschbacher–Smith, refs/quasithin.pdf, printed
p.1023. Parts (4–5) retain exactly the properness and Sylow conclusions of
preceding parts (1–2), whose producer is `suitable_involution_intersection_sylow`.
The suitable-core action comes directly from `source_suitable_core_and_residual`;
no factorization or maximality conclusion is assumed.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]

open SourcePreliminaries Chapter15.Section03 Chapter15.Section03.InitialSource ChapterA.Section05To06

private theorem source_intersection_factorization
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (u : G) (I : Subgroup G)
    (hTuI : (T : Subgroup G) ⊓ centralizer ({u} : Set G) ≤ I)
    (hmove : ¬ Mc.pCoreIn 2 ⊓ centralizer ({u} : Set G) ≤
      Mc.pCoreIn 2 ⊓ centralizer (localModule T M : Set G))
    (hout : ¬ I ⊓ M ≤ Mc) :
    let L := sourceResidual M Mc
    let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
    (L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
      (L ⊔ (T : Subgroup G) : Subgroup G) =
        (R : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
          ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) := by
  let L := sourceResidual M Mc
  let C := (centralizer (localModule T M : Set G)).subgroupOf M
  let f := e.toMonoidHom.comp (QuotientGroup.mk' C)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective C)
  have hk : f.ker = C := by
    ext x
    change e (QuotientGroup.mk x) = 1 ↔ x ∈ C
    rw [←e.map_one,e.injective.eq_iff,QuotientGroup.eq_one_iff]
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    apply (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hunique ▸ Set.mem_singleton Mc).2
    intro z hz
    exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
  have hQT : Mc.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc] using
      pCoreIn_le_sylow Mc (T.subtype hTMc)
  have hQM : Mc.pCoreIn 2 ≤ M := hQT.trans hM.1.2
  have hCMc := localModule_centralizer_le_partner T M hunique
  have hMcQ : Mc ≤ normalizer (Mc.pCoreIn 2 : Set G) := Mc.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))
  let Y := L.subgroupOf M
  let Q := (Mc.pCoreIn 2).subgroupOf M
  let S := (T : Subgroup G).subgroupOf M
  let X := I.subgroupOf M
  let : Y.Normal := residualY_normal M Mc
  have hYp : IsPPerfect 2 Y := (residualY_isPPerfect M Mc).of_surjective
    (subgroupOfEquivOfLe (sourceResidual_le M Mc)).symm.toMonoidHom
    (subgroupOfEquivOfLe (sourceResidual_le M Mc)).symm.surjective
  obtain ⟨_,_,_,_,⟨eY⟩,hcore,rest⟩ :=
    source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e
  have hYc : Nat.card (Y.map f) = 3 := by
    change Nat.card (Y.map (e.toMonoidHom.comp (QuotientGroup.mk' C))) = 3
    rw [←Subgroup.map_map,Nat.card_congr
      ((Y.map (QuotientGroup.mk' C)).equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm]
    rw [Nat.card_congr eY.toEquiv]
    exact Nat.card_zmod 3
  have hYk : IsPGroup 2 (Y ⊓ f.ker : Subgroup M) := by
    rw [hk]
    change IsPGroup 2 ((L ⊓ centralizer (localModule T M : Set G)).subgroupOf M)
    rw [←hcore]
    exact (isPGroup_pCoreIn 2 _).comap_subtype
  have hkQ : f.ker ≤ normalizer (Q : Set M) := by
    rw [hk, ← subgroupOf_normalizer_eq hQM]
    exact fun x hx => hMcQ (hCMc hx)
  have hQI : ¬ Q ⊓ X ≤ f.ker := by
    intro hh
    apply hmove
    intro q hq
    have hqI : q ∈ I := hTuI ⟨hQT hq.1,hq.2⟩
    have hc : (⟨q,hQM hq.1⟩ : M) ∈ f.ker := hh ⟨hq.1,hqI⟩
    have hc' : (⟨q,hQM hq.1⟩ : M) ∈ C := hk ▸ hc
    exact ⟨hq.1,hc'⟩
  have hXout : ¬ X ≤ Q ⊔ f.ker := by
    intro hh
    apply hout
    intro x hx
    have hle : Q ⊔ f.ker ≤ Mc.subgroupOf M := sup_le
      (fun q hq => pCoreIn_le 2 Mc hq)
      (fun q hq => hCMc (show q ∈ C from hk ▸ hq))
    exact hle (hh (show (⟨x,hx.2⟩ : M) ∈ X from hx.1))
  obtain ⟨hLfac,hLTfac⟩ := plane_intersection_factorization f hf Y Q S X hYp
    (isPGroup_pCoreIn 2 Mc).comap_subtype hYc hYk hkQ (comap_mono hQT)
    T.isPGroup'.comap_subtype hQI hXout
  let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
  have hYM : Y.map M.subtype = L := map_subgroupOf_eq_of_le (sourceResidual_le M Mc)
  have hSM : S.map M.subtype = (T : Subgroup G) := map_subgroupOf_eq_of_le hM.1.2
  have hYXM : (Y ⊓ X).map M.subtype = L ⊓ I := by
    rw [Subgroup.map_inf _ _ _ M.subtype_injective,hYM,subgroupOf_map_subtype]
    ext x
    exact ⟨fun hx => ⟨hx.1,hx.2.1⟩,fun hx => ⟨hx.1,hx.2,sourceResidual_le M Mc hx.1⟩⟩
  have hRM : ((pResidual 2 (Y ⊓ X : Subgroup M)).map (Y ⊓ X).subtype).map M.subtype = R := by
    rw [map_embedded_pResidual,hYXM]
  have hkerM : f.ker.map M.subtype = M ⊓ centralizer (localModule T M : Set G) := by
    rw [hk,subgroupOf_map_subtype,inf_comm]
  have hYkM : (Y ⊓ f.ker).map M.subtype = L.pCoreIn 2 := by
    rw [Subgroup.map_inf _ _ _ M.subtype_injective,hYM,hkerM,←inf_assoc,
      inf_eq_left.mpr (sourceResidual_le M Mc)]
    exact hcore.symm
  have hSXM : (S ⊓ X).map M.subtype = (T : Subgroup G) ⊓ I := by
    rw [Subgroup.map_inf _ _ _ M.subtype_injective,hSM,subgroupOf_map_subtype]
    ext x
    exact ⟨fun hx => ⟨hx.1,hx.2.1⟩,fun hx => ⟨hx.1,hx.2,hM.1.2 hx.1⟩⟩
  have hYSkM : ((Y ⊔ S) ⊓ f.ker).map M.subtype = (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [Subgroup.map_inf _ _ _ M.subtype_injective,Subgroup.map_sup,hYM,hSM,hkerM,←inf_assoc,
      inf_eq_left.mpr (sup_le (sourceResidual_le M Mc) hM.1.2)]
    exact (Section02.source_residualSylow_quotient hG T hempty hM hunique hmany hcard e).1.symm
  have h1 : L = R ⊔ L.pCoreIn 2 := by
    have hh := congrArg (Subgroup.map M.subtype) hLfac
    simpa only [Subgroup.map_sup,hYM,hRM,hYkM] using hh
  have h2 : L ⊔ (T : Subgroup G) = R ⊔ ((T : Subgroup G) ⊓ I) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    have hh := congrArg (Subgroup.map M.subtype) hLTfac
    simpa only [Subgroup.map_sup,hYM,hSM,hRM,hSXM,hYSkM] using hh
  have hRL : R ≤ L := (map_subtype_le _).trans inf_le_left
  have hLQ : L ≤ normalizer (L.pCoreIn 2 : Set G) := L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hLTQ : L ⊔ (T : Subgroup G) ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)))
  have hTIbase : (T : Subgroup G) ⊓ I ≤ normalizer (L ⊓ I : Set G) :=
    (le_inf (inf_le_left.trans ((Section02.source_lemma_14_2_4 hG T hempty hM hunique hmany hcard e).sylow_normalizes_L))
      (inf_le_right.trans I.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hTIR : (T : Subgroup G) ⊓ I ≤ normalizer (R : Set G) := hTIbase.trans
    (normalizer_le_normalizer_characteristic_image _ (pResidual 2 (L ⊓ I : Subgroup G)))
  constructor
  · calc
      (L : Set G) = (R ⊔ L.pCoreIn 2 : Subgroup G) := congrArg SetLike.coe h1
      _ = _ := coe_mul_of_left_le_normalizer_right _ _ (hRL.trans hLQ)
  · calc
      ((L ⊔ (T : Subgroup G) : Subgroup G) : Set G) =
          ((R ⊔ ((T : Subgroup G) ⊓ I) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 : Subgroup G) : Set G) :=
        congrArg SetLike.coe h2
      _ = (R ⊔ ((T : Subgroup G) ⊓ I) : Subgroup G) *
          ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
        coe_mul_of_left_le_normalizer_right _ _ ((sup_le (hRL.trans le_sup_left)
          (inf_le_left.trans le_sup_right)).trans hLTQ)
      _ = _ := by rw [coe_mul_of_right_le_normalizer_left _ _ hTIR]

private theorem characteristicNormalizerIn_le_or_intersection_not_le
    (T : Sylow 2 G) (Tu Mc M I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G) Tu Mc M))
    (hTuT : Tu ≤ (T : Subgroup G))
    (hproper : (T : Subgroup G) ⊓ I < (T : Subgroup G)) :
    ChapterA.Section04.characteristicNormalizerIn I ((T : Subgroup G) ⊓ I) ≤ I ⊓ Mc ∨
      ¬ I ⊓ M ≤ Mc := by
  classical
  by_cases hIM : I ⊓ M ≤ Mc
  · left
    let R : Subgroup G := (T : Subgroup G) ⊓ I
    have hTuR : Tu ≤ R := le_inf hTuT hI.1.2.1
    have hRproper : R.subgroupOf (T : Subgroup G) < ⊤ := by
      rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
      exact hproper.not_ge
    let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
    obtain ⟨t, ht, htR⟩ := SetLike.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent (R.subgroupOf (T : Subgroup G)) hRproper)
    have htN : (t : G) ∈ normalizer (R : Set G) := by
      rw [← subgroupOf_normalizer_eq (show R ≤ (T : Subgroup G) from inf_le_left)] at ht
      exact ht
    apply iSup_le
    intro C
    apply iSup_le
    intro hC
    apply iSup_le
    intro hne
    let := hC
    let W : Subgroup G := C.map R.subtype
    have hWne : W ≠ ⊥ := fun hz => hne
      ((map_eq_bot_iff_of_injective _ R.subtype_injective).mp hz)
    have hWp : IsPGroup 2 W :=
      ((T.isPGroup'.to_le (show R ≤ (T : Subgroup G) from inf_le_left)).to_subgroup C).map _
    have hRN : normalizer (R : Set G) ≤ normalizer (W : Set G) :=
      normalizer_le_normalizer_characteristic_image R C
    have hWcore : W ≤ (normalizer (W : Set G)).pCoreIn 2 :=
      le_pCoreIn_of_normalizes hWp W.le_normalizer le_rfl
    have hNH : normalizer (W : Set G) ∈ Chapter1.H G := by
      intro hz
      exact hWne (le_bot_iff.mp (hz ▸ hWcore))
    refine le_inf inf_le_left ?_
    by_contra hnot
    have hNMc : ¬ normalizer (W : Set G) ≤ Mc := fun hn =>
      hnot (inf_le_right.trans hn)
    have hNM : ¬ normalizer (W : Set G) ≤ M := fun hn =>
      hnot ((le_inf inf_le_left (inf_le_right.trans hn)).trans hIM)
    have hNfam : normalizer (W : Set G) ∈ outsideOvergroups (Chapter1.H G) Tu Mc M :=
      ⟨hNH, hTuR.trans (R.le_normalizer.trans hRN), hNMc, hNM⟩
    have hbound : (T : Subgroup G) ⊓ normalizer (W : Set G) ≤ R :=
      hI.2 hNfam (le_inf inf_le_left (R.le_normalizer.trans hRN))
    exact htR (hbound ⟨t.property, hRN htN⟩)
  · exact Or.inr hIM

omit [Finite G] in
private theorem unique_maximal_or_intersection_not_le
    (T : Sylow 2 G) (Tu Mc M I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G) Tu Mc M))
    (hTuT : Tu ≤ (T : Subgroup G)) (hTMc : (T : Subgroup G) ≤ Mc)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ I) I) :
    (((T : Subgroup G) ⊓ I ≤ I ⊓ Mc) ∧
      Maximal (fun Y : Subgroup G => Y < I) (I ⊓ Mc) ∧
      ∀ J : Subgroup G, (T : Subgroup G) ⊓ I ≤ J →
        Maximal (fun Y : Subgroup G => Y < I) J → J = I ⊓ Mc) ∨
      ¬ I ⊓ M ≤ Mc := by
  classical
  by_cases hIM : I ⊓ M ≤ Mc
  · left
    apply unique_maximal_over_intersection_of_iMin hI hTuT hTMc hIM
    intro J hRJ hJI
    obtain ⟨P, hP⟩ := hSyl
    have hcoreR : I.pCoreIn 2 ≤ (T : Subgroup G) ⊓ I := hP ▸ pCoreIn_le_sylow I P
    have hIn : I ≤ normalizer (I.pCoreIn 2 : Set G) :=
      I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
    have hcoreJ : I.pCoreIn 2 ≤ J.pCoreIn 2 :=
      le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I) (hcoreR.trans hRJ)
        (hJI.le.trans hIn)
    intro hz
    exact hI.1.1.1 (le_bot_iff.mp (hz ▸ hcoreJ))
  · exact Or.inr hIM

/-- Original 14.6.6(3), with the suitable-involution action constructed from the original source. -/
theorem source_lemma_14_6_6_3
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (I : Subgroup G) (hTuI : (T : Subgroup G) ⊓ centralizer ({u} : Set G) ≤ I)
    (hout : ¬ I ⊓ M ≤ Mc) :
    let L := sourceResidual M Mc
    let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
    (L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
      (L ⊔ (T : Subgroup G) : Subgroup G) =
        (R : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
          ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) := by
  exact source_intersection_factorization hG T hempty hM hunique hmany hcard e u I hTuI
    (source_suitable_core_and_residual hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct).2.1 hout

/-- Original 14.6.6(4). The proper Sylow intersection is supplied by parts (1–2),
proved in `suitable_involution_intersection_sylow`. -/
theorem source_lemma_14_6_6_4
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hproper : (T : Subgroup G) ⊓ I < (T : Subgroup G)) :
    let L := sourceResidual M Mc
    let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
    ChapterA.Section04.characteristicNormalizerIn I ((T : Subgroup G) ⊓ I) ≤ I ⊓ Mc ∨
      ((L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
        (L ⊔ (T : Subgroup G) : Subgroup G) =
          (R : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
            ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  rcases characteristicNormalizerIn_le_or_intersection_not_le T _ Mc M I hI inf_le_left hproper with hc | hx
  · exact Or.inl hc
  · exact Or.inr (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct I hI.1.2.1 hx)

/-- Original 14.6.6(5). Its Sylow premise is exactly the preceding part (2),
proved in `suitable_involution_intersection_sylow`; all local-family hypotheses
in the maximality argument are discharged here. -/
theorem source_lemma_14_6_6_5
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ I) I) :
    let L := sourceResidual M Mc
    let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
    (((T : Subgroup G) ⊓ I ≤ I ⊓ Mc) ∧
      Maximal (fun Y : Subgroup G => Y < I) (I ⊓ Mc) ∧
      ∀ J : Subgroup G, (T : Subgroup G) ⊓ I ≤ J →
        Maximal (fun Y : Subgroup G => Y < I) J → J = I ⊓ Mc) ∨
      ((L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
        (L ⊔ (T : Subgroup G) : Subgroup G) =
          (R : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
            ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    apply (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hunique ▸ Set.mem_singleton Mc).2
    intro z hz
    exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
  rcases unique_maximal_or_intersection_not_le T _ Mc M I hI inf_le_left hTMc hSyl with hc | hx
  · exact Or.inl hc
  · exact Or.inr (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct I hI.1.1.2.1 hx)

end CFSG.Quasithin.Chapter14.Section06
