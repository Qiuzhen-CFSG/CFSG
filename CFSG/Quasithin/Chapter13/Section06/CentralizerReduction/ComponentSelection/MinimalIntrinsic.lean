module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.CharacteristicNormalizers
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.ActionKernels
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import Theory.GroupTheory.CComponent.QuasisimpleImageSupplement
public import Theory.GroupTheory.SolvableRadical.TwoCoreOddQuotient
public import Theory.Quasithin.Rank

/-!
# Intrinsic quasisimplicity of an equal-star minimum

Let K be minimal among the original local components with its star image,
and put R=rad(K), S=Tᵥ. Frattini's argument gives K=R N_K(R∩S).
The residual of N_K(R∩S)S is another local component, invariant under S.
Its radical-supplement property and the quasisimple two-core quotient of
K* give the same literal star image. Minimality forces K to normalize R∩S.
Consequently R/O₂(K) has odd order. Both nonquasisimple alternatives of
A.3.6 have even radical, so K/O₂(K) is quasisimple.

This proves the source minimality step uniformly, including L₃(2)≅L₂(7).
It does not assume that the natural odd radical splits or that an arbitrary
plus-action kernel is a two-group. The original-source linear-three
consumer instantiates A.3.6 and constructs its MS pair.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 13.6.22,
printed p.932; A.3.6, pp.43--45.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
variable {G : Type*} [Group G] [Finite G]

private theorem normalizer_replacement_le_normal (K S : Subgroup G) (C : Subgroup S)
    [C.Normal] (hK : K ∈ Chapter1.L G S)
    (hS : S ≤ normalizer (K : Set G)) :
    characteristicNormalizerReplacement K S C ≤ K ⊓ normalizer (C.map S.subtype : Set G) := by
  let D := C.map S.subtype
  let M := (K ⊓ normalizer (D : Set G)) ⊔ S
  have hSD : S ≤ normalizer (D : Set G) :=
    by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (C.le_normalizer_map S.subtype :
        (normalizer (C : Set S)).map S.subtype ≤ normalizer (C.map S.subtype : Set G))
  have hMH : M ≤ K ⊔ S := sup_le_sup inf_le_left le_rfl
  let := Chapter1.mem_L_isPerfect hK
  let : Group.IsNilpotent S := (Chapter1.isSylowIn_iff.mp hK.2.1).1.isNilpotent
  have hres := map_residual_sup_eq_of_perfect_of_solvable K S hS
  exact le_inf ((map_solvableResidual_mono hMH).trans hres.le)
    ((map_subtype_le (solvableResidual M)).trans (sup_le inf_le_right hSD))

/-- Failure of strictness constructs the supplement, its invariance and its
genuine local-family membership. No moving condition is inferred from coverage. -/
private theorem normalizerReplacement_spec_of_normal
    (S K : Subgroup G) (hK : K ∈ Chapter1.L G S)
    (hS : S ≤ normalizer (K : Set G))
    (C : Subgroup S) [C.Normal] (hC : C ≠ ⊥)
    (hgen : (solvableRadical K).map K.subtype ⊔
      (K ⊓ normalizer (C.map S.subtype : Set G)) = K) :
    characteristicNormalizerReplacement K S C ≤ K ⊓ normalizer (C.map S.subtype : Set G) ∧
    S ≤ normalizer (characteristicNormalizerReplacement K S C : Set G) ∧
    characteristicNormalizerReplacement K S C ∈ Chapter1.L G S ∧
    (solvableRadical K).map K.subtype ⊔ characteristicNormalizerReplacement K S C = K := by
  let R := (solvableRadical K).map K.subtype
  let D := C.map S.subtype
  let N := K ⊓ normalizer (D : Set G)
  let H := K ⊔ S
  let M := N ⊔ S
  let K₁ := characteristicNormalizerReplacement K S C
  have hK₁N : K₁ ≤ N := normalizer_replacement_le_normal K S C hK hS
  have hSD : S ≤ normalizer (D : Set G) :=
    by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (C.le_normalizer_map S.subtype :
        (normalizer (C : Set S)).map S.subtype ≤ normalizer (C.map S.subtype : Set G))
  have hMK₁ : M ≤ normalizer (K₁ : Set G) :=
    M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (solvableResidual M))
  have hSK₁ : S ≤ normalizer (K₁ : Set G) := le_sup_right.trans hMK₁
  have hMH : M ≤ H := sup_le_sup inf_le_left le_rfl
  have hRM : R ⊔ M = H := by
    change R ⊔ (N ⊔ S) = K ⊔ S
    rw [← sup_assoc, hgen]
  have hRH : R ≤ H := (map_subtype_le _).trans le_sup_left
  have hHR : H ≤ normalizer (R : Set G) :=
    (sup_le K.le_normalizer hS).trans
      (normalizer_le_normalizer_characteristic_image K (solvableRadical K))
  let : Group.IsSolvable R := Group.isSolvable_of_surjective
    (f := K.subtype.subgroupMap (solvableRadical K))
    (K.subtype.subgroupMap_surjective _)
  let := Chapter1.mem_L_isPerfect hK
  let : Group.IsNilpotent S := (Chapter1.isSylowIn_iff.mp hK.2.1).1.isNilpotent
  have hres : (solvableResidual H).map H.subtype = K :=
    map_residual_sup_eq_of_perfect_of_solvable K S hS
  have hres' : solvableResidual H = K.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hres, map_subgroupOf_eq_of_le le_sup_left]
  have hHcomp : (solvableResidual H).IsCComponent := hres'.symm ▸ hK.1
  have hMcomp : (solvableResidual M).IsCComponent :=
    residual_isCComponent_of_solvable_supplement_in H R M hRH hMH hHR hRM hHcomp
  have hK₁M : K₁ ≤ M := map_subtype_le _
  have hK₁comp : (K₁.subgroupOf M).IsCComponent := by
    have he : K₁.subgroupOf M = solvableResidual M :=
      comap_map_eq_self_of_injective M.subtype_injective _
    exact he.symm ▸ hMcomp
  have hJM : K₁ ⊔ S ≤ M := sup_le hK₁M le_sup_right
  have hJH : K₁ ⊔ S ≤ H := hJM.trans hMH
  have hDcore : D ≤ (K₁ ⊔ S).pCoreIn 2 :=
    le_pCoreIn_of_normalizes
      ((Chapter1.isSylowIn_iff.mp hK.2.1).1.to_le (map_subtype_le C))
      ((map_subtype_le C).trans le_sup_right)
      (sup_le (hK₁N.trans inf_le_right) hSD)
  have hlocal : K₁ ∈ Chapter1.L G S := by
    refine ⟨hK₁comp.subgroupOf_of_le le_sup_left hJM,
      hK.2.1.restrict le_sup_right hJH, ?_⟩
    intro he
    exact hC ((map_eq_bot_iff_of_injective C S.subtype_injective).mp
      (bot_unique (he ▸ hDcore)))
  refine ⟨hK₁N, hSK₁, hlocal, le_antisymm
    (sup_le (map_subtype_le _) (hK₁N.trans inf_le_left)) ?_⟩
  exact hres.symm.le.trans
    (map_solvableResidual_le_sup_residual_of_sup_eq H R M hRH hMH hHR hRM)


open Theory.GroupTheory

private theorem local_sylow_intersection (K S : Subgroup G)
    (hK : K ∈ Chapter1.L G S) (hn : S ≤ normalizer (K : Set G)) :
    ∃ R : Sylow 2 K, (R : Subgroup K).map K.subtype ≤ S := by
  let J := K ⊔ S
  let C := K.subgroupOf J
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  obtain ⟨P, hP⟩ := hK.2.1
  obtain ⟨R, hR⟩ := P.exists_subgroupOf_eq_of_normal C
  let i : C ≃* K := subgroupOfEquivOfLe le_sup_left
  refine ⟨R.mapSurjective (f := i.toMonoidHom) i.surjective, ?_⟩
  rintro x ⟨k, ⟨r, hr, rfl⟩, rfl⟩
  have hrP : (r : J) ∈ (P : Subgroup J) := by
    change r ∈ (P : Subgroup J).subgroupOf C
    rw [← hR]
    exact hr
  exact hP ▸ mem_map_of_mem J.subtype hrP

/-- The original star image is unchanged by every invariant radical supplement. -/
theorem starImage_eq_of_invariant_radical_supplement
    (K D L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v)
    (hnK : Tv T v ≤ normalizer (K : Set G))
    (hnD : Tv T v ≤ normalizer (D : Set G))
    (hgen : (solvableRadical K).map K.subtype ⊔ D = K) :
    starImage z v D = starImage z v K := by
  have hDK : D ≤ K := le_sup_right.trans_eq hgen
  let B := D.subgroupOf K
  let A := starImage z v K
  let f := starImageMap z v K hK.1.1
  have hf := starImageMap_surjective z v K hK.1.1
  let := Chapter1.mem_L_isPerfect hK.1.2
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective hf
  let : IsQuasisimple (A ⧸ pCore 2 A) := hK.2.1
  obtain ⟨R,hR⟩ := local_sylow_intersection K (Tv T v) hK.1.2 hnK
  have hnB : (R : Subgroup K) ≤ normalizer (B : Set K) := by
    apply le_normalizer_iff.mpr
    intro x hx y hy
    exact (mem_normalizer_iff.mp (hnD (hR (mem_map_of_mem _ hx))) (y:G)).mp hy
  have hgenB : solvableRadical K ⊔ B = ⊤ := by
    apply map_injective K.subtype_injective
    simpa only [Subgroup.map_sup, B, map_subgroupOf_eq_of_le hDK,
      ← MonoidHom.range_eq_map, range_subtype] using hgen
  have htop := map_radical_supplement_eq_top_of_quasisimple_twoCore f hf R B hnB hgenB
  rw [starImageMap_subgroup z v D K hK.1.1 hDK] at htop
  exact le_antisymm (map_mono (comap_mono hDK)) (subgroupOf_eq_top.mp htop)

/-- Equal-star minimality forces normalization of every normal Sylow subgroup
whose normalizer supplements the radical. -/
private theorem normalizes_of_minimal_equalStar_normalizer_supplement
    (K H L T : Subgroup G) (z v : G) (hK : K ∈ Yz L T z v)
    (hnK : Tv T v ≤ normalizer (K : Set G))
    (hmin : Minimal (fun D => D ∈ Chapter1.LIn H (Tv T v) ∧
      starImage z v D = starImage z v K) K)
    (C : Subgroup (Tv T v)) [C.Normal] (hC : C ≠ ⊥)
    (hgen : (solvableRadical K).map K.subtype ⊔
      (K ⊓ normalizer (C.map (Tv T v).subtype : Set G)) = K) :
    K ≤ normalizer (C.map (Tv T v).subtype : Set G) := by
  obtain ⟨hle, hn, hl, hg⟩ := normalizerReplacement_spec_of_normal
    (Tv T v) K hK.1.2 hnK C hC hgen
  have he := starImage_eq_of_invariant_radical_supplement K _ L T z v hK hnK hn hg
  have hKD := hmin.2 ⟨⟨(hle.trans inf_le_left).trans hmin.1.1.1, hl⟩,he⟩
    (hle.trans inf_le_left)
  exact hKD.trans (hle.trans inf_le_right)

private theorem radical_sylow_normalizer_supplement (K S : Subgroup G)
    (hK : K ∈ Chapter1.L G S) :
    let R := (solvableRadical K).map K.subtype
    R ⊔ (K ⊓ normalizer ((R ⊓ S : Subgroup G) : Set G)) = K := by
  let R := (solvableRadical K).map K.subtype
  have hRK : R ≤ K := map_subtype_le _
  have hKR : K ≤ normalizer (R : Set G) :=
    K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (solvableRadical K))
  let R' := R.subgroupOf K
  let : R'.Normal := normal_subgroupOf_of_le_normalizer hKR
  have hSK := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hK.2.1 (show K ≤ K ⊔ S from le_sup_left) hK.1.subnormal
  have hSR := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSK hRK
    (inferInstance : R'.Normal).isSubnormal
  have hi : (S ⊓ K) ⊓ R = R ⊓ S := by
    ext x
    simp only [mem_inf]
    constructor
    · exact fun h => ⟨h.2,h.1.1⟩
    · exact fun h => ⟨⟨h.2,hRK h.1⟩,h.1⟩
  rw [hi] at hSR
  obtain ⟨P,hP⟩ := hSR
  let e : R ≃* R' := (subgroupOfEquivOfLe hRK).symm
  let P' : Sylow 2 R' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmap : ((P' : Subgroup R').map R'.subtype).map K.subtype = R ⊓ S := by
    change (((P : Subgroup R).map e.toMonoidHom).map R'.subtype).map K.subtype = _
    rw [map_map,map_map]
    exact hP
  have hfr := congrArg (fun A : Subgroup K => A.map K.subtype) P'.normalizer_sup_eq_top
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, K.range_subtype,
    subgroupOf_map_subtype, inf_of_le_left hRK] at hfr
  apply le_antisymm (sup_le hRK inf_le_left)
  apply hfr.symm.le.trans
  refine sup_le (le_trans ?_ le_sup_right) le_sup_left
  refine le_inf (map_subtype_le _) ?_
  have hn := ((P' : Subgroup R').map R'.subtype).le_normalizer_map K.subtype
  rwa [hmap] at hn

/-- The actual radical Sylow subgroup is normalized by an equal-star minimal
component. Frattini supplies the supplement; there is no normalizer premise. -/
private theorem radical_sylow_normalized_of_minimal_equalStar
    (K H L T : Subgroup G) (z v : G) (hK : K ∈ Yz L T z v)
    (hnK : Tv T v ≤ normalizer (K : Set G))
    (hmin : Minimal (fun D => D ∈ Chapter1.LIn H (Tv T v) ∧
      starImage z v D = starImage z v K) K) :
    K ≤ normalizer (((solvableRadical K).map K.subtype ⊓ Tv T v : Subgroup G) : Set G) := by
  let S := Tv T v
  let R := (solvableRadical K).map K.subtype
  let C := R.subgroupOf S
  have hSR : S ≤ normalizer (R : Set G) :=
    hnK.trans (normalizer_le_normalizer_characteristic_image K (solvableRadical K))
  let : C.Normal := normal_subgroupOf_of_le_normalizer hSR
  have hCmap : C.map S.subtype = R ⊓ S := subgroupOf_map_subtype R S
  by_cases hC : C = ⊥
  · rw [← hCmap,hC,Subgroup.map_bot]
    rw [normalizer_eq_top]
    exact le_top
  have hg := radical_sylow_normalizer_supplement K S hK.1.2
  change R ⊔ (K ⊓ normalizer ((R ⊓ S : Subgroup G) : Set G)) = K at hg
  rw [← hCmap] at hg
  have hh := normalizes_of_minimal_equalStar_normalizer_supplement
    K H L T z v hK hnK hmin C hC hg
  change K ≤ normalizer (C.map S.subtype : Set G) at hh
  rwa [hCmap] at hh

/-- Normalization of the literal radical Sylow intersection makes the radical
index over O₂(K) odd. -/
private theorem odd_radical_relIndex_of_normalized_intersection
    (K S : Subgroup G) (hK : K ∈ Chapter1.L G S)
    (hnK : S ≤ normalizer (K : Set G))
    (hnP : K ≤ normalizer (((solvableRadical K).map K.subtype ⊓ S : Subgroup G) : Set G)) :
    Odd ((pCore 2 K).relIndex (solvableRadical K)) := by
  let P := (solvableRadical K).map K.subtype ⊓ S
  let : (P.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hnP
  have hPtwo : IsPGroup 2 P := (Chapter1.isSylowIn_iff.mp hK.2.1).1.to_le inf_le_right
  have hPc : P.subgroupOf K ≤ pCore 2 K :=
    le_sSup ⟨inferInstance,hPtwo.comap_subtype⟩
  obtain ⟨U,hU⟩ := local_sylow_intersection K S hK hnK
  obtain ⟨Q,hQ⟩ := U.exists_subgroupOf_eq_of_normal (solvableRadical K)
  have hQc : (Q : Subgroup (solvableRadical K)) ≤ (pCore 2 K).subgroupOf (solvableRadical K) := by
    intro q hq
    apply hPc
    refine ⟨mem_map_of_mem K.subtype q.property, ?_⟩
    apply hU
    apply mem_map_of_mem
    have hq' : q ∈ (U : Subgroup K).subgroupOf (solvableRadical K) := hQ ▸ hq
    exact hq'
  exact Nat.not_even_iff_odd.mp (fun he => Q.not_dvd_index
    ((even_iff_two_dvd.mp he).trans (index_dvd_of_le hQc)))

/-- Source minimality removes the even radical in the actual intrinsic quotient. -/
theorem odd_radical_relIndex_of_minimal_equalStar
    (K H L T : Subgroup G) (z v : G) (hK : K ∈ Yz L T z v)
    (hnK : Tv T v ≤ normalizer (K : Set G))
    (hmin : Minimal (fun D => D ∈ Chapter1.LIn H (Tv T v) ∧
      starImage z v D = starImage z v K) K) :
    Odd ((pCore 2 K).relIndex (solvableRadical K)) :=
  odd_radical_relIndex_of_normalized_intersection K (Tv T v) hK.1.2 hnK
    (radical_sylow_normalized_of_minimal_equalStar K H L T z v hK hnK hmin)

private theorem odd_radical_equiv {A B : Type*} [Group A] [Finite A]
    [Group B] [Finite B] (e : A ≃* B)
    (h : Odd (Nat.card (solvableRadical A))) : Odd (Nat.card (solvableRadical B)) := by
  rw [← map_solvableRadical_equiv e,
    ← Nat.card_congr ((solvableRadical A).equivMapOfInjective e.toMonoidHom e.injective).toEquiv]
  exact h

private theorem quasisimple_of_a36_odd_radical
    {X : Type*} [Group X] [Finite X] (B : Subgroup X) (hB : B.IsCComponent)
    (h : Chapter1.Section02.A36Conclusion B)
    (ho : Odd (Nat.card (solvableRadical B))) : IsQuasisimple B := by
  rcases h.2.2.2.1 with hi | hc
  · have hd := relIndex_dvd_card (fittingSubgroup B) (solvableRadical B)
    rw [hi.2.2] at hd
    exact (Nat.not_even_iff_odd.mpr ho (even_iff_two_dvd.mpr hd)).elim
  · have hr : solvableRadical B = center B := hc.2.1.symm.trans hc.1
    let := hB.perfect
    let := hB.isSimpleGroup_quotient_solvableRadical
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩

/-- The actual equal-star source minimum has quasisimple intrinsic quotient.
The complete A.3.6 theorem is instantiated on the original local two-core quotient. -/
theorem intrinsic_quasisimple_of_minimal_equalStar
    {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (hA36 : ∀ (X : Type _) [Group X] [Finite X], IsSQTK 𝒦 X → pCore 2 X = ⊥ →
      ∀ B : Subgroup X, B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (K H L T : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hK : K ∈ Yz L T z v) (hnK : Tv T v ≤ normalizer (K : Set G))
    (hmin : Minimal (fun D => D ∈ Chapter1.LIn H (Tv T v) ∧
      starImage z v D = starImage z v K) K) : IsQuasisimple (K ⧸ pCore 2 K) := by
  let X := K ⊔ Tv T v
  let B := K.subgroupOf X
  have hle : X ≤ Gv v := sup_le hK.1.1 inf_le_right
  have hsq : IsSQTK 𝒦 X := (IsSQTK.equiv (subgroupOfEquivOfLe hle)).mp
    ((hG.involution_centralizer_sqtk hv).subgroup (X.subgroupOf (Gv v)))
  have hsqQ : IsSQTK 𝒦 (X ⧸ pCore 2 X) := by
    refine ⟨?_, hsq.isKGroup.quotient (pCore 2 X)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 X) pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  let := pCore_isNilpotent (p := 2) (G := X)
  have hB : B.IsCComponent := hK.1.2.1
  have ha := Chapter1.Section02.proposition_1_2_1_four_earlier_conclusion hA36 hsqQ hB
  let a : B ≃* K := subgroupOfEquivOfLe le_sup_left
  let e := (QuotientGroup.congr (pCore 2 B) (pCore 2 K) a (pCore_map_iso 2 a)).symm.trans
    (cComponentTwoCoreQuotientEquiv hB)
  have ho : Odd (Nat.card (solvableRadical (K ⧸ pCore 2 K))) :=
    (odd_radical_twoCore_quotient_iff).mpr
      (odd_radical_relIndex_of_minimal_equalStar K H L T z v hK hnK hmin)
  let := quasisimple_of_a36_odd_radical _ (hB.map_quotient _) ha (odd_radical_equiv e ho)
  exact IsQuasisimple.of_mulEquiv e.symm

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
