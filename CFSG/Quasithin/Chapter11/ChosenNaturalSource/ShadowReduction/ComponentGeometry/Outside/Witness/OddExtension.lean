module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.Attainment
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.OddIndex.CanonicalSource
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent
public import Theory.GroupTheory.Fitting.TwoCoreMonotonicity
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# The source odd-extension outside R₁-Sylow witness

The inverse image F of F(K/O₂(K)) cannot lie in M. Otherwise F normalizes
L₁, and its odd quotient normalizes the image of L₁ in K/O₂(K). The
intersection is trivial: its preimage is solvable in L₁, whose radical
is a two-group. Thus that image centralizes the self-centralizing odd
Fitting subgroup, contradicting the nonsolvability of L₁.

The original SQTK component hypotheses identify F with O₂,₂′(K), for
every surviving odd-by-SL₂ row, including nonsplit extensions and all
allowed primary kernels. Select an actual H-star inside FT and put
H₁ = R₁ O²(H). Both groups are solvable, so E.1.13 and positive attained
generation give their literal generation parameters as one. The original
radical Sylow theorem makes R₁ an actual Sylow subgroup of H₁. Escape,
containment in H, and the selected residual alternative are all proved.

Only the permitted preceding geometry, Kz=K, and the surviving source
row remain explicit. Their producers are qt-d-1222-natural-local-geometry,
qt-d-1222-shadow-linear-geometry, qt-d-1222-shadow-component-triangle and
qt-d-1222-shadow-component-comparison; final discharge belongs to
qt-d-1222-shadow-components. This branch needs no OddKernelNormalizer
premise. Generation one for every outside H, and the equal-component
carrier's upper bound, remain with qt-d-1222-shadow-component-witness.

Source: Aschbacher--Smith, A.3.6, pp.43--45; E.1.13, p.214;
11.4.4--11.5.1, printed pp.778--779, especially the odd-extension
construction in the opening paragraph of p.779.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside

private theorem not_normalizes_image_of_odd_fitting
    {A Q : Type*} [Group A] [Finite A] [Group Q] [Finite Q]
    (a : A →* Q) (ha : IsPGroup 2 a.ker)
    (hr : IsPGroup 2 (solvableRadical A)) (hs : ¬ Group.IsSolvable A)
    (F : Subgroup Q) [F.Normal] [Group.IsSolvable F]
    (ho : Odd (Nat.card F)) (hc : centralizer (F : Set Q) ≤ F) :
    ¬ F ≤ normalizer (a.range : Set Q) := by
  intro hn
  let : Group.IsNilpotent a.ker := ha.isNilpotent
  let N := F.comap a
  let : Group.IsSolvable N := isSolvable_comap_of_solvable_ker a F
  have hN : N ≤ solvableRadical A := le_solvableRadical _ inferInstance inferInstance
  have himage : N.map a = F ⊓ a.range := (map_comap_eq a F).trans (inf_comm _ _)
  have hp : IsPGroup 2 (F ⊓ a.range : Subgroup Q) := himage ▸ (hr.to_le hN).map a
  have hodd : Odd (Nat.card (F ⊓ a.range : Subgroup Q)) :=
    Odd.of_dvd_nat ho (card_dvd_of_le (inf_le_left : F ⊓ a.range ≤ F))
  have hi : F ⊓ a.range = ⊥ := card_eq_one.mp
    (hp.card_eq_or_dvd.resolve_right (Nat.not_even_iff_odd.mpr hodd ∘ even_iff_two_dvd.mpr))
  have hcomm : ⁅F,a.range⁆ = ⊥ := by
    apply bot_unique
    rw [← hi]
    exact le_inf (commutator_le_left _ _)
      (le_normalizer_iff_commutator_le_right.mp hn)
  have hrange : a.range ≤ F :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans hc
  let : Group.IsSolvable a.range := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hrange) (inclusion_injective hrange)
  exact hs (Group.isSolvable_of_ker_le_range a.ker.subtype a.rangeRestrict (by
    intro x hx
    exact ⟨⟨x,congrArg Subtype.val hx⟩,rfl⟩))


variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- The actual inverse image of the odd Fitting kernel escapes M in every
odd-by-SL₂ source row, without any splitting or restriction on its primary factors. -/
theorem ofFlag_odd_fitting_not_le
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    {p : ℕ} (hp : p = 5 ∨ (p.Prime ∧ 11 ≤ p))
    (hm : Source.IsSL (Source.TwoOddQuotient (ofFlag S f X z H).K) 2 p) :
    ¬ (twoFittingCore (ofFlag S f X z H).K).map (ofFlag S f X z H).K.subtype ≤
      normalizer (L : Set G) := by
  let E := ofFlag S f X z H
  let A := f.Li 0
  let K := E.K
  let Q := K ⧸ pCore 2 K
  let q := QuotientGroup.mk' (pCore 2 K)
  have hAK : A ≤ K := le_conjugateSpanBy _ _
  let a : A →* Q := q.comp (inclusion hAK)
  have ha : IsPGroup 2 a.ker := by
    change IsPGroup 2 (q.comp (inclusion hAK)).ker
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective (inclusion hAK) (inclusion_injective hAK)
  let : Group.IsPerfect A := LocalGeometry.localResidual_perfect _
  have hmodel : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 2 (2 ^ S.field.degree) := by
    obtain ⟨f₀,hu,_,hq,_⟩ := LocalGeometry.exists_unique_marked_flag D S c
    have he : A = f₀.Li 0 := by
      change LocalGeometry.localResidual L (c.preimage (f.space 0)) = _
      rw [hu 0 _ (f.dimension 0) (f.invariant 0)]
      rfl
    exact ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,he.symm ▸ hq 0⟩
  have hr : IsPGroup 2 (solvableRadical A) := by
    rw [Radical.radical_eq_core_of_psl2
      ((show 3 < 2 ^ 2 from by decide).trans_le
        (Nat.pow_le_pow_right (by decide) S.nonbinary)) hmodel]
    exact pCore_isPGroup
  have hns : ¬ Group.IsSolvable A :=
    Chapter1.mem_L_not_isSolvable (Triangle.Reselection.flag_residual_mem_local D S f 0)
  have hp' : p.Prime ∧ 3 < p := by
    rcases hp with rfl | ⟨hp,hl⟩
    · exact ⟨by decide,by decide⟩
    · exact ⟨hp,by omega⟩
  let : Fact p.Prime := ⟨hp'.1⟩
  have hnc := Radical.ofFlag_quotient_fitting_noncentral_of_sl2 S f K h.line_component hp'.2 hm
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using h.line_component.2.subgroupOf_of_le le_rfl h.line_component.1
  let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
  have hQ : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      htop.map_quotient (pCore 2 K)
  have hnq : ¬ IsQuasisimple Q := by
    intro hq
    let := hq
    exact hnc ((le_solvableRadical _ inferInstance inferInstance).trans
      IsQuasisimple.solvableRadical_le_center)
  have hE : componentLayer Q = ⊥ := by
    apply sSup_eq_bot.mpr
    intro C hC
    have ht := hC.isCComponent.eq_of_le hQ le_top
    let : IsQuasisimple (⊤ : Subgroup Q) := ht ▸ hC.2
    exact (hnq (IsQuasisimple.of_mulEquiv topEquiv)).elim
  have hstar : generalizedFitting Q = fittingSubgroup Q := by
    rw [generalizedFitting,hE,sup_bot_eq]
  have hc : centralizer (fittingSubgroup Q : Set Q) ≤ fittingSubgroup Q :=
    by simpa only [hstar] using (centralizer_generalizedFitting_le_fitting (G := Q))
  have ho : Odd (Nat.card (fittingSubgroup Q)) := Nat.coprime_two_left.mp
    (pPrimeCore_coprime_card.of_dvd_right
      (card_dvd_of_le (fitting_le_pPrimeCore_of_pCore_eq_bot 2 (pCore_quotient_pCore_eq_bot 2))))
  intro hFM
  have hFN : (twoFittingCore K).map K.subtype ≤ normalizer (A : Set G) :=
    (le_inf hFM ((map_subtype_le _).trans E.K_le_G₁)).trans
      Comparison.EarlierGeometry.line_stabilizer_normalizes_seed
  have hn : twoFittingCore K ≤ normalizer (A.subgroupOf K : Set K) := by
    rw [← subgroupOf_normalizer_eq hAK]
    intro k hk
    exact hFN (mem_map_of_mem K.subtype hk)
  have himage : (A.subgroupOf K).map q = a.range := by
    change (A.subgroupOf K).map q = (q.comp (inclusion hAK)).range
    rw [MonoidHom.range_comp]
    congr 1
    ext k
    constructor
    · intro hk
      exact ⟨⟨k,hk⟩,rfl⟩
    · rintro ⟨a,rfl⟩
      exact a.property
  have hFn : fittingSubgroup Q ≤ normalizer (a.range : Set Q) := by
    have hh := (map_mono (f := q) hn).trans (le_normalizer_map q)
    change ((fittingSubgroup Q).comap q).map q ≤ _ at hh
    rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),himage] at hh
    exact hh
  exact not_normalizes_image_of_odd_fitting a ha hr hns (fittingSubgroup Q) ho hc hFn


/-- In the source odd-extension row, the Fitting preimage is exactly O₂,₂′(K). -/
theorem ofFlag_twoFittingCore_eq_twoOddCore
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    {p : ℕ} (hp : p = 5 ∨ (p.Prime ∧ 11 ≤ p))
    (hm : Source.IsSL (Source.TwoOddQuotient (ofFlag S f X z H).K) 2 p) :
    twoFittingCore (ofFlag S f X z H).K =
      (pPrimeCore 2 ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K)).comap
        (QuotientGroup.mk' (pCore 2 (ofFlag S f X z H).K)) := by
  let K := (ofFlag S f X z H).K
  let Q := K ⧸ pCore 2 K
  have hK : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using h.line_component.2.subgroupOf_of_le le_rfl h.line_component.1
  let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
  have hQ : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      hK.map_quotient (pCore 2 K)
  have hs : IsSQTK KnownSimple.IsKnownSimple K :=
    (IsSQTK.equiv (subgroupOfEquivOfLe h.line_component.1)).mp
      ((S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0)).subgroup
        (K.subgroupOf (normalizer (f.Vi 0 : Set G))))
  have hsQ : IsSQTK KnownSimple.IsKnownSimple Q := by
    refine ⟨?_,hs.isKGroup.quotient _⟩
    intro r hr ho
    let : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r ho _ pCore_isPGroup).trans
      (hs.stronglyQuasithin r hr ho)
  have hlarge : 3 < p := by rcases hp with rfl | ⟨_,hl⟩ <;> omega
  exact congrArg (comap (QuotientGroup.mk' (pCore 2 K)))
    (Radical.intrinsic_fitting_eq_oddCore hsQ (pCore_quotient_pCore_eq_bot 2) hQ hlarge hm)

/-- Choose H inside O₂,₂′(K)T and construct its escaping R₁-Sylow subgroup.
Both literal generation parameters are one by solvability, with no Hall-control input. -/
theorem ofFlag_odd_selected_radical_witness
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hn : S.field.degree = 2)
    {p : ℕ} (hp : p = 5 ∨ (p.Prime ∧ 11 ≤ p))
    (hm : Source.IsSL (Source.TwoOddQuotient (ofFlag S f X z H).K) 2 p) :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z H) ∧ SelectedResidualAlternative (ofFlag S f X z J) ∧
      ChapterE.generationParameter J = 1 ∧
      ∃ w : OutsideRadicalWitness (ofFlag S f X z J),
        w.H₁ = (ofFlag S f X z H).R₁ ⊔ (pResidual 2 J).map J.subtype ∧
        w.H₁ ≤ (ofFlag S f X z H).R₁ ⊔
          ((pPrimeCore 2 ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K)).comap
            (QuotientGroup.mk' (pCore 2 (ofFlag S f X z H).K))).map
              (ofFlag S f X z H).K.subtype := by
  let E := ofFlag S f X z H
  let F := (twoFittingCore E.K).map E.K.subtype
  have hFK : F ≤ E.K := map_subtype_le _
  have hNK : Gz E ≤ normalizer (E.K : Set G) := point_normalizes_component E he
  have hNF : Gz E ≤ normalizer (F : Set G) := hNK.trans
    (normalizer_le_normalizer_characteristic_image E.K (twoFittingCore E.K))
  have hTF : (T : Subgroup G) ≤ normalizer (F : Set G) :=
    h.sylow_le_pointCentralizer.trans hNF
  have hFz : F ≤ Gz E := hFK.trans (he ▸ h.point_component.1)
  have hFout : ¬ F ≤ E.M := ofFlag_odd_fitting_not_le S f X z H h hp hm
  let : Group.IsSolvable (twoFittingCore E.K) := twoFittingCore_solvable
  let : Group.IsSolvable F := Group.isSolvable_of_surjective
    (E.K.subtype.subgroupMap_surjective (twoFittingCore E.K))
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  let : Group.IsSolvable (F ⊔ (T : Subgroup G) : Subgroup G) :=
    Group.isSolvable_sup_of_normalizes _ _ hTF
  have hFTz := sup_le hFz h.sylow_le_pointCentralizer
  obtain ⟨J,hJ,hJF⟩ := exists_HStar_below_point E h (F ⊔ (T : Subgroup G))
    le_sup_right hFTz (fun hh => hFout (le_sup_left.trans hh))
  have hJz := hJF.trans hFTz
  have hres : (pResidual 2 J).map J.subtype ≤ F := residual_le_factor F J hTF hJF
  let : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hJF) (inclusion_injective hJF)
  have hJpos := (selected_generation_spec (ofFlag S f X z J)
    ⟨h.point_mem,h.point_fixed,h.point_ne_one,h.seed_centralizes,
      h.line_component,h.point_component,h.normalizer_split⟩ hJ hJz).1
  have hJn : ChapterE.generationParameter J = 1 := Nat.le_antisymm
    ChapterE.generationParameter_le_one_of_solvable hJpos
  have hKc : Source.NormalComponentIn (centralizer (f.Vi 0 : Set G)) E.K :=
    ⟨⟨h.line_component_centralizes,h.line_component.2.subgroupOf_of_le
      h.line_component_centralizes (Subgroup.centralizer_le_normalizer _)⟩,
      normal_subgroupOf_of_le_normalizer
        ((Subgroup.centralizer_le_normalizer _).trans E.G₁_normalizes_K)⟩
  have hAK : f.Li 0 ≤ E.K := le_conjugateSpanBy _ _
  have hTK := (f.invariant 0).trans E.G₁_normalizes_K
  have hSyl := Radical.ofFlag_surviving_sylow_radical S f X z H E.K hKc hAK hTK
    (.sl2Prime rfl hn p hp hm)
  let C := E.K ⊔ (T : Subgroup G)
  let R := (solvableRadical C).map C.subtype
  have hCF : C ≤ normalizer (F : Set G) :=
    (sup_le E.K.le_normalizer hTK).trans
      (normalizer_le_normalizer_characteristic_image E.K (twoFittingCore E.K))
  have hFC : F ≤ C := hFK.trans le_sup_left
  let : (F.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer hCF
  let : Group.IsSolvable (F.subgroupOf C) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hFC).toMonoidHom) (subgroupOfEquivOfLe hFC).injective
  have hFR : F ≤ R := by
    have hh := map_mono (f := C.subtype)
      (le_solvableRadical (F.subgroupOf C) inferInstance inferInstance)
    rwa [map_subgroupOf_eq_of_le hFC] at hh
  let J₁ := E.R₁ ⊔ (pResidual 2 J).map J.subtype
  have hRJ : E.R₁ ≤ J := (LocalGeometry.localRadical_le_sylow _).trans hJ.1.1.2
  have hJ₁J : J₁ ≤ J := sup_le hRJ (map_subtype_le _)
  have hJ₁R : J₁ ≤ R := sup_le (Chapter1.isSylowIn_iff.mp hSyl).2.1 (hres.trans hFR)
  have hSyl₁ : Chapter1.IsSylowIn 2 E.R₁ J₁ := hSyl.restrict le_sup_left hJ₁R
  have hJ₁out : ¬ J₁ ≤ E.M := by
    intro hh
    apply hJ.1.2
    have hj := congrArg (map J.subtype) (pResidual_sup_sylow_eq_top (T.subtype hJ.1.1.2))
    have hPT : (T.subtype hJ.1.1.2 : Subgroup J).map J.subtype = (T : Subgroup G) := by
      change ((T : Subgroup G).subgroupOf J).map J.subtype = _
      exact map_subgroupOf_eq_of_le hJ.1.1.2
    have hjoin : (pResidual 2 J).map J.subtype ⊔ (T : Subgroup G) = J := by
      simpa only [Subgroup.map_sup,hPT, ← MonoidHom.range_eq_map,range_subtype] using hj
    rw [← hjoin]
    exact sup_le (le_sup_right.trans hh) D.sylow_normalizes_component
  let : Group.IsSolvable J₁ := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hJ₁J) (inclusion_injective hJ₁J)
  have hpos := (point_overgroup_generation_spec E h J₁ (hJ₁J.trans hJz)
    (mem_sup_left (f.seed_le_Ri S 0 (E.V₁_le h.point_mem)))).1
  have hn₁ : ChapterE.generationParameter J₁ = 1 := Nat.le_antisymm
    ChapterE.generationParameter_le_one_of_solvable hpos
  obtain ⟨P,hP⟩ := hSyl₁
  refine ⟨J,hJ,hJz,Or.inr (hres.trans hFK),hJn,
    ⟨J₁,P,hP,hJ₁J,hJ₁out,hn₁⟩,rfl,?_⟩
  rw [← ofFlag_twoFittingCore_eq_twoOddCore S f X z H h hp hm]
  exact sup_le_sup_left hres _

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside
