module
public import Stellmacher.SectionTen.OpeningData
public import Stellmacher.SectionNine.NineNextQuotientFixedGeneration
public import Stellmacher.SectionNine.NineSevenNormalityObstructions
public import Stellmacher.SectionThree.PSetQuadraticFixedHyperplane
public import Theory.GroupAction.SubgroupQuotientCommutatorImage
public import Theory.GroupAction.ActorSubtypeCommutator
public import Theory.GroupAction.InvolutionCommutatorSmallLayer

/-!
# An actor with a small commutator in Stellmacher (10.1)

From the ambient Section Ten context and offset-two middle vertex alone,
there is an actor in the first module outside the terminal core whose
commutator with the terminal module has order two or four. In the latter
case it contains the first center. No module size, transvection, fixed-space,
or index conclusion is assumed.

Use the literal conjugation action on the first module modulo its center.
Its two-core kernel and the proved Sylow-fixed generation permit the
hereditary (1.2) fixed-hyperplane theorem. The terminal module acts
quadratically by (7.5), and critical noncontainment makes the image of the
terminal core proper. The returned fixed vector lifts to the actor outside
that core; the returned actor subgroup has index at most two and commutator
contained in the first center. The elementary displacement-count theorem
therefore bounds the full commutator by order four. The full terminal-module
centralizer bound excludes a trivial commutator, and the two-group order
forces the stated dichotomy.

Source: Stellmacher, Journal of Algebra 190 (1997), (10.1), printed p.60,
the application of (1.2) and assertion (4), `refs/files/stellmacher-n-group.pdf`.
The first theorem retains the actual subgroup and fixed-vector witness used
in that source step; the second supplies an ambient cardinal bound. The
third takes the quotient by the terminal center, as the bars on printed
pp.59–60 require, and gives exactly assertion (4). The faithful quotient
action excludes quotient order one, and the elementary subgroup product
formula converts the ambient order bound to the quotient dichotomy.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem commutator_zpowers_le
    {K : Type u} [Group K] (U Z : Subgroup K) (actor : K)
    (hnorm : actor ∈ Subgroup.normalizer (Z : Set K))
    (hcomm : ∀ element ∈ U, ⁅element, actor⁆ ∈ Z) :
    ⁅U, Subgroup.zpowers actor⁆ ≤ Z := by
  have hnorms : Subgroup.closure ({actor} : Set K) ≤ Subgroup.normalizer (Z : Set K) :=
    (Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hnorm)
  apply Subgroup.commutator_le.mpr
  intro element helement mover hmover
  rw [Subgroup.zpowers_eq_closure] at hmover
  induction hmover using Subgroup.closure_induction with
  | mem mover hmover => exact Set.mem_singleton_iff.mp hmover ▸ hcomm element helement
  | one => simp
  | mul first second hfirst hsecond ihfirst ihsecond =>
    rw [commutatorElement_mul_right_eq_mul_conj]
    simpa only [mul_assoc] using Z.mul_mem ihfirst
      ((Subgroup.mem_normalizer_iff.mp (hnorms hfirst) _).mp ihsecond)
  | inv mover hmover ih =>
    rw [commutatorElement_inv_right, ← commutatorElement_inv]
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
      (hnorms ((Subgroup.closure ({actor} : Set K)).inv_mem hmover)) _).mp (Z.inv_mem ih)

public theorem ten_one_fixed_hyperplane_actor
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    ∃ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep ∧
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' ∧
      ∃ A₀ : Subgroup G, A₀ ≤ VAt ctx.Γ ctx.criticalPath.a' ∧
        Nat.card (VAt ctx.Γ ctx.criticalPath.a') ≤ 2 * Nat.card A₀ ∧
        ⁅A₀, Subgroup.zpowers actor⁆ ≤ ZAt ctx.Γ ctx.criticalPath.firstStep := by
  classical
  let P := GAt ctx.Γ ctx.criticalPath.firstStep
  let V := VAt ctx.Γ ctx.criticalPath.firstStep
  let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
  let Y := VAt ctx.Γ ctx.criticalPath.a'
  let Qend := QAt ctx.Γ ctx.criticalPath.a'
  obtain ⟨_, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hb2 : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hYmiddle : Y ≤ QAt ctx.Γ middle :=
    (show Y ≤ GeneratedNeighborhoodV ctx.Γ middle from
      le_sSup ⟨_, (mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal, rfl⟩).trans
      (nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hb2 middle)
  have hYP : Y ≤ P := hYmiddle.trans
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core middle ctx.criticalPath.firstStep
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2
  have hZQ : Z ≤ Qend := by
    apply critical_minimality ctx.Γ ctx.criticalPath
    have hdist := ctx.Γ.distance_le_of_path 2
      ![ctx.criticalPath.firstStep, middle, ctx.criticalPath.a'] (by
        intro step
        fin_cases step
        · exact ctx.Γ.adjacent_symm hfirst
        · exact hterminal)
    change ctx.Γ.distance ctx.criticalPath.firstStep ctx.criticalPath.a' ≤ 2 at hdist
    rw [ctx.critical_length]
    omega
  obtain ⟨hN, hW, action, haction, hkernel⟩ := nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hb ctx.criticalPath.firstStep ⟨1, ctx.Γ.act_one _⟩
  let _ := hN
  let _ := hW
  let W := V ⧸ Z.subgroupOf V
  let q : V →* W := QuotientGroup.mk' (Z.subgroupOf V)
  let R : Subgroup W := (Qend.subgroupOf V).map q
  have hR : R ≠ ⊤ := by
    intro heq
    apply (sectionTenOpeningData ctx middle hpath).first_noncontainment
    intro vector hvector
    have hmem : q ⟨vector, hvector⟩ ∈ R := heq ▸ Subgroup.mem_top _
    obtain ⟨preimage, hpreimage, hsame⟩ := hmem
    have hd : preimage / (⟨vector, hvector⟩ : V) ∈ Z.subgroupOf V :=
      QuotientGroup.eq_iff_div_mem.mp hsame
    have hvectorQ := Qend.mul_mem (Qend.inv_mem (hZQ hd)) hpreimage
    change ((preimage : G) / vector)⁻¹ * (preimage : G) ∈ Qend at hvectorQ
    simpa [div_eq_mul_inv, mul_assoc] using hvectorQ
  let Ynative := Y.subgroupOf P
  have hYtwo : IsPGroup 2 Y := by
    let _ : IsElementaryAbelian 2 Y :=
      (nine_three_second_extraction_inputs ctx.toLocalContext.toSectionNineLocalContext hb).2.2.1
    exact IsElementaryAbelian.isPGroup 2 Y
  have hYnativeTwo : IsPGroup 2 Ynative :=
    hYtwo.of_equiv (Subgroup.subgroupOfEquivOfLe hYP).symm
  obtain ⟨sylow, hYsylow⟩ := hYnativeTwo.exists_le_sylow
  have hgenerate := nine_next_quotient_sylow_fixed_generation
    ctx.toAmbientSectionNineContext hb hN action haction sylow
  have hquad : ⁅⁅V, Y⁆, Y⁆ ≤ Z := by
    have hzero := ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
      ctx.commutator_eq).longer_case hb).2.2
    exact hzero.le.trans bot_le
  have hquadratic : IsQuadraticAction (Ynative.map action.rangeRestrict) W := by
    have hh := Subgroup.quotient_conjugation_quadratic_of_double_commutator_le
      P V Z Y (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep)
        hYP hN hquad action haction
    change commutatorAction₂ (Ynative.map action.rangeRestrict) W = ⊥
    rw [← commutatorAction₂_map_actor_subtype action.range (Ynative.map action.rangeRestrict),
      Subgroup.map_map]
    exact hh
  have hlocal := (edge_local_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2
  obtain ⟨Y₀, hY₀, hcount, hescape⟩ := SectionThree.pSet_quadratic_fixed_hyperplane_lift
    T P (sectionThreeHypotheses ctx.sectionSeven)
    ((pFamily_iff_pSet _ _ _).mp hlocal.1) hlocal.2 action hkernel.ge sylow
      hgenerate Ynative hYsylow hquadratic R hR
  obtain ⟨point, hpoint, hout⟩ := SetLike.not_le_iff_exists.mp hescape
  obtain ⟨actor, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf V) point
  have hactorOut : (actor : G) ∉ Qend := fun hx => hout (Subgroup.mem_map_of_mem q hx)
  let A₀ := Y₀.map P.subtype
  have hA₀Y : A₀ ≤ Y :=
    (Subgroup.map_mono hY₀).trans_eq (Subgroup.map_subgroupOf_eq_of_le hYP)
  have hcomm : ∀ element ∈ A₀, ⁅element, (actor : G)⁆ ∈ Z := by
    rintro element ⟨native, hnative, rfl⟩
    have hh := hpoint
      ⟨action.rangeRestrict native, Subgroup.mem_map_of_mem action.rangeRestrict hnative⟩
    change action native (q actor) = q actor at hh
    rw [haction] at hh
    have hd := QuotientGroup.eq_iff_div_mem.mp hh
    change (native : G) * (actor : G) * (native : G)⁻¹ / (actor : G) ∈ Z at hd
    change ⁅(native : G), (actor : G)⁆ ∈ Z
    simpa only [commutatorElement_def, div_eq_mul_inv] using hd
  have hcountA : Nat.card A₀ = Nat.card Y₀ := Subgroup.card_map_of_injective P.subtype_injective
  have hcountY : Nat.card Ynative = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYP).toEquiv
  rw [hcountY, ← hcountA] at hcount
  have hcoreP : QAt ctx.Γ ctx.criticalPath.firstStep ≤ P := by
    rw [QAt, CosetGraphContext.q, ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hactorP : (actor : G) ∈ P := hcoreP
    (neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath hb _ actor.property)
  exact ⟨actor, actor.property, hactorOut, A₀, hA₀Y, hcount,
    commutator_zpowers_le A₀ Z actor
      (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.firstStep hactorP) hcomm⟩

public theorem ten_one_small_commutator_actor
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    ∃ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep ∧
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' ∧
      (Nat.card (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ : Subgroup G) = 2 ∨
        Nat.card (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ : Subgroup G) = 4 ∧
          ZAt ctx.Γ ctx.criticalPath.firstStep ≤
            ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆) := by
  obtain ⟨actor, hactor, hout, A₀, hA₀, hindex, hcomm⟩ :=
    ten_one_fixed_hyperplane_actor ctx middle hpath
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case hb).1
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a') :=
    (nine_three_second_extraction_inputs ctx.toLocalContext.toSectionNineLocalContext hb).2.2.1
  have hinvolution : actor ≠ 1 ∧ actor ^ 2 = 1 :=
    ⟨fun heq => hout (heq ▸ (QAt ctx.Γ ctx.criticalPath.a').one_mem),
      elemPow_eq_one_of_isElementaryAbelian _ hactor⟩
  have hnormal : Subgroup.zpowers actor ≤
      Subgroup.normalizer (VAt ctx.Γ ctx.criticalPath.a' : Set G) :=
    (Subgroup.zpowers_le.mpr
      ((lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2 hactor)).trans
        (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a')
  have hfour := (lemma_nine_three_ambient ctx.toAmbientSectionNineContext hb
    ctx.criticalPath.a ⟨1, ctx.Γ.act_one _⟩).2
  have hline := nine_next_center_order_of_initial_four
    ctx.toLocalContext.toSectionNineLocalContext hfour
  obtain ⟨hbound, hcontain⟩ := Subgroup.commutator_card_le_four_of_index_two_small_layer
    (VAt ctx.Γ ctx.criticalPath.a') A₀ (ZAt ctx.Γ ctx.criticalPath.firstStep) actor
    hinvolution hnormal hA₀ hindex hcomm hline
  let D := ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆
  have hDne : D ≠ ⊥ := by
    intro hbot
    have hcent : Subgroup.zpowers actor ≤
        Subgroup.centralizer (VAt ctx.Γ ctx.criticalPath.a' : Set G) :=
      Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
    exact hout ((sectionTenOpeningData ctx middle hpath).endpoint_centralizer
      (hcent (Subgroup.mem_zpowers actor)))
  have hDU : D ≤ VAt ctx.Γ ctx.criticalPath.a' :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hnormal
  have hDtwo : IsPGroup 2 D :=
    (IsElementaryAbelian.isPGroup 2 (VAt ctx.Γ ctx.criticalPath.a')).to_le hDU
  have heven : 2 ∣ Nat.card D := hDtwo.card_eq_or_dvd.resolve_left
    (fun hone => hDne (Subgroup.card_eq_one.mp hone))
  have hpos := (Subgroup.one_lt_card_iff_ne_bot D).mpr hDne
  refine ⟨actor, hactor, hout, ?_⟩
  by_cases htwo : Nat.card D = 2
  · exact Or.inl htwo
  · have hcard : Nat.card D = 4 := by
      obtain ⟨factor, hfactor⟩ := heven
      change Nat.card D ≤ 4 at hbound
      omega
    exact Or.inr ⟨hcard, hcontain hcard⟩

open scoped IsMulCommutative

public theorem ten_one_quotient_commutator_actor
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    ∃ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep ∧
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' ∧
      (QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2 ∨
        QuotientCardEq
          (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
            ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 4 ∧
          ZAt ctx.Γ ctx.criticalPath.firstStep ≤
            ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆) := by
  obtain ⟨actor, hactor, hout, hcase⟩ := ten_one_small_commutator_actor ctx middle hpath
  let D := ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆
  let Z := ZAt ctx.Γ ctx.criticalPath.a'
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  obtain ⟨mover, _, hmover⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hdata := nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext hb
    ctx.criticalPath.a' ⟨mover, hmover⟩
  have hactorP : actor ∈ GAt ctx.Γ ctx.criticalPath.a' :=
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2 hactor
  have hnot : ¬ D ≤ Z := fun hle => hout ((hdata.2.2 actor hactorP).mp hle)
  have hZcard : Nat.card Z = 2 := hdata.1
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a') :=
    (nine_three_second_extraction_inputs ctx.toLocalContext.toSectionNineLocalContext hb).2.2.1
  have hDU : D ≤ VAt ctx.Γ ctx.criticalPath.a' :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.zpowers_le.mpr hactorP).trans
        (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a'))
  have hZU : Z ≤ VAt ctx.Γ ctx.criticalPath.a' := by
    dsimp only [Z]
    rw [← hdata.2.1]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((show QAt ctx.Γ ctx.criticalPath.a' ≤ GAt ctx.Γ ctx.criticalPath.a' from by
        rw [QAt, q, ctx.Γ.twoCoreAt_def]; exact twoCoreIn_le _).trans
          (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a'))
  have hnorm : Z ≤ Subgroup.normalizer (D : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro element helement
    rw [Subgroup.mem_centralizer_iff]
    intro other hother
    exact congrArg Subtype.val (mul_comm
      (⟨other, hDU hother⟩ : VAt ctx.Γ ctx.criticalPath.a')
      (⟨element, hZU helement⟩ : VAt ctx.Γ ctx.criticalPath.a'))
  have hjoin := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes D Z hnorm
  have hinf := Subgroup.card_dvd_of_le (show D ⊓ Z ≤ Z from inf_le_right)
  rw [hZcard] at hinf
  have hquotne : Nat.card (D ⊔ Z : Subgroup G) ≠ Nat.card Z := by
    intro heq
    exact hnot ((show D ≤ D ⊔ Z from le_sup_left).trans
      (Subgroup.eq_of_le_of_card_ge le_sup_right heq.le).ge)
  refine ⟨actor, hactor, hout, ?_⟩
  change QuotientCardEq (D ⊔ Z) Z 2 ∨
    QuotientCardEq (D ⊔ Z) Z 4 ∧ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ D
  rcases (Nat.dvd_prime Nat.prime_two).mp hinf with hone | htwo
  · rw [hone, one_mul, hZcard] at hjoin
    rcases hcase with hcard | ⟨hcard, hcontain⟩
    · apply Or.inl
      change Nat.card (D ⊔ Z : Subgroup G) = 2 * Nat.card Z
      change Nat.card D = 2 at hcard
      rw [hZcard, ← hjoin, hcard]
    · refine Or.inr ⟨?_, hcontain⟩
      change Nat.card (D ⊔ Z : Subgroup G) = 4 * Nat.card Z
      change Nat.card D = 4 at hcard
      rw [hZcard, ← hjoin, hcard]
  · rw [htwo, hZcard] at hjoin
    rcases hcase with hcard | ⟨hcard, _⟩
    · change Nat.card D = 2 at hcard
      rw [hZcard] at hquotne
      omega
    · apply Or.inl
      change Nat.card (D ⊔ Z : Subgroup G) = 2 * Nat.card Z
      change Nat.card D = 4 at hcard
      rw [hZcard]
      omega


end Stellmacher.SectionTen
