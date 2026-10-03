module

public import Stellmacher.SectionNine.NineSevenCommutatorCenters
public import Stellmacher.SectionNine.NineSevenCenterLines

/-!
# The length-seven center witnesses in (9.7)

The middle module intersection puts the common order-two subgroup in the
offset-four center. Distinct order-four neighbor centers at offsets three
and five intersect in their respective order-two vertex centers. This
identifies the subgroup with both of those centers without identifying
arbitrary existential neighbor witnesses with path vertices.

The general geometric statement applies to every order-two subgroup in the
offset-two and offset-six centers. The final theorem specializes it to the
actual terminal-module/initial-center commutator, obtaining its order and
containments from the established commutator-center theorem.

Source: Stellmacher (9.7), printed p.53 / PDF p.43 of
`refs/files/stellmacher-n-group.pdf`, the paragraph beginning with b = 7.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

private theorem path_even_shift_conjugate
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (start steps : ℕ)
    (hbound : start + 2 * steps ≤ ctx.criticalPath.length) :
    IsConjugateVertex ctx.Γ
      (ctx.criticalPath.path ⟨start, by omega⟩)
      (ctx.criticalPath.path ⟨start + 2 * steps, by omega⟩) := by
  induction steps with
  | zero =>
    exact ⟨1, by simpa using ctx.Γ.act_one (ctx.criticalPath.path ⟨start, by omega⟩)⟩
  | succ steps ih =>
    obtain ⟨first, hfirst⟩ := ih (by omega)
    have hleft := ctx.criticalPath.path_adj ⟨start + 2 * steps, by omega⟩
    have hright := ctx.criticalPath.path_adj ⟨start + 2 * steps + 1, by omega⟩
    obtain ⟨second, hsecond⟩ :=
      (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
        (ctx.criticalPath.path ⟨start + 2 * steps + 1, by omega⟩)
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hleft))
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hright)
    refine ⟨first * (second : G), ?_⟩
    rw [ctx.Γ.act_mul, hfirst]
    convert hsecond using 1 <;> congr 1

private theorem initial_orbit_of_even_offset
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (offset : ℕ)
    (hbound : offset ≤ ctx.criticalPath.length) (heven : Even offset) :
    IsConjugateVertex ctx.Γ ctx.criticalPath.a
      (ctx.criticalPath.path ⟨offset, by omega⟩) := by
  obtain ⟨half, hhalf⟩ := heven
  have horbit := path_even_shift_conjugate ctx 0 half (by omega)
  have hnum : 2 * half = offset := by
    omega
  have hpath0 : ctx.criticalPath.path ⟨0, by omega⟩ = ctx.criticalPath.a :=
    ctx.criticalPath.path_start
  rw [hpath0] at horbit
  have horbit' : IsConjugateVertex ctx.Γ ctx.criticalPath.a
      (ctx.criticalPath.path ⟨offset, by omega⟩) := by
    simpa [hnum] using horbit
  exact horbit'

private theorem model_of_conjugate_vertex
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) {source target : Γ.Vertex}
    (horbit : IsConjugateVertex Γ source target)
    (hmodel : QuotientIsModel (GAt Γ source) (QAt Γ source) SL2Two) :
    QuotientIsModel (GAt Γ target) (QAt Γ target) SL2Two := by
  obtain ⟨actor, rfl⟩ := horbit
  obtain ⟨projection, hsurj, hker⟩ := hmodel
  change QuotientIsModel (stabilizer Γ (Γ.act actor source))
    (q Γ (Γ.act actor source)) SL2Two
  rw [stabilizer_act, q_act]
  let equiv := (GAt Γ source).equivMapOfInjective
    (MulAut.conj actor⁻¹).toMonoidHom (MulAut.conj actor⁻¹).injective
  refine ⟨projection.comp equiv.symm.toMonoidHom,
    hsurj.comp equiv.symm.surjective, ?_⟩
  ext point
  change projection (equiv.symm point) = 1 ↔
    (point : G) ∈ (QAt Γ source).map (MulAut.conj actor⁻¹).toMonoidHom
  rw [← MonoidHom.mem_ker, hker, Subgroup.mem_map_equiv]
  have heq : (equiv.symm point : G) = (MulAut.conj actor⁻¹).symm (point : G) := by
    apply (MulAut.conj actor⁻¹).injective
    change (equiv (equiv.symm point) : G) = _
    simp only [MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val (equiv.apply_symm_apply point)
  change (equiv.symm point : G) ∈ QAt Γ source ↔ _
  rw [heq]

private theorem module_card_of_conjugate_vertex
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) {source target : Γ.Vertex}
    (horbit : IsConjugateVertex Γ source target) :
    Nat.card (VAt Γ target) = Nat.card (VAt Γ source) := by
  obtain ⟨actor, rfl⟩ := horbit
  change Nat.card (v Γ (Γ.act actor source)) = Nat.card (v Γ source)
  rw [v_act, Subgroup.card_map_of_injective (MulAut.conj actor⁻¹).injective]

public theorem nine_seven_length_seven_witness_selection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (third : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hindex : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2)
    (hfirstCard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 2^3)
    (hfirstModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hstartData : ∀ vertex, IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex →
      QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two ∧
        Nat.card (ZAt ctx.Γ vertex) = 4)
    (hseven : ctx.criticalPath.length = 7)
    (R : Subgroup G) (hRcard : Nat.card R = 2)
    (hRsecond : R ≤ ZAt ctx.Γ (ctx.criticalPath.path ⟨2, by omega⟩))
    (hRsixth : R ≤ ZAt ctx.Γ (ctx.criticalPath.path ⟨6, by omega⟩)) :
    R = ZAt ctx.Γ (ctx.criticalPath.path ⟨3, by omega⟩) ∧
      R = ZAt ctx.Γ (ctx.criticalPath.path ⟨5, by omega⟩) := by
  let vertices : Fin 8 → ctx.Γ.Vertex := fun index =>
    ctx.criticalPath.path ⟨index.val, by omega⟩
  have hadj (index : Fin 7) : ctx.Γ.adjacent
      (vertices index.castSucc) (vertices index.succ) :=
    ctx.criticalPath.path_adj ⟨index.val, by omega⟩
  have hstart : vertices 0 = ctx.criticalPath.a := ctx.criticalPath.path_start
  have hfirst : vertices 1 = ctx.criticalPath.firstStep := ctx.criticalPath.path_first
  have hend : vertices 7 = ctx.criticalPath.a' := by
    convert ctx.criticalPath.path_end using 1
    exact congrArg ctx.criticalPath.path (Fin.ext hseven.symm)
  have hnoShort (shortened : Fin 6 → ctx.Γ.Vertex)
      (hleft : shortened 0 = vertices 0) (hright : shortened 5 = vertices 7)
      (hwalk : ∀ index : Fin 5, ctx.Γ.adjacent
        (shortened index.castSucc) (shortened index.succ)) : False := by
    have hdist := ctx.Γ.distance_le_of_path 5 shortened hwalk
    change ctx.Γ.distance (shortened 0) (shortened 5) ≤ 5 at hdist
    rw [hleft, hright, hstart, hend, ctx.criticalPath.endpoint_distance, hseven] at hdist
    omega
  have htwoFour : vertices 2 ≠ vertices 4 := by
    intro heq
    apply hnoShort ![vertices 0, vertices 1, vertices 2, vertices 5, vertices 6, vertices 7]
      rfl rfl
    intro index
    fin_cases index
    · exact hadj 0
    · exact hadj 1
    · change ctx.Γ.adjacent (vertices 2) (vertices 5)
      rw [heq]
      exact hadj 4
    · exact hadj 5
    · exact hadj 6
  have hfourSix : vertices 4 ≠ vertices 6 := by
    intro heq
    apply hnoShort ![vertices 0, vertices 1, vertices 2, vertices 3, vertices 4, vertices 7]
      rfl rfl
    intro index
    fin_cases index
    · exact hadj 0
    · exact hadj 1
    · exact hadj 2
    · exact hadj 3
    · change ctx.Γ.adjacent (vertices 4) (vertices 7)
      rw [heq]
      exact hadj 6
  have heven (index : Fin 8) (heven : Even index.val) :
      IsConjugateVertex ctx.Γ ctx.criticalPath.a (vertices index) :=
    initial_orbit_of_even_offset ctx.toLocalContext index.val (by
      change index.val ≤ ctx.criticalPath.length
      omega) heven
  have htwoOrbit := heven 2 ⟨1, rfl⟩
  have hfourOrbit := heven 4 ⟨2, rfl⟩
  have hsixOrbit := heven 6 ⟨3, rfl⟩
  have hodd (steps : ℕ) (hbound : 1 + 2 * steps ≤ 7) :
      IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep
        (ctx.criticalPath.path ⟨1 + 2 * steps, by omega⟩) := by
    have horbit := path_even_shift_conjugate ctx.toLocalContext 1 steps (by
      change 1 + 2 * steps ≤ ctx.criticalPath.length
      omega)
    change IsConjugateVertex ctx.Γ (vertices 1) _ at horbit
    rwa [hfirst] at horbit
  have hthreeOrbit := hodd 1 (by omega)
  have hfiveOrbit := hodd 2 (by omega)
  have hthreeModel := model_of_conjugate_vertex ctx.Γ hthreeOrbit hfirstModel
  have hfiveModel := model_of_conjugate_vertex ctx.Γ hfiveOrbit hfirstModel
  have hthreeCard : Nat.card (VAt ctx.Γ (vertices 3)) = 8 :=
    (module_card_of_conjugate_vertex ctx.Γ hthreeOrbit).trans hfirstCard
  have hfiveCard : Nat.card (VAt ctx.Γ (vertices 5)) = 8 :=
    (module_card_of_conjugate_vertex ctx.Γ hfiveOrbit).trans hfirstCard
  have htwoCard := (hstartData _ htwoOrbit).2
  have hfourCard := (hstartData _ hfourOrbit).2
  have hsixCard := (hstartData _ hsixOrbit).2
  have htwoLines := nine_seven_center_lines ctx (by omega) hfirstModel hstartData
    (vertices 2) htwoOrbit
  have hfourLines := nine_seven_center_lines ctx (by omega) hfirstModel hstartData
    (vertices 4) hfourOrbit
  have hsixLines := nine_seven_center_lines ctx (by omega) hfirstModel hstartData
    (vertices 6) hsixOrbit
  have hthreeTwo := htwoLines.1 (vertices 3)
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (hadj 2))
  have hthreeFour := hfourLines.1 (vertices 3)
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm (hadj 3)))
  have hfiveFour := hfourLines.1 (vertices 5)
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (hadj 4))
  have hfiveSix := hsixLines.1 (vertices 5)
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm (hadj 5)))
  have htwoFourCenters := nine_seven_neighbor_centers_distinct ctx.sectionSeven ctx.Γ
    hthreeModel hthreeCard htwoCard (ctx.Γ.adjacent_symm (hadj 2)) (hadj 3) htwoFour
  have hfourSixCenters := nine_seven_neighbor_centers_distinct ctx.sectionSeven ctx.Γ
    hfiveModel hfiveCard hfourCard (ctx.Γ.adjacent_symm (hadj 4)) (hadj 5) hfourSix
  have hleftIntersection := nine_seven_distinct_planes_inf_eq_line htwoCard hfourCard
    htwoFourCenters hthreeTwo.1 (le_inf hthreeTwo.2 hthreeFour.2)
  have hrightIntersection := nine_seven_distinct_planes_inf_eq_line hfourCard hsixCard
    hfourSixCenters hfiveFour.1 (le_inf hfiveFour.2 hfiveSix.2)
  have hmiddle := nine_seven_length_seven_middle_intersection ctx.toLocalContext
    third hpath hindex hfirstCard hstartData hseven
  change VAt ctx.Γ (vertices 3) ⊓ VAt ctx.Γ (vertices 5) =
    ZAt ctx.Γ (vertices 4) at hmiddle
  have hRfour : R ≤ ZAt ctx.Γ (vertices 4) := by
    rw [← hmiddle]
    exact le_inf
      (hRsecond.trans (nine_seven_neighbor_center_le_module ctx.Γ
        (ctx.Γ.adjacent_symm (hadj 2))))
      (hRsixth.trans (nine_seven_neighbor_center_le_module ctx.Γ (hadj 5)))
  have hRthree : R ≤ ZAt ctx.Γ (vertices 3) :=
    (le_inf hRsecond hRfour).trans_eq hleftIntersection
  have hRfive : R ≤ ZAt ctx.Γ (vertices 5) :=
    (le_inf hRfour hRsixth).trans_eq hrightIntersection
  exact ⟨Subgroup.eq_of_le_of_card_ge hRthree (hthreeTwo.1.le.trans hRcard.ge),
    Subgroup.eq_of_le_of_card_ge hRfive (hfiveFour.1.le.trans hRcard.ge)⟩

public theorem nine_seven_b7_commutator_witness_selection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (third : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hindex : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2)
    (hfirstCard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 2^3)
    (hfirstModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hendCard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^3)
    (hendModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2Two)
    (hstartData : ∀ vertex, IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex →
      QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two ∧
        Nat.card (ZAt ctx.Γ vertex) = 4)
    (hseven : ctx.criticalPath.length = 7) :
    let R := ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆
    R = ZAt ctx.Γ (ctx.criticalPath.path ⟨3, by omega⟩) ∧
      R = ZAt ctx.Γ (ctx.criticalPath.path ⟨5, by omega⟩) := by
  obtain ⟨hcard, hsecond, hpenultimate⟩ := nine_seven_commutator_centers ctx
    (by omega) third hpath hindex hfirstCard hfirstModel hendCard hendModel hstartData
    (by omega)
  apply nine_seven_length_seven_witness_selection ctx third hpath hindex hfirstCard
    hfirstModel hstartData hseven _ hcard hsecond
  convert hpenultimate using 1
  exact congrArg (ZAt ctx.Γ) (congrArg ctx.criticalPath.path (Fin.ext (by
    dsimp only
    omega)))

end Stellmacher.SectionNine
