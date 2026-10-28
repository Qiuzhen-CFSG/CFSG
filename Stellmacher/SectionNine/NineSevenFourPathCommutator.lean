module

public import Stellmacher.SectionNine.NineSevenCommutatorGeometry
public import Stellmacher.SectionNine.NineSevenFourPathLocal

/-!
# The distance-five four-path commutator formula

The actual critical commutator is the middle order-two center: it lies in
two distinct order-four neighbor planes whose intersection is that center.
The two initial neighbor planes generate the first order-eight module, and
the terminal module centralizes the second plane. Four-path transitivity
and conjugation covariance then give the equality on every nonbacktracking
four-edge path starting in the first-step orbit.

Source: Stellmacher, printed pp.54–55 / PDF pp.44–45 of
`refs/files/stellmacher-n-group.pdf`, the distance-five paragraph of (9.7).
The graph group and ambient group remain distinct throughout.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement

universe u

private theorem commutator_sup_le_of_normalizes
    {G : Type u} [Group G] (left right actor bound : Subgroup G)
    (hnorm : left ⊔ right ≤ Subgroup.normalizer (bound : Set G))
    (hleft : ⁅actor, left⁆ ≤ bound) (hright : ⁅actor, right⁆ ≤ bound) :
    ⁅actor, left ⊔ right⁆ ≤ bound := by
  let good : Subgroup G :=
    { carrier := {point | point ∈ Subgroup.normalizer (bound : Set G) ∧
        ∀ mover ∈ actor, ⁅mover, point⁆ ∈ bound}
      one_mem' := ⟨(Subgroup.normalizer (bound : Set G)).one_mem, by simp⟩
      mul_mem' := by
        rintro first second ⟨hfirst, hfirstComm⟩ ⟨hsecond, hsecondComm⟩
        refine ⟨(Subgroup.normalizer (bound : Set G)).mul_mem hfirst hsecond, ?_⟩
        intro mover hmover
        rw [commutatorElement_mul_right_eq_mul_conj]
        rw [mul_assoc, mul_assoc, ← mul_assoc first]
        exact bound.mul_mem (hfirstComm mover hmover)
          ((Subgroup.mem_normalizer_iff.mp hfirst _).mp (hsecondComm mover hmover))
      inv_mem' := by
        rintro point ⟨hpoint, hcomm⟩
        refine ⟨(Subgroup.normalizer (bound : Set G)).inv_mem hpoint, ?_⟩
        intro mover hmover
        have heq : ⁅mover, point⁻¹⁆ = point⁻¹ * ⁅mover, point⁆⁻¹ * point := by
          simp only [commutatorElement_def]
          group
        rw [heq]
        simpa only [inv_inv] using
          (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (bound : Set G)).inv_mem hpoint) _).mp
              (bound.inv_mem (hcomm mover hmover)) }
  have hle : left ⊔ right ≤ good := by
    apply sup_le
    · intro point hpoint
      exact ⟨hnorm (Subgroup.mem_sup_left hpoint), fun mover hmover =>
        hleft (Subgroup.commutator_mem_commutator hmover hpoint)⟩
    · intro point hpoint
      exact ⟨hnorm (Subgroup.mem_sup_right hpoint), fun mover hmover =>
        hright (Subgroup.commutator_mem_commutator hmover hpoint)⟩
  exact Subgroup.commutator_le.mpr fun mover hmover point hpoint =>
    (hle hpoint).2 mover hmover

private theorem two_planes_sup_eq_eight
    {G : Type u} [Group G] [Finite G] {left right whole : Subgroup G}
    (hleft : left ≤ whole) (hright : right ≤ whole)
    (hleftCard : Nat.card left = 4) (hrightCard : Nat.card right = 4)
    (hwholeCard : Nat.card whole = 8) (hne : left ≠ right) : left ⊔ right = whole := by
  have hproper : left ≠ left ⊔ right := by
    intro heq
    exact hne (Subgroup.eq_of_le_of_card_ge
      (heq.ge.trans' le_sup_right) (by omega)).symm
  have hlt : 4 < Nat.card (left ⊔ right : Subgroup G) := by
    rw [← hleftCard]
    exact lt_of_le_of_ne (Subgroup.card_le_of_le le_sup_left) (fun heq =>
      hproper (Subgroup.eq_of_le_of_card_ge le_sup_left heq.ge))
  have hdvd := Subgroup.card_dvd_of_le (sup_le hleft hright)
  rw [hwholeCard] at hdvd
  have hcard : Nat.card (left ⊔ right : Subgroup G) = 8 := by
    obtain ⟨factor, hfactor⟩ := hdvd
    have hpos : 0 < factor := by nlinarith
    have hone : factor = 1 := by nlinarith
    simpa only [hone, mul_one] using hfactor.symm
  exact Subgroup.eq_of_le_of_card_ge (sup_le hleft hright) (by omega)

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

private theorem five_path_nonbacktracking
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (vertices : Fin 6 → Γ.Vertex)
    (hadj : ∀ index : Fin 5, Γ.adjacent (vertices index.castSucc) (vertices index.succ))
    (hdist : Γ.distance (vertices 0) (vertices 5) = 5) :
    ∀ index : Fin 4, vertices index.castSucc.castSucc ≠ vertices index.succ.succ := by
  have hnoShort (shortened : Fin 4 → Γ.Vertex)
      (hstart : shortened 0 = vertices 0) (hend : shortened 3 = vertices 5)
      (hwalk : ∀ index : Fin 3, Γ.adjacent
        (shortened index.castSucc) (shortened index.succ)) : False := by
    have hbound := Γ.distance_le_of_path 3 shortened hwalk
    change Γ.distance (shortened 0) (shortened 3) ≤ 3 at hbound
    rw [hstart, hend, hdist] at hbound
    omega
  intro index heq
  fin_cases index
  · change vertices 0 = vertices 2 at heq
    apply hnoShort ![vertices 0, vertices 3, vertices 4, vertices 5] rfl rfl
    intro step
    fin_cases step
    · change Γ.adjacent (vertices 0) (vertices 3)
      rw [heq]
      exact hadj 2
    · exact hadj 3
    · exact hadj 4
  · change vertices 1 = vertices 3 at heq
    apply hnoShort ![vertices 0, vertices 1, vertices 4, vertices 5] rfl rfl
    intro step
    fin_cases step
    · exact hadj 0
    · change Γ.adjacent (vertices 1) (vertices 4)
      rw [heq]
      exact hadj 3
    · exact hadj 4
  · change vertices 2 = vertices 4 at heq
    apply hnoShort ![vertices 0, vertices 1, vertices 2, vertices 5] rfl rfl
    intro step
    fin_cases step
    · exact hadj 0
    · exact hadj 1
    · change Γ.adjacent (vertices 2) (vertices 5)
      rw [heq]
      exact hadj 4
  · change vertices 3 = vertices 5 at heq
    apply hnoShort ![vertices 0, vertices 1, vertices 2, vertices 5] rfl rfl
    intro step
    fin_cases step
    · exact hadj 0
    · exact hadj 1
    · change Γ.adjacent (vertices 2) (vertices 5)
      rw [← heq]
      exact hadj 2

public theorem nine_seven_five_base_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
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
    (hfive : ctx.criticalPath.length = 5) :
    ⁅VAt ctx.Γ ctx.criticalPath.firstStep, VAt ctx.Γ ctx.criticalPath.a'⁆ =
      ZAt ctx.Γ (ctx.criticalPath.path ⟨3, by omega⟩) := by
  let vertices : Fin 6 → ctx.Γ.Vertex := fun index =>
    ctx.criticalPath.path ⟨index.val, by omega⟩
  have hadj (index : Fin 5) : ctx.Γ.adjacent
      (vertices index.castSucc) (vertices index.succ) :=
    ctx.criticalPath.path_adj ⟨index.val, by omega⟩
  have hstart : vertices 0 = ctx.criticalPath.a := ctx.criticalPath.path_start
  have hfirst : vertices 1 = ctx.criticalPath.firstStep := ctx.criticalPath.path_first
  have hend : vertices 5 = ctx.criticalPath.a' := by
    convert ctx.criticalPath.path_end using 1
    exact congrArg ctx.criticalPath.path (Fin.ext hfive.symm)
  have hback := five_path_nonbacktracking ctx.Γ vertices hadj
    (by rw [hstart, hend, ctx.criticalPath.endpoint_distance, hfive])
  have htwoOrbit : IsConjugateVertex ctx.Γ ctx.criticalPath.a (vertices 2) :=
    initial_orbit_of_even_offset ctx.toLocalContext 2
      (by change 2 ≤ ctx.criticalPath.length; omega) ⟨1, rfl⟩
  have hfourOrbit : IsConjugateVertex ctx.Γ ctx.criticalPath.a (vertices 4) :=
    initial_orbit_of_even_offset ctx.toLocalContext 4
      (by change 4 ≤ ctx.criticalPath.length; omega) ⟨2, rfl⟩
  have hthreeOrbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep (vertices 3) := by
    have horbit := path_even_shift_conjugate ctx.toLocalContext 1 1
      (by change 3 ≤ ctx.criticalPath.length; omega)
    change IsConjugateVertex ctx.Γ (vertices 1) (vertices 3) at horbit
    rwa [hfirst] at horbit
  have hthreeModel := model_of_conjugate_vertex ctx.Γ hthreeOrbit hfirstModel
  have hthreeCard : Nat.card (VAt ctx.Γ (vertices 3)) = 8 :=
    (module_card_of_conjugate_vertex ctx.Γ hthreeOrbit).trans hfirstCard
  have htwoCard := (hstartData _ htwoOrbit).2
  have hfourCard := (hstartData _ hfourOrbit).2
  have htwoLines := nine_seven_center_lines ctx hb hfirstModel hstartData _ htwoOrbit
  have hfourLines := nine_seven_center_lines ctx hb hfirstModel hstartData _ hfourOrbit
  have hthreeTwo := htwoLines.1 (vertices 3)
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (hadj 2))
  have hthreeFour := hfourLines.1 (vertices 3)
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm (hadj 3)))
  have hdistinct := nine_seven_neighbor_centers_distinct ctx.sectionSeven ctx.Γ
    hthreeModel hthreeCard htwoCard (ctx.Γ.adjacent_symm (hadj 2)) (hadj 3) (hback 2)
  have hinf := nine_seven_distinct_planes_inf_eq_line htwoCard hfourCard hdistinct
    hthreeTwo.1 (le_inf hthreeTwo.2 hthreeFour.2)
  obtain ⟨hRcard, hRtwo, hRfour, _⟩ := nine_seven_commutator_geometry ctx hb third
    hpath hindex hfirstCard hfirstModel hendCard hendModel hstartData (by omega)
  let bound := ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆
  have hRle : bound ≤ ZAt ctx.Γ (vertices 2) ⊓ ZAt ctx.Γ (vertices 4) := by
    refine le_inf hRtwo ?_
    convert hRfour using 1
    exact congrArg (fun index => ZAt ctx.Γ (ctx.criticalPath.path index))
      (Fin.ext (by dsimp; omega))
  have hReq : bound = ZAt ctx.Γ (vertices 3) :=
    Subgroup.eq_of_le_of_card_ge (hRle.trans hinf.le)
      (by change Nat.card (ZAt ctx.Γ (vertices 3)) ≤ Nat.card
            (⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
          rw [hthreeTwo.1, hRcard])
  have hzeroCard := (hstartData _ ⟨1, ctx.Γ.act_one _⟩).2
  have hzeroLe : ZAt ctx.Γ ctx.criticalPath.a ≤ VAt ctx.Γ ctx.criticalPath.firstStep :=
    nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj)
  have htwoLe : ZAt ctx.Γ (vertices 2) ≤ VAt ctx.Γ ctx.criticalPath.firstStep := by
    rw [← hfirst]
    exact nine_seven_neighbor_center_le_module ctx.Γ (hadj 1)
  have hzeroTwo : ZAt ctx.Γ ctx.criticalPath.a ≠ ZAt ctx.Γ (vertices 2) := by
    apply nine_seven_neighbor_centers_distinct ctx.sectionSeven ctx.Γ hfirstModel
      hfirstCard hzeroCard (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj)
      (by rw [← hfirst]; exact hadj 1)
    rw [← hstart]
    exact hback 0
  have hsup := two_planes_sup_eq_eight hzeroLe htwoLe hzeroCard htwoCard hfirstCard hzeroTwo
  have hcentral : VAt ctx.Γ ctx.criticalPath.a' ≤
      Subgroup.centralizer (ZAt ctx.Γ (vertices 2) : Set G) := by
    have hcenter := (lemma_seven_three ctx.sectionSeven ctx.Γ).center_core
      (vertices 2) (vertices 3) ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (hadj 2))
    exact (nine_three_second_extraction_inputs ctx.toLocalContext hb).2.1.trans
      (Subgroup.le_centralizer_iff.mp (hcenter.trans
        ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))))
  have hRfirst : bound ≤ VAt ctx.Γ ctx.criticalPath.firstStep :=
    (hRle.trans inf_le_left).trans htwoLe
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case hb).1
  have hnorm : VAt ctx.Γ ctx.criticalPath.firstStep ≤ Subgroup.normalizer (bound : Set G) :=
    ((Subgroup.le_centralizer (H := VAt ctx.Γ ctx.criticalPath.firstStep)).trans
      (Subgroup.centralizer_le hRfirst)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hbound := commutator_sup_le_of_normalizes
    (ZAt ctx.Γ ctx.criticalPath.a) (ZAt ctx.Γ (vertices 2))
    (VAt ctx.Γ ctx.criticalPath.a') bound (hsup.le.trans hnorm) le_rfl
    ((Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral).le.trans bot_le)
  rw [hsup] at hbound
  have heq : ⁅VAt ctx.Γ ctx.criticalPath.a', VAt ctx.Γ ctx.criticalPath.firstStep⁆ = bound :=
    le_antisymm hbound (Subgroup.commutator_mono le_rfl hzeroLe)
  rw [Subgroup.commutator_comm, heq, hReq]
  rfl

private theorem commutator_formula_act
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (actor : G) (path : Fin 5 → Γ.Vertex)
    (heq : ⁅VAt Γ (path 0), VAt Γ (path 4)⁆ = ZAt Γ (path 2)) :
    ⁅VAt Γ (Γ.act actor (path 0)), VAt Γ (Γ.act actor (path 4))⁆ =
      ZAt Γ (Γ.act actor (path 2)) := by
  have hmap := congrArg
    (fun subgroup : Subgroup G => subgroup.map (MulAut.conj actor⁻¹).toMonoidHom) heq
  rw [Subgroup.map_commutator] at hmap
  change ⁅(v Γ (path 0)).map _, (v Γ (path 4)).map _⁆ = (z Γ (path 2)).map _ at hmap
  rwa [← v_act, ← v_act, ← z_act] at hmap

public theorem nine_seven_four_path_commutator_transport
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hfirstModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hstartModels : ∀ vertex, IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex →
      QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two)
    (first second : Fin 5 → ctx.Γ.Vertex)
    (hfirst : first 0 = ctx.criticalPath.firstStep)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep (second 0))
    (hfirstadj : ∀ index : Fin 4,
      ctx.Γ.adjacent (first index.castSucc) (first index.succ))
    (hsecondadj : ∀ index : Fin 4,
      ctx.Γ.adjacent (second index.castSucc) (second index.succ))
    (hfirstback : ∀ index : Fin 3,
      first index.castSucc.castSucc ≠ first index.succ.succ)
    (hsecondback : ∀ index : Fin 3,
      second index.castSucc.castSucc ≠ second index.succ.succ)
    (heq : ⁅VAt ctx.Γ (first 0), VAt ctx.Γ (first 4)⁆ = ZAt ctx.Γ (first 2)) :
    ⁅VAt ctx.Γ (second 0), VAt ctx.Γ (second 4)⁆ = ZAt ctx.Γ (second 2) := by
  obtain ⟨mover, hmover⟩ := horbit
  let target : Fin 5 → ctx.Γ.Vertex := fun index => ctx.Γ.act mover⁻¹ (second index)
  have hundo (index : Fin 5) : ctx.Γ.act mover (target index) = second index := by
    dsimp [target]
    rw [← ctx.Γ.act_mul, inv_mul_cancel, ctx.Γ.act_one]
  have htarget : target 0 = ctx.criticalPath.firstStep := by
    dsimp [target]
    rw [← hmover, ← ctx.Γ.act_mul, mul_inv_cancel, ctx.Γ.act_one]
  have htargetadj (index : Fin 4) : ctx.Γ.adjacent
      (target index.castSucc) (target index.succ) :=
    adjacent_act ctx.Γ mover⁻¹ (hsecondadj index)
  have htargetback (index : Fin 3) :
      target index.castSucc.castSucc ≠ target index.succ.succ := by
    intro hequal
    apply hsecondback index
    have hmap := congrArg (ctx.Γ.act mover) hequal
    simpa only [hundo] using hmap
  obtain ⟨actor, hactor⟩ :=
    (nineSeven_cubic_four_path_transitivity_local ctx hfirstModel hstartModels).2
      first target hfirst htarget hfirstadj htargetadj hfirstback htargetback
  have htargetEq := commutator_formula_act ctx.Γ (actor : G) first heq
  rw [hactor 0, hactor 4, hactor 2] at htargetEq
  have hfinal := commutator_formula_act ctx.Γ mover target htargetEq
  simpa only [hundo] using hfinal

public theorem nine_seven_four_path_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
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
    (hfive : ctx.criticalPath.length = 5)
    (path : Fin 5 → ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep (path 0))
    (hadj : ∀ index : Fin 4, ctx.Γ.adjacent (path index.castSucc) (path index.succ))
    (hback : ∀ index : Fin 3, path index.castSucc.castSucc ≠ path index.succ.succ) :
    ⁅VAt ctx.Γ (path 0), VAt ctx.Γ (path 4)⁆ = ZAt ctx.Γ (path 2) := by
  let vertices : Fin 6 → ctx.Γ.Vertex := fun index =>
    ctx.criticalPath.path ⟨index.val, by omega⟩
  have hverticesAdj (index : Fin 5) : ctx.Γ.adjacent
      (vertices index.castSucc) (vertices index.succ) :=
    ctx.criticalPath.path_adj ⟨index.val, by omega⟩
  have hstart : vertices 0 = ctx.criticalPath.a := ctx.criticalPath.path_start
  have hfirst : vertices 1 = ctx.criticalPath.firstStep := ctx.criticalPath.path_first
  have hend : vertices 5 = ctx.criticalPath.a' := by
    convert ctx.criticalPath.path_end using 1
    exact congrArg ctx.criticalPath.path (Fin.ext hfive.symm)
  have hverticesBack := five_path_nonbacktracking ctx.Γ vertices hverticesAdj
    (by rw [hstart, hend, ctx.criticalPath.endpoint_distance, hfive])
  let base : Fin 5 → ctx.Γ.Vertex := fun index => vertices index.succ
  have hbaseAdj (index : Fin 4) : ctx.Γ.adjacent
      (base index.castSucc) (base index.succ) := hverticesAdj index.succ
  have hbaseBack (index : Fin 3) :
      base index.castSucc.castSucc ≠ base index.succ.succ := hverticesBack index.succ
  have hbaseEq : ⁅VAt ctx.Γ (base 0), VAt ctx.Γ (base 4)⁆ = ZAt ctx.Γ (base 2) := by
    change ⁅VAt ctx.Γ (vertices 1), VAt ctx.Γ (vertices 5)⁆ = ZAt ctx.Γ (vertices 3)
    rw [hfirst, hend]
    exact nine_seven_five_base_commutator ctx hb third hpath hindex hfirstCard
      hfirstModel hendCard hendModel hstartData hfive
  exact nine_seven_four_path_commutator_transport ctx.toLocalContext hfirstModel
    (fun vertex hvertex => (hstartData vertex hvertex).1) base path hfirst horbit
    hbaseAdj hadj hbaseBack hback hbaseEq

end Stellmacher.SectionNine
