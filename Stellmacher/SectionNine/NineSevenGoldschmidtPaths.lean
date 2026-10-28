module

public import Stellmacher.SectionNine.NineSevenGoldschmidtTransport
public import Stellmacher.SectionNine.NineSevenShiftedIntersections

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

variable {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}

public theorem goldschmidt_neighbor_other
    (Γ : CosetGraphContext G T A B) (vertex previous : Γ.Vertex)
    (hdegree : Nat.card {neighbor // Γ.adjacent vertex neighbor} = 3) :
    ∃ next, Γ.adjacent vertex next ∧ next ≠ previous := by
  by_contra! hnone
  have hsub : Subsingleton {neighbor // Γ.adjacent vertex neighbor} :=
    ⟨fun left right => Subtype.ext ((hnone left left.property).trans
      (hnone right right.property).symm)⟩
  let := hsub
  have hcard : Nat.card {neighbor // Γ.adjacent vertex neighbor} ≤ 1 := by
    simpa using Nat.card_le_card_of_injective
      (fun _ : {neighbor // Γ.adjacent vertex neighbor} => ())
      (fun _ _ _ => Subsingleton.elim _ _)
  omega

public theorem goldschmidt_four_path_extend
    (Γ : CosetGraphContext G T A B)
    (hdegree : ∀ vertex, Nat.card {neighbor // Γ.adjacent vertex neighbor} = 3)
    (path : Fin 5 → Γ.Vertex)
    (hadj : ∀ index : Fin 4, Γ.adjacent (path index.castSucc) (path index.succ))
    (hback : ∀ index : Fin 3,
      path index.castSucc.castSucc ≠ path index.succ.succ) :
    ∃ extended : Fin 7 → Γ.Vertex,
      (∀ index : Fin 5, extended ⟨index.val, by omega⟩ = path index) ∧
      (∀ index : Fin 6, Γ.adjacent (extended index.castSucc) (extended index.succ)) ∧
      (∀ index : Fin 5,
        extended index.castSucc.castSucc ≠ extended index.succ.succ) := by
  obtain ⟨sixth, hsixth, hsixthNe⟩ := goldschmidt_neighbor_other Γ (path 4) (path 3)
    (hdegree (path 4))
  obtain ⟨seventh, hseventh, hseventhNe⟩ := goldschmidt_neighbor_other Γ sixth (path 4)
    (hdegree sixth)
  refine ⟨![path 0, path 1, path 2, path 3, path 4, sixth, seventh], ?_, ?_, ?_⟩
  · intro index
    fin_cases index <;> rfl
  · intro index
    fin_cases index
    · exact hadj 0
    · exact hadj 1
    · exact hadj 2
    · exact hadj 3
    · exact hsixth
    · exact hseventh
  · intro index
    fin_cases index
    · exact hback 0
    · exact hback 1
    · exact hback 2
    · exact hsixthNe.symm
    · exact hseventhNe.symm

public theorem goldschmidt_five_path_nonbacktracking
    (Γ : CosetGraphContext G T A B) (path : Fin 6 → Γ.Vertex)
    (hadj : ∀ index : Fin 5, Γ.adjacent (path index.castSucc) (path index.succ))
    (hdistance : Γ.distance (path 0) (path 5) = 5) :
    ∀ index : Fin 4, path index.castSucc.castSucc ≠ path index.succ.succ := by
  have hshort (short : Fin 4 → Γ.Vertex)
      (hshortadj : ∀ index : Fin 3,
        Γ.adjacent (short index.castSucc) (short index.succ))
      (hstart : short 0 = path 0) (hend : short 3 = path 5) : False := by
    have hbound := Γ.distance_le_of_path 3 short hshortadj
    change Γ.distance (short 0) (short 3) ≤ 3 at hbound
    rw [hstart, hend, hdistance] at hbound
    omega
  intro index heq
  fin_cases index
  · change path 0 = path 2 at heq
    apply hshort ![path 0, path 3, path 4, path 5] _ rfl rfl
    intro index
    fin_cases index
    · change Γ.adjacent (path 0) (path 3)
      rw [heq]
      exact hadj 2
    · exact hadj 3
    · exact hadj 4
  · change path 1 = path 3 at heq
    apply hshort ![path 0, path 1, path 4, path 5] _ rfl rfl
    intro index
    fin_cases index
    · exact hadj 0
    · change Γ.adjacent (path 1) (path 4)
      rw [heq]
      exact hadj 3
    · exact hadj 4
  · change path 2 = path 4 at heq
    apply hshort ![path 0, path 1, path 2, path 5] _ rfl rfl
    intro index
    fin_cases index
    · exact hadj 0
    · exact hadj 1
    · change Γ.adjacent (path 2) (path 5)
      rw [heq]
      exact hadj 4
  · change path 3 = path 5 at heq
    apply hshort ![path 0, path 1, path 2, path 3] _ rfl heq
    intro index
    fin_cases index
    · exact hadj 0
    · exact hadj 1
    · exact hadj 2

public theorem goldschmidt_critical_four_path
    (ctx : SectionNineLocalContext G T A B) (hfive : ctx.criticalPath.length = 5) :
    ∃ path : Fin 5 → ctx.Γ.Vertex,
      path 0 = ctx.criticalPath.firstStep ∧ path 4 = ctx.criticalPath.a' ∧
      (∀ index : Fin 4, ctx.Γ.adjacent (path index.castSucc) (path index.succ)) ∧
      (∀ index : Fin 3, path index.castSucc.castSucc ≠ path index.succ.succ) := by
  let full : Fin 6 → ctx.Γ.Vertex := fun index => ctx.criticalPath.path ⟨index.val, by omega⟩
  have hfulladj : ∀ index : Fin 5,
      ctx.Γ.adjacent (full index.castSucc) (full index.succ) := by
    intro index
    exact ctx.criticalPath.path_adj ⟨index.val, by omega⟩
  have hstart : full 0 = ctx.criticalPath.a := ctx.criticalPath.path_start
  have hend : full 5 = ctx.criticalPath.a' := by
    convert ctx.criticalPath.path_end using 1
    simp [full, hfive]
  have hdist : ctx.Γ.distance (full 0) (full 5) = 5 := by
    rw [hstart, hend, ctx.criticalPath.endpoint_distance, hfive]
  have hback := goldschmidt_five_path_nonbacktracking ctx.Γ full hfulladj hdist
  refine ⟨fun index => full index.succ, ctx.criticalPath.path_first, hend, ?_, ?_⟩
  · intro index
    exact hfulladj index.succ
  · intro index
    exact hback index.succ

public theorem goldschmidt_module_le_core_of_three_path
    (ctx : SectionNineLocalContext G T A B) (hlength : 4 < ctx.criticalPath.length)
    (path : Fin 4 → ctx.Γ.Vertex)
    (hadj : ∀ index : Fin 3,
      ctx.Γ.adjacent (path index.castSucc) (path index.succ)) :
    VAt ctx.Γ (path 0) ≤ QAt ctx.Γ (path 3) := by
  change v ctx.Γ (path 0) ≤ _
  rw [v, ctx.Γ.vAt_def]
  apply sSup_le
  rintro subgroup ⟨neighbor, hneighbor, rfl⟩
  have hdist := ctx.Γ.distance_le_of_path 4
    ![neighbor, path 0, path 1, path 2, path 3] (by
      intro index
      fin_cases index
      · exact ctx.Γ.adjacent_symm ((mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor)
      · exact hadj 0
      · exact hadj 1
      · exact hadj 2)
  exact critical_minimality ctx.Γ ctx.criticalPath (lt_of_le_of_lt hdist hlength)

public theorem goldschmidt_core_fixes_neighbor
    (ctx : SectionNineLocalContext G T A B) {middle neighbor : ctx.Γ.Vertex}
    (hadj : ctx.Γ.adjacent middle neighbor) {actor : G}
    (hactor : actor ∈ QAt ctx.Γ middle) : ctx.Γ.act actor neighbor = neighbor := by
  have hle := ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core
    middle neighbor ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj) default).2.2
  exact Set.ext_iff.mp (ctx.Γ.stabilizer_def neighbor) actor |>.mp (hle hactor)

public theorem goldschmidt_act_injective
    (Γ : CosetGraphContext G T A B) (actor : G) : Function.Injective (Γ.act actor) := by
  intro left right heq
  have hinv := congrArg (Γ.act actor⁻¹) heq
  simpa only [← Γ.act_mul, mul_inv_cancel, Γ.act_one] using hinv

public theorem goldschmidt_three_points_two_fixed
    {Points : Type*} [Finite Points] (hcard : Nat.card Points = 3)
    (action : Points → Points) (hinj : Function.Injective action)
    (first second : Points) (hne : first ≠ second)
    (hfirst : action first = first) (hsecond : action second = second) :
    ∀ point, action point = point := by
  classical
  let := Fintype.ofFinite Points
  intro point
  by_cases hpointFirst : point = first
  · simpa only [hpointFirst] using hfirst
  by_cases hpointSecond : point = second
  · simpa only [hpointSecond] using hsecond
  have hcover : ({first, second, point} : Finset Points) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← Nat.card_eq_fintype_card, hcard]
    simp [hne, Ne.symm hpointFirst, Ne.symm hpointSecond]
  have himage : action point ∈ ({first, second, point} : Finset Points) := by
    rw [hcover]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at himage
  rcases himage with himage | himage | himage
  · exact (hpointFirst (hinj (himage.trans hfirst.symm))).elim
  · exact (hpointSecond (hinj (himage.trans hsecond.symm))).elim
  · exact himage

public theorem goldschmidt_cubic_actor_moves_other
    (ctx : SectionNineLocalContext G T A B) (middle fixed other : ctx.Γ.Vertex)
    (hmodel : QuotientIsModel (GAt ctx.Γ middle) (QAt ctx.Γ middle) SL2Two)
    (hfixedAdj : ctx.Γ.adjacent middle fixed) (hotherAdj : ctx.Γ.adjacent middle other)
    (hne : fixed ≠ other) (actor : GAt ctx.Γ middle)
    (hactor : (actor : G) ∉ QAt ctx.Γ middle)
    (hfixed : ctx.Γ.act (actor : G) fixed = fixed) :
    ctx.Γ.act (actor : G) other ≠ other := by
  let _ : Finite ctx.Γ.Vertex := ctx.Γ.finiteVertex
  intro hother
  have hlocal := cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven middle hmodel
  apply hactor
  apply (hlocal.kernel actor).mpr
  have hmiddle : ctx.Γ.act (actor : G) middle = middle :=
    (Set.ext_iff.mp (ctx.Γ.stabilizer_def middle) (actor : G)).mp actor.property
  let action : {neighbor // ctx.Γ.adjacent middle neighbor} →
      {neighbor // ctx.Γ.adjacent middle neighbor} := fun point =>
    ⟨ctx.Γ.act (actor : G) point, by
      simpa only [hmiddle] using adjacent_act ctx.Γ (actor : G) point.property⟩
  have hinj : Function.Injective action := by
    intro first second heq
    exact Subtype.ext (goldschmidt_act_injective ctx.Γ (actor : G) (congrArg Subtype.val heq))
  have hfixAll := goldschmidt_three_points_two_fixed hlocal.degree action hinj
    ⟨fixed, hfixedAdj⟩ ⟨other, hotherAdj⟩
    (fun heq => hne (congrArg Subtype.val heq)) (Subtype.ext hfixed) (Subtype.ext hother)
  intro neighbor hneighbor
  exact congrArg Subtype.val (hfixAll ⟨neighbor, hneighbor⟩)

public theorem goldschmidt_bent_four_path
    (Γ : CosetGraphContext G T A B) (first second middle : Γ.Vertex) (actor : G)
    (hfirst : Γ.adjacent first second) (hsecond : Γ.adjacent second middle)
    (hback : first ≠ middle) (hfix : Γ.act actor middle = middle)
    (hmove : Γ.act actor second ≠ second) :
    let path := ![first, second, middle, Γ.act actor second, Γ.act actor first]
    (∀ index : Fin 4, Γ.adjacent (path index.castSucc) (path index.succ)) ∧
      (∀ index : Fin 3, path index.castSucc.castSucc ≠ path index.succ.succ) := by
  dsimp only
  constructor
  · intro index
    fin_cases index
    · exact hfirst
    · exact hsecond
    · change Γ.adjacent middle (Γ.act actor second)
      simpa only [hfix] using adjacent_act Γ actor (Γ.adjacent_symm hsecond)
    · exact adjacent_act Γ actor (Γ.adjacent_symm hfirst)
  · intro index
    fin_cases index
    · exact hback
    · exact hmove.symm
    · change middle ≠ Γ.act actor first
      rw [← hfix]
      exact fun heq => hback ((goldschmidt_act_injective Γ actor heq).symm)

end Stellmacher.SectionNine
