module

public import Stellmacher.SectionNine.NineSevenGoldschmidtOrbits
public import Stellmacher.SectionNine.NineSevenGoldschmidtPlane
public import Stellmacher.SectionNine.NineSevenFourPathCommutator

/-!
# The distance-five Goldschmidt contradiction in (9.7)

Extend the critical four-edge segment to six edges in the cubic graph.
Transport critical noncontainment to select two involutions, then use the
local action kernel to construct both bent four-edge paths. The proved
four-path commutator formula places their diagonal commutators in disjoint
neighbor-center lines. These commutators are inverses, so both are trivial;
no dihedral-order assertion or questionable printed power equation is used.

A plane and the selected involution generate the initial elementary eight.
Short walks give the mixed commuting factors, forcing the entire module to
commute with its conjugate. The same four-path formula identifies that
commutator with a nontrivial center line, a contradiction.

The ambient hypotheses remain on H throughout. The final theorem has the
exact model, cardinality, orbit and index assumptions supplied by the parent.
Source: Stellmacher, printed pp.54–55 / PDF pp.44–45 of
`refs/files/stellmacher-n-group.pdf`, from the distance-five paragraph to (9.8).
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement

universe u

private theorem six_path_contradiction
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H} {embedding : G →* H}
    {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hfive : ctx.criticalPath.length = 5)
    (hfirstCard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hfirstModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hstartData : ∀ vertex, IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex →
      QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two ∧
        Nat.card (ZAt ctx.Γ vertex) = 4)
    (hformula : ∀ path : Fin 5 → ctx.Γ.Vertex,
      IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep (path 0) →
      (∀ index : Fin 4, ctx.Γ.adjacent (path index.castSucc) (path index.succ)) →
      (∀ index : Fin 3, path index.castSucc.castSucc ≠ path index.succ.succ) →
      ⁅VAt ctx.Γ (path 0), VAt ctx.Γ (path 4)⁆ = ZAt ctx.Γ (path 2))
    (path : Fin 7 → ctx.Γ.Vertex) (hstart : path 0 = ctx.criticalPath.firstStep)
    (hadj : ∀ index : Fin 6, ctx.Γ.adjacent (path index.castSucc) (path index.succ))
    (hback : ∀ index : Fin 5, path index.castSucc.castSucc ≠ path index.succ.succ) :
    False := by
  have hb : 1 < ctx.criticalPath.length := by omega
  have hfiveLocal : ctx.toLocalContext.criticalPath.length = 5 := hfive
  have hmodels := fun vertex hvertex => (hstartData vertex hvertex).1
  have horbit0 : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep (path 0) :=
    ⟨1, by rw [ctx.Γ.act_one, hstart]⟩
  have horbit2 := goldschmidt_orbit_step ctx.toLocalContext horbit0
    (ctx.Γ.adjacent_symm (hadj 0)) (hadj 1)
  have horbit4 := goldschmidt_orbit_step ctx.toLocalContext horbit2
    (ctx.Γ.adjacent_symm (hadj 2)) (hadj 3)
  have horbit6 := goldschmidt_orbit_step ctx.toLocalContext horbit4
    (ctx.Γ.adjacent_symm (hadj 4)) (hadj 5)
  have hinitial1 : IsConjugateVertex ctx.Γ ctx.criticalPath.a (path 1) :=
    goldschmidt_orbit_step ctx.toLocalContext
      ⟨1, ctx.Γ.act_one ctx.criticalPath.a⟩
      (by
        change ctx.Γ.adjacent (path 0) ctx.criticalPath.a
        rw [hstart]
        exact ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj) (hadj 0)
  have hinitial3 := goldschmidt_orbit_step ctx.toLocalContext hinitial1
    (ctx.Γ.adjacent_symm (hadj 1)) (hadj 2)
  let forward : Fin 5 → ctx.Γ.Vertex := ![path 0, path 1, path 2, path 3, path 4]
  let backward : Fin 5 → ctx.Γ.Vertex := ![path 6, path 5, path 4, path 3, path 2]
  have hfadj : ∀ index : Fin 4,
      ctx.Γ.adjacent (forward index.castSucc) (forward index.succ) := by
    intro index
    fin_cases index
    · exact hadj 0
    · exact hadj 1
    · exact hadj 2
    · exact hadj 3
  have hfback : ∀ index : Fin 3,
      forward index.castSucc.castSucc ≠ forward index.succ.succ := by
    intro index
    fin_cases index
    · exact hback 0
    · exact hback 1
    · exact hback 2
  have hbadj : ∀ index : Fin 4,
      ctx.Γ.adjacent (backward index.castSucc) (backward index.succ) := by
    intro index
    fin_cases index
    · exact ctx.Γ.adjacent_symm (hadj 5)
    · exact ctx.Γ.adjacent_symm (hadj 4)
    · exact ctx.Γ.adjacent_symm (hadj 3)
    · exact ctx.Γ.adjacent_symm (hadj 2)
  have hbback : ∀ index : Fin 3,
      backward index.castSucc.castSucc ≠ backward index.succ.succ := by
    intro index
    fin_cases index
    · exact (hback 4).symm
    · exact (hback 3).symm
    · exact (hback 2).symm
  have houtsideFirst := goldschmidt_four_path_noncontainment ctx.toLocalContext hfive
    hfirstModel hmodels forward horbit0 hfadj hfback
  have houtsideLast := goldschmidt_four_path_noncontainment ctx.toLocalContext hfive
    hfirstModel hmodels backward horbit6 hbadj hbback
  obtain ⟨generator, hgenerator, hgeneratorOutside⟩ := SetLike.not_le_iff_exists.mp houtsideFirst
  obtain ⟨actor, hactor, hactorOutside⟩ := SetLike.not_le_iff_exists.mp houtsideLast
  change generator ∈ VAt ctx.Γ (path 0) at hgenerator
  change generator ∉ QAt ctx.Γ (path 4) at hgeneratorOutside
  change actor ∈ VAt ctx.Γ (path 6) at hactor
  change actor ∉ QAt ctx.Γ (path 2) at hactorOutside
  have hmodule0 := goldschmidt_orbit_module ctx.toLocalContext hb hfirstCard _ horbit0
  have hmodule6 := goldschmidt_orbit_module ctx.toLocalContext hb hfirstCard _ horbit6
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ (path 0)) := hmodule0.2
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ (path 6)) := hmodule6.2
  have hgeneratorPow : generator ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian generator hgenerator
  have hactorPow : actor ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian actor hactor
  have hgeneratorInv : generator⁻¹ = generator :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hgeneratorPow)
  have hactorInv : actor⁻¹ = actor :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hactorPow)
  have hfirstCore2 : VAt ctx.Γ (path 0) ≤ QAt ctx.Γ (path 2) :=
    goldschmidt_module_le_core_of_short_path ctx.toLocalContext 2 (by omega)
      ![path 0, path 1, path 2] (by
        intro index
        fin_cases index
        · exact hadj 0
        · exact hadj 1)
  have hfirstCore3 : VAt ctx.Γ (path 0) ≤ QAt ctx.Γ (path 3) :=
    goldschmidt_module_le_core_of_three_path ctx.toLocalContext (by omega)
      ![path 0, path 1, path 2, path 3] (by
        intro index
        fin_cases index
        · exact hadj 0
        · exact hadj 1
        · exact hadj 2)
  have hlastCore4 : VAt ctx.Γ (path 6) ≤ QAt ctx.Γ (path 4) :=
    goldschmidt_module_le_core_of_short_path ctx.toLocalContext 2 (by omega)
      ![path 6, path 5, path 4] (by
        intro index
        fin_cases index
        · exact ctx.Γ.adjacent_symm (hadj 5)
        · exact ctx.Γ.adjacent_symm (hadj 4))
  have hlastCore3 : VAt ctx.Γ (path 6) ≤ QAt ctx.Γ (path 3) :=
    goldschmidt_module_le_core_of_three_path ctx.toLocalContext (by omega)
      ![path 6, path 5, path 4, path 3] (by
        intro index
        fin_cases index
        · exact ctx.Γ.adjacent_symm (hadj 5)
        · exact ctx.Γ.adjacent_symm (hadj 4)
        · exact ctx.Γ.adjacent_symm (hadj 3))
  have hgenFix3 := goldschmidt_core_fixes_neighbor ctx.toLocalContext (hadj 2)
    (hfirstCore2 hgenerator)
  have hgenFix4 := goldschmidt_core_fixes_neighbor ctx.toLocalContext (hadj 3)
    (hfirstCore3 hgenerator)
  have hactFix3 := goldschmidt_core_fixes_neighbor ctx.toLocalContext
    (ctx.Γ.adjacent_symm (hadj 3)) (hlastCore4 hactor)
  have hactFix2 := goldschmidt_core_fixes_neighbor ctx.toLocalContext
    (ctx.Γ.adjacent_symm (hadj 2)) (hlastCore3 hactor)
  have hgenStab : generator ∈ GAt ctx.Γ (path 4) :=
    (Set.ext_iff.mp (ctx.Γ.stabilizer_def (path 4)) generator).mpr hgenFix4
  have hactStab : actor ∈ GAt ctx.Γ (path 2) :=
    (Set.ext_iff.mp (ctx.Γ.stabilizer_def (path 2)) actor).mpr hactFix2
  have hgenMove5 := goldschmidt_cubic_actor_moves_other ctx.toLocalContext
    (path 4) (path 3) (path 5) (goldschmidt_orbit_model ctx.Γ horbit4 hfirstModel)
    (ctx.Γ.adjacent_symm (hadj 3)) (hadj 4) (hback 3)
    ⟨generator, hgenStab⟩ hgeneratorOutside hgenFix3
  have hactMove1 := goldschmidt_cubic_actor_moves_other ctx.toLocalContext
    (path 2) (path 3) (path 1) (goldschmidt_orbit_model ctx.Γ horbit2 hfirstModel)
    (hadj 2) (ctx.Γ.adjacent_symm (hadj 1)) (hback 1).symm
    ⟨actor, hactStab⟩ hactorOutside hactFix3
  let bentFirst : Fin 5 → ctx.Γ.Vertex :=
    ![path 0, path 1, path 2, ctx.Γ.act actor (path 1), ctx.Γ.act actor (path 0)]
  let bentLast : Fin 5 → ctx.Γ.Vertex :=
    ![path 6, path 5, path 4, ctx.Γ.act generator (path 5), ctx.Γ.act generator (path 6)]
  have hbf := goldschmidt_bent_four_path ctx.Γ (path 0) (path 1) (path 2) actor
    (hadj 0) (hadj 1) (hback 0) hactFix2 hactMove1
  have hbl := goldschmidt_bent_four_path ctx.Γ (path 6) (path 5) (path 4) generator
    (ctx.Γ.adjacent_symm (hadj 5)) (ctx.Γ.adjacent_symm (hadj 4))
    (hback 4).symm hgenFix4 hgenMove5
  have hcommFirst := hformula bentFirst horbit0 hbf.1 hbf.2
  have hcommLast := hformula bentLast horbit6 hbl.1 hbl.2
  change ⁅VAt ctx.Γ (path 0), VAt ctx.Γ (ctx.Γ.act actor (path 0))⁆ =
    ZAt ctx.Γ (path 2) at hcommFirst
  change ⁅VAt ctx.Γ (path 6), VAt ctx.Γ (ctx.Γ.act generator (path 6))⁆ =
    ZAt ctx.Γ (path 4) at hcommLast
  have hactorConjugate : generator * actor * generator⁻¹ ∈
      VAt ctx.Γ (ctx.Γ.act generator (path 6)) := by
    rw [VAt, v_act, hgeneratorInv]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hgeneratorInv, VAt] using
      Subgroup.mem_map_of_mem (MulAut.conj generator).toMonoidHom hactor
  have hgeneratorConjugate : actor * generator * actor⁻¹ ∈
      VAt ctx.Γ (ctx.Γ.act actor (path 0)) := by
    rw [VAt, v_act, hactorInv]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hactorInv, VAt] using
      Subgroup.mem_map_of_mem (MulAut.conj actor).toMonoidHom hgenerator
  have hdiagLast : ⁅actor, generator * actor * generator⁻¹⁆ ∈ ZAt ctx.Γ (path 4) := by
    rw [← hcommLast]
    exact Subgroup.commutator_mem_commutator hactor hactorConjugate
  have hdiagFirst : ⁅generator, actor * generator * actor⁻¹⁆ ∈ ZAt ctx.Γ (path 2) := by
    rw [← hcommFirst]
    exact Subgroup.commutator_mem_commutator hgenerator hgeneratorConjugate
  have hlines := nine_seven_center_lines ctx hb hfirstModel hstartData (path 3) hinitial3
  have hline2 := hlines.1 (path 2)
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm (hadj 2)))
  have hdisj := hlines.2.2 (path 4) (path 2)
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (hadj 3))
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm (hadj 2)))
    (hback 2).symm
  have hplaneCore4 : ZAt ctx.Γ (path 1) ≤ QAt ctx.Γ (path 4) := by
    have hdist := ctx.Γ.distance_le_of_path 3 ![path 1, path 2, path 3, path 4] (by
      intro index
      fin_cases index
      · exact hadj 1
      · exact hadj 2
      · exact hadj 3)
    exact critical_minimality ctx.Γ ctx.criticalPath (lt_of_le_of_lt hdist (by omega))
  have hgenerate := goldschmidt_plane_generator (VAt ctx.Γ (path 0))
    (ZAt ctx.Γ (path 1)) hmodule0.1 (hstartData _ hinitial1).2
    (nine_seven_neighbor_center_le_module ctx.Γ (hadj 0)) generator hgenerator
    (fun hmem => hgeneratorOutside (hplaneCore4 hmem))
  have hVmap : (VAt ctx.Γ (path 0)).map (MulAut.conj actor).toMonoidHom =
      VAt ctx.Γ (ctx.Γ.act actor (path 0)) := by
    change (v ctx.Γ (path 0)).map _ = v ctx.Γ (ctx.Γ.act actor (path 0))
    rw [v_act, hactorInv]
  have hZmap : (ZAt ctx.Γ (path 1)).map (MulAut.conj actor).toMonoidHom =
      ZAt ctx.Γ (ctx.Γ.act actor (path 1)) := by
    change (z ctx.Γ (path 1)).map _ = z ctx.Γ (ctx.Γ.act actor (path 1))
    rw [z_act, hactorInv]
  have hright : ⁅VAt ctx.Γ (path 0),
      (ZAt ctx.Γ (path 1)).map (MulAut.conj actor).toMonoidHom⁆ = ⊥ := by
    rw [hZmap]
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    have hcore := goldschmidt_module_le_core_of_three_path ctx.toLocalContext (by omega)
      ![path 0, path 1, path 2, ctx.Γ.act actor (path 1)] (by
        intro index
        fin_cases index
        · exact hadj 0
        · exact hadj 1
        · exact hbf.1 2)
    exact hcore.trans (goldschmidt_core_centralizes_center ctx.toLocalContext
      (ctx.Γ.adjacent_symm (hbf.1 2)))
  have hleft : ⁅ZAt ctx.Γ (path 1),
      (VAt ctx.Γ (path 0)).map (MulAut.conj actor).toMonoidHom⁆ = ⊥ := by
    rw [hVmap, Subgroup.commutator_comm]
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    have hcore := goldschmidt_module_le_core_of_three_path ctx.toLocalContext (by omega)
      ![ctx.Γ.act actor (path 0), ctx.Γ.act actor (path 1), path 2, path 1] (by
        intro index
        fin_cases index
        · exact ctx.Γ.adjacent_symm (hbf.1 3)
        · exact ctx.Γ.adjacent_symm (hbf.1 2)
        · exact ctx.Γ.adjacent_symm (hadj 1))
    exact hcore.trans (goldschmidt_core_centralizes_center ctx.toLocalContext (hadj 1))
  have hcollapse := goldschmidt_commutator_collapse (VAt ctx.Γ (path 0))
    (ZAt ctx.Γ (path 1)) (ZAt ctx.Γ (path 4)) (ZAt ctx.Γ (path 2)) actor generator
    hactorPow hgeneratorPow hgenerate hleft hright hdiagLast hdiagFirst (disjoint_iff.mp hdisj)
  rw [hVmap, hcommFirst] at hcollapse
  have hcard := hline2.1
  rw [hcollapse] at hcard
  simp at hcard

public theorem nine_seven_length_ne_five
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H} {embedding : G →* H}
    {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (third : ctx.Γ.Vertex)
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
        Nat.card (ZAt ctx.Γ vertex) = 4) :
    ctx.criticalPath.length ≠ 5 := by
  intro hfive
  obtain ⟨reference, hrefstart, _, hrefadj, hrefback⟩ :=
    goldschmidt_critical_four_path ctx.toLocalContext hfive
  have hdegree := (nineSeven_cubic_four_path_transitivity_local ctx.toLocalContext hfirstModel
    (fun vertex hvertex => (hstartData vertex hvertex).1)).1
  obtain ⟨extended, hext, hextadj, hextback⟩ :=
    goldschmidt_four_path_extend ctx.Γ hdegree reference hrefadj hrefback
  exact six_path_contradiction ctx hfive hfirstCard hfirstModel hstartData
    (nine_seven_four_path_commutator ctx hb third hpath hindex hfirstCard hfirstModel
      hendCard hendModel hstartData hfive)
    extended ((hext 0).trans hrefstart) hextadj hextback

end Stellmacher.SectionNine
