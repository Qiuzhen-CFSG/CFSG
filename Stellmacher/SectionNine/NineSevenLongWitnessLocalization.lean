module
public import Stellmacher.SectionNine.NineSevenResidualTwoArc
public import Stellmacher.SectionNine.NineSevenNeighborJoinBounds
public import Stellmacher.SectionNine.NineSevenNormalityObstructions

/-!
# The long-distance commutator witness lies on the path

With the order-eight modules and SL₂(2) quotient data of (9.7), at critical
distance greater than seven a neighbor of offset two whose center equals
the critical commutator must be either the first or third path vertex.

If it were the other neighbor, transported (7.6)(b) and the cubic action
would supply an element of its residual two-core taking the first vertex
to the third. This element lies in the centralizer core of the commutator
and therefore normalizes the penultimate neighborhood. Critical minimality
makes the third module centralize that neighborhood; transport gives the
same for the first module. The terminal module lies in the neighborhood,
so the nontrivial critical commutator would vanish.

This supplies the witness localization used by the penultimate transport
of the initial neighbor join. Source: Stellmacher (9.7), printed p.54 /
PDF p.44, first paragraph of the long-distance branch.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_seven_long_commutator_witness_on_path
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
    (hlong : 7 < ctx.criticalPath.length)
    (rho : ctx.Γ.Vertex)
    (hrho : rho ∈ Neighborhood ctx.Γ (ctx.criticalPath.path ⟨2, by omega⟩))
    (hRrho : ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ =
      ZAt ctx.Γ rho) :
    rho = ctx.criticalPath.firstStep ∨ rho = third := by
  classical
  by_contra! hbad
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : 7 < cp.length := hlong
  let second := cp.path ⟨2, by dsimp [cp]; omega⟩
  let penultimate := cp.path ⟨cp.length - 1, by dsimp [cp]; omega⟩
  let R := ⁅VAt Γ cp.a', ZAt Γ cp.a⁆
  let C := twoCoreIn (Subgroup.centralizer (R : Set G))
  let K := twoCoreIn (EAt Γ rho)
  have hthird : cp.path ⟨3, by dsimp [cp]; omega⟩ = third := by
    obtain ⟨index, hindex, heq⟩ := hpath
    have hfin : index = ⟨3, by omega⟩ := Fin.ext hindex
    rwa [hfin] at heq
  have hfirstSecond : Γ.adjacent cp.firstStep second := by
    have hadj := cp.path_adj ⟨1, by dsimp [cp]; omega⟩
    change Γ.adjacent (cp.path ⟨1, by dsimp [cp]; omega⟩) second at hadj
    rwa [cp.path_first] at hadj
  have hsecondThird : Γ.adjacent second third := by
    have hadj := cp.path_adj ⟨2, by dsimp [cp]; omega⟩
    change Γ.adjacent second (cp.path ⟨3, by dsimp [cp]; omega⟩) at hadj
    rwa [hthird] at hadj
  have hsecondRho : Γ.adjacent second rho :=
    (mem_neighborhood_iff_adjacent Γ).mp hrho
  obtain ⟨orbitActor, horbitActor⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
    second ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hfirstSecond)) hrho
  have hrhoOrbit : IsConjugateVertex Γ cp.firstStep rho := ⟨orbitActor, horbitActor⟩
  obtain ⟨secondActor, hsecondActor⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
    cp.firstStep ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
      ((mem_neighborhood_iff_adjacent Γ).mpr hfirstSecond)
  have hsecondModel := (hstartData second ⟨secondActor, hsecondActor⟩).1
  have hKQ : K ≤ QAt Γ rho := by
    change twoCoreIn (Γ.twoResidualAt rho) ≤ Γ.twoCoreAt rho
    rw [Γ.twoResidualAt_def, Γ.twoCoreAt_def, residual_core_eq_inter_core]
    exact inf_le_right
  have hKrho : K ≤ GAt Γ rho := by
    apply hKQ.trans
    change Γ.twoCoreAt rho ≤ Γ.stabilizer rho
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hKsecond : K ≤ GAt Γ second := hKQ.trans
    (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core rho second
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hsecondRho)) default).2.2)
  have htrans := (cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven second
    hsecondModel).punctured_transitivity rho hsecondRho K (le_inf hKsecond hKrho)
      (nine_seven_residual_core_escapes_neighbor ctx.toLocalContext rho second hrhoOrbit
        (Γ.adjacent_symm hsecondRho))
  obtain ⟨actor, hactorMove⟩ := htrans
    ⟨(mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hfirstSecond), hbad.1.symm⟩
    ⟨(mem_neighborhood_iff_adjacent Γ).mpr hsecondThird, hbad.2.symm⟩
  have hgeometry := nine_seven_commutator_geometry ctx hb third hpath hindex
    hfirstCard hfirstModel hendCard hendModel hstartData (by omega)
  have hRcard : Nat.card R = 2 := hgeometry.1
  have hKC : K ≤ C := by
    have hcore := (nine_seven_order_two_centralizer_core_control ctx rho
      (hRrho ▸ hRcard)).2.1
    rwa [← hRrho] at hcore
  have hCnormalizes : C ≤ Subgroup.normalizer (GeneratedNeighborhoodV Γ penultimate : Set G) :=
    (nine_seven_commutator_centralizer_core_control ctx hb third hpath hindex
      hfirstCard hfirstModel hendCard hendModel hstartData (by omega)).2.2.2
  have hthirdCentral : VAt Γ third ≤
      Subgroup.centralizer (GeneratedNeighborhoodV Γ penultimate : Set G) := by
    change v Γ third ≤ _
    rw [v, Γ.vAt_def]
    apply sSup_le
    rintro subgroup ⟨neighbor, hneighbor, rfl⟩
    have hdist := path_distance_le Γ cp 3 (cp.length - 1) (by dsimp [cp]; omega) (by omega)
    rw [hthird] at hdist
    have hnear := nine_seven_adjacent_distance_bound Γ neighbor third penultimate
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor))
    have hWQ : GeneratedNeighborhoodV Γ penultimate ≤ QAt Γ neighbor := by
      apply nine_seven_neighborhood_le_core_of_distance Γ cp
      rw [Γ.distance_symm]
      dsimp only [penultimate] at hnear ⊢
      omega
    have hcenter := (lemma_seven_three ctx.sectionSeven Γ).center_core neighbor third
      ((mem_neighborhood_iff_adjacent Γ).mpr
        (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor)))
    exact (hcenter.trans ((omegaOneCenter_le_centerAmbient _).trans
      (centerAmbient_le_centralizer _))).trans (Subgroup.centralizer_le hWQ)
  have hactorC : (actor : G) ∈ C := hKC actor.property
  have hWmap : (GeneratedNeighborhoodV Γ penultimate).map
      (MulAut.conj (actor : G)).toMonoidHom = GeneratedNeighborhoodV Γ penultimate :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hCnormalizes hactorC)
  have hthirdBack : Γ.act (actor : G)⁻¹ third = cp.firstStep := by
    rw [← hactorMove, ← Γ.act_mul, mul_inv_cancel, Γ.act_one]
  have hVmap : (VAt Γ third).map (MulAut.conj (actor : G)).toMonoidHom =
      VAt Γ cp.firstStep := by
    have hmap := v_act Γ (actor : G)⁻¹ third
    simpa only [inv_inv, hthirdBack] using hmap.symm
  have hfirstCentral : VAt Γ cp.firstStep ≤
      Subgroup.centralizer (GeneratedNeighborhoodV Γ penultimate : Set G) := by
    have hbound := (Subgroup.map_mono (f := (MulAut.conj (actor : G)).toMonoidHom)
      hthirdCentral).trans (Subgroup.map_centralizer_le_centralizer_image _ _)
    rw [← Subgroup.coe_map, hVmap, hWmap] at hbound
    exact hbound
  have hpenTerminal : Γ.adjacent penultimate cp.a' := by
    have hadj := cp.path_adj ⟨cp.length - 1, by dsimp [cp]; omega⟩
    have hend : (⟨cp.length - 1, by dsimp [cp]; omega⟩ : Fin cp.length).succ =
        ⟨cp.length, by omega⟩ := Fin.ext (by dsimp [cp]; omega)
    rwa [hend, cp.path_end] at hadj
  have hterminalW := nine_seven_neighbor_module_le_neighborhood Γ hpenTerminal
  have hZfirst : ZAt Γ cp.a ≤ VAt Γ cp.firstStep :=
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  apply nine_seven_terminal_initial_commutator_ne_bot ctx
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact Subgroup.le_centralizer_iff.mp
    (hZfirst.trans (hfirstCentral.trans (Subgroup.centralizer_le hterminalW)))

end Stellmacher.SectionNine
