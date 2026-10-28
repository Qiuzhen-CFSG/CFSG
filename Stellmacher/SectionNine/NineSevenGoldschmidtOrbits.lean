module

public import Stellmacher.SectionNine.NineSevenGoldschmidtPaths

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

variable {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}

public theorem goldschmidt_four_path_orbit_transport
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
      second index.castSucc.castSucc ≠ second index.succ.succ) :
    ∃ actor : G, ∀ index, ctx.Γ.act actor (first index) = second index := by
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
    exact hsecondback index (goldschmidt_act_injective ctx.Γ mover⁻¹ hequal)
  obtain ⟨actor, hactor⟩ :=
    (nineSeven_cubic_four_path_transitivity_local ctx hfirstModel hstartModels).2
      first target hfirst htarget hfirstadj htargetadj hfirstback htargetback
  refine ⟨(actor : G) * mover, ?_⟩
  intro index
  rw [ctx.Γ.act_mul, hactor, hundo]

public theorem goldschmidt_four_path_noncontainment
    (ctx : SectionNineLocalContext G T A B) (hfive : ctx.criticalPath.length = 5)
    (hfirstModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hstartModels : ∀ vertex, IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex →
      QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two)
    (path : Fin 5 → ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep (path 0))
    (hadj : ∀ index : Fin 4, ctx.Γ.adjacent (path index.castSucc) (path index.succ))
    (hback : ∀ index : Fin 3, path index.castSucc.castSucc ≠ path index.succ.succ) :
    ¬ VAt ctx.Γ (path 0) ≤ QAt ctx.Γ (path 4) := by
  obtain ⟨reference, hfirst, hend, hrefadj, hrefback⟩ := goldschmidt_critical_four_path ctx hfive
  obtain ⟨actor, hactor⟩ := goldschmidt_four_path_orbit_transport ctx hfirstModel
    hstartModels reference path hfirst horbit hrefadj hadj hrefback hback
  intro hle
  apply ctx.criticalPath.critical.2
  apply (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1.trans
  have hmaple : (VAt ctx.Γ (reference 0)).map (MulAut.conj actor⁻¹).toMonoidHom ≤
      (QAt ctx.Γ (reference 4)).map (MulAut.conj actor⁻¹).toMonoidHom := by
    rw [← v_act, ← q_act, hactor 0, hactor 4]
    exact hle
  rw [hfirst, hend] at hmaple
  intro element helement
  have hmem := hmaple (Subgroup.mem_map_of_mem (MulAut.conj actor⁻¹).toMonoidHom helement)
  simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, QAt, q] using
    (Subgroup.mem_map_equiv).mp hmem

public theorem goldschmidt_orbit_step
    (ctx : SectionNineLocalContext G T A B) {base source middle target : ctx.Γ.Vertex}
    (hsource : IsConjugateVertex ctx.Γ base source)
    (hleft : ctx.Γ.adjacent middle source) (hright : ctx.Γ.adjacent middle target) :
    IsConjugateVertex ctx.Γ base target := by
  obtain ⟨first, hfirst⟩ := hsource
  obtain ⟨second, hsecond⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hleft)
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hright)
  exact ⟨first * (second : G), by rw [ctx.Γ.act_mul, hfirst, hsecond]⟩

public theorem goldschmidt_orbit_model
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

public theorem goldschmidt_orbit_module
    (ctx : SectionNineLocalContext G T A B) (hb : 1 < ctx.criticalPath.length)
    (hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (vertex : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep vertex) :
    Nat.card (VAt ctx.Γ vertex) = 8 ∧ IsElementaryAbelian 2 (VAt ctx.Γ vertex) := by
  obtain ⟨actor, rfl⟩ := horbit
  change Nat.card (v ctx.Γ (ctx.Γ.act actor ctx.criticalPath.firstStep)) = 8 ∧
    IsElementaryAbelian 2 (v ctx.Γ (ctx.Γ.act actor ctx.criticalPath.firstStep))
  rw [v_act]
  constructor
  · rw [Subgroup.card_map_of_injective (MulAut.conj actor⁻¹).injective]
    exact hcard
  · let _ := (lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
      ctx.commutator_eq).longer_case hb |>.1
    exact IsElementaryAbelian.map (MulAut.conj actor⁻¹).toMonoidHom

public theorem goldschmidt_module_le_core_of_short_path
    (ctx : SectionNineLocalContext G T A B) (length : ℕ)
    (hlength : length + 1 < ctx.criticalPath.length)
    (path : Fin (length + 1) → ctx.Γ.Vertex)
    (hadj : ∀ index : Fin length,
      ctx.Γ.adjacent (path index.castSucc) (path index.succ)) :
    VAt ctx.Γ (path 0) ≤ QAt ctx.Γ (path ⟨length, by omega⟩) := by
  change v ctx.Γ (path 0) ≤ _
  rw [v, ctx.Γ.vAt_def]
  apply sSup_le
  rintro subgroup ⟨neighbor, hneighbor, rfl⟩
  let extended : Fin (length + 1 + 1) → ctx.Γ.Vertex := Fin.cases neighbor path
  have hextadj : ∀ index : Fin (length + 1),
      ctx.Γ.adjacent (extended index.castSucc) (extended index.succ) := by
    intro index
    refine Fin.cases ?_ (fun index => ?_) index
    · exact ctx.Γ.adjacent_symm ((mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor)
    · simpa only [extended, Fin.castSucc_succ, Fin.cases_succ] using hadj index
  have hdist := ctx.Γ.distance_le_of_path (length + 1) extended hextadj
  have hdist' : ctx.Γ.distance neighbor (path ⟨length, by omega⟩) ≤ length + 1 := hdist
  exact critical_minimality ctx.Γ ctx.criticalPath (lt_of_le_of_lt hdist' hlength)

public theorem goldschmidt_core_centralizes_center
    (ctx : SectionNineLocalContext G T A B) {middle neighbor : ctx.Γ.Vertex}
    (hadj : ctx.Γ.adjacent middle neighbor) :
    QAt ctx.Γ middle ≤ Subgroup.centralizer (ZAt ctx.Γ middle : Set G) := by
  apply Subgroup.le_centralizer_iff.mpr
  exact ((lemma_seven_three ctx.sectionSeven ctx.Γ).center_core middle neighbor
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)).trans
    ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))

end Stellmacher.SectionNine

