module
public import Stellmacher.SectionFiveToSeven.Result7_8.QuotientConfiguration
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Theory.GroupAction.MinimalNormal


/-!
# Generating with a transported neighboring core

Let `d,l` be adjacent vertices under the genuine Section Seven hypotheses.
If a subgroup `Q ≤ Q_l` is not contained in `Q_d`, there is a conjugator `y`
such that the join of `Q` with `Q_(act y⁻¹ l)` contains `y`, lies in `G_d`,
and generates `G_d` together with the full transported edge stabilizer.
The transported vertex remains a neighbor of `d`.

Choose an inclusion-minimal subgroup `A ≤ Q` outside `Q_d`. Its Frattini
subgroup is contained in `Q_d`: otherwise minimality would make it all of
`A`, and the finite Frattini nongeneration property would make `A` trivial.
Apply the proved quotient configuration of (7.8) to `A`. Its self-containing
conjugator and generated subgroup lie in the larger core join. Conjugate the
original edge-generation equality by this same element and enlarge the
generated subgroup to obtain the claimed full-edge generation.

This supplies the core-join configuration in the second branch of assertion
(6) in Stellmacher (8.4), Journal of Algebra 190 (1997), printed p.39. It uses
only the proved quotient form of (7.8), and neither requires `Q` elementary
abelian nor imposes a Frattini condition on `Q` itself.
-/

namespace Stellmacher.SectionsFiveToSeven
open CosetGraphContext SevenSix

/-- Extract a neighboring core join which contains its conjugator and
generates the vertex stabilizer with the transported full edge. -/
public theorem sevenEight_core_join_configuration
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2)
    (d l : Γ.Vertex) (hl : l ∈ neighborhood Γ d)
    (Q : Subgroup G) (hQ : Q ≤ q Γ l) (hQnot : ¬ Q ≤ q Γ d) :
    ∃ y : G, y ∈ Q ⊔ q Γ (Γ.act y⁻¹ l) ∧
      Q ⊔ q Γ (Γ.act y⁻¹ l) ≤ stabilizer Γ d ∧
      Γ.act y⁻¹ l ∈ neighborhood Γ d ∧
      (Q ⊔ q Γ (Γ.act y⁻¹ l)) ⊔
        (stabilizer Γ d ⊓ stabilizer Γ (Γ.act y⁻¹ l)) = stabilizer Γ d := by
  classical
  obtain ⟨A, hAnot, hAQ, hmin⟩ :=
    exists_minimal_subgroup_of_mem_le (fun A : Subgroup G => ¬ A ≤ q Γ d) Q hQnot
  have hPhi : frattiniAmbient A ≤ q Γ d := by
    by_contra hbad
    have hEq : frattiniAmbient A = A := hmin _ hbad (Subgroup.map_subtype_le _)
    have hPhiTop : frattini A = ⊤ := by
      apply Subgroup.map_injective A.subtype_injective
      change frattiniAmbient A = (⊤ : Subgroup A).map A.subtype
      rw [hEq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hbotTop : (⊥ : Subgroup A) = ⊤ :=
      frattini_nongenerating (by rw [hPhiTop]; simp)
    apply hAnot
    intro a ha
    have habot : (⟨a, ha⟩ : A) ∈ (⊥ : Subgroup A) := by rw [hbotTop]; trivial
    have haone : a = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp habot)
    rw [haone]
    exact (q Γ d).one_mem
  obtain ⟨y, A0, L, hLP, hyP, hA0, hLgen, hcard, hyL, hysq, hA0core,
    hLedge, hmodel, horbit, hby, hres⟩ :=
    sevenEight_quotient_configuration h Γ d l hl A (hAQ.trans hQ) hAnot hPhi
  let m := Γ.act y⁻¹ l
  have hQm : q Γ m = (q Γ l).conjBy y := by
    rw [show m = Γ.act y⁻¹ l from rfl, q_act, inv_inv]
    rfl
  have hGm : stabilizer Γ m = (stabilizer Γ l).conjBy y := by
    rw [show m = Γ.act y⁻¹ l from rfl, stabilizer_act, inv_inv]
    rfl
  have hfixd : Γ.act y⁻¹ d = d :=
    (Set.ext_iff.mp (Γ.stabilizer_def d) y⁻¹).mp ((stabilizer Γ d).inv_mem hyP)
  have hm : m ∈ neighborhood Γ d := by
    apply (mem_neighborhood_iff_adjacent Γ).mpr
    have hadj := adjacent_act Γ y⁻¹ ((mem_neighborhood_iff_adjacent Γ).mp hl)
    simpa only [hfixd] using hadj
  have hQmP : q Γ m ≤ stabilizer Γ d :=
    ((lemma_seven_three h Γ).sylow_and_core m d
      ((mem_neighborhood_iff_adjacent Γ).mpr
        (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hm))) default).2.2
  have hQP : Q ≤ stabilizer Γ d := hQ.trans
    (((lemma_seven_three h Γ).sylow_and_core l d
      ((mem_neighborhood_iff_adjacent Γ).mpr
        (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hl))) default).2.2)
  have hLjoin : L ≤ Q ⊔ q Γ m := by
    rw [hLgen]
    refine sup_le (hAQ.trans le_sup_left) ?_
    apply le_trans _ le_sup_right
    rw [hQm]
    exact Subgroup.map_mono (hAQ.trans hQ)
  have hLmap : L.conjBy y = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer hyL)
  have hPmap : (stabilizer Γ d).conjBy y = stabilizer Γ d :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ((stabilizer Γ d).le_normalizer hyP)
  have hnewedge : L ⊔ (stabilizer Γ d ⊓ stabilizer Γ m) = stabilizer Γ d := by
    have hh := congrArg (Subgroup.map (MulAut.conj y).toMonoidHom) hLedge
    rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj y).injective] at hh
    change L.conjBy y ⊔ ((stabilizer Γ l).conjBy y ⊓
      (stabilizer Γ d).conjBy y) = (stabilizer Γ d).conjBy y at hh
    rw [hLmap, hPmap, ← hGm, inf_comm] at hh
    exact hh
  refine ⟨y, hLjoin hyL, sup_le hQP hQmP, hm, ?_⟩
  exact le_antisymm (sup_le (sup_le hQP hQmP) inf_le_left)
    (hnewedge.symm.le.trans (sup_le_sup_right hLjoin _))

end Stellmacher.SectionsFiveToSeven
