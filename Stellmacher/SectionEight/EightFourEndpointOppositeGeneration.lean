module
public import Stellmacher.LaterDefs
public import Stellmacher.SectionFiveToSeven.HypothesisTwoToSectionSeven
public import Stellmacher.SectionFiveToSeven.ResidualTransport
public import Stellmacher.SectionFiveToSeven.PrescribedCriticalPairNormalization
public import Stellmacher.SectionFiveToSeven.Result7_6
public import Stellmacher.SectionEight.EightFourInitialTwoConjugateGeneration

/-!
# One endpoint actor gives both generation conclusions at length two

For the original noncommuting Section Eight context at critical distance two,
one element of the endpoint stabilizer selects a neighbor whose module,
together with the first neighbor module, contains the endpoint residual.
The same selected neighbor has edge stabilizer generating the endpoint
stabilizer together with the initial center. Keeping a single actor in both
conclusions is essential for the normal-star argument in (8.4)(8).

Normalize the reversed critical path and apply the strengthened initial
opposite-generation theorem. Conjugation covariance transports the residual,
modules, centers, and stabilizers back through the same graph action.
The inverse of the pulled-back conjugator is the reported endpoint actor.
No central-first-step or fixed-closure assumption is needed.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.4)(8), printed p.39,
`refs/files/stellmacher-n-group.pdf`.

The local theorem rebuilds the normalized critical-path record over the same
Section Seven hypotheses and graph. The canonical API is an exact wrapper.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem residual_act
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (Γ : CosetGraphContext H S P1 P2) (g : H) (d : Γ.Vertex) :
    EAt Γ (Γ.act g d) = (EAt Γ d).conjBy g⁻¹ := by
  change Γ.twoResidualAt (Γ.act g d) = (Γ.twoResidualAt d).map (MulAut.conj g⁻¹).toMonoidHom
  rw [Γ.twoResidualAt_def,Γ.twoResidualAt_def]
  change twoResidualIn (stabilizer Γ (Γ.act g d)) = _
  rw [stabilizer_act,conjugateBy,twoResidualIn_map_equiv]
  rfl

/-- An actual endpoint stabilizer element supplies the second neighbor module. -/
public theorem eight_four_endpoint_opposite_generation_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hlen : ctx.criticalPath.length = 2) :
    ∃ g ∈ GAt ctx.Γ ctx.criticalPath.a',
      EAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep ⊔
        VAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep) ∧
      ZAt ctx.Γ ctx.criticalPath.a ⊔
        (GAt ctx.Γ ctx.criticalPath.a' ⊓
          GAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep)) =
        GAt ctx.Γ ctx.criticalPath.a' := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  have hcrit := ((lemma_seven_four h Γ cp).commutator_case ctx.commutator_ne).2
  have hcomm : ⁅z Γ cp.a',z Γ cp.a⁆ ≠ ⊥ := by
    rw [Subgroup.commutator_comm]
    exact ctx.commutator_ne
  have hadj : Γ.adjacent cp.a' cp.firstStep := by
    have he := cp.path_adj ⟨1, by change 1 < ctx.criticalPath.length; omega⟩
    have hi : (⟨1, by change 1 < ctx.criticalPath.length; omega⟩ : Fin cp.length).succ =
        ⟨cp.length,Nat.lt_succ_self _⟩ := by apply Fin.ext; simp; exact hlen.symm
    rw [hi,cp.path_end] at he
    have hstart : cp.path (⟨1,by change 1 < ctx.criticalPath.length + 1; omega⟩ : Fin (cp.length+1)) = cp.firstStep := cp.path_first
    exact Γ.adjacent_symm (by simpa only [Fin.castSucc_mk,hstart] using he)
  have hnear : Γ.distance cp.a' cp.a = Γ.distance cp.firstStep cp.a + 1 := by
    rw [Γ.distance_symm cp.a' cp.a, cp.endpoint_distance,
      Γ.distance_symm cp.firstStep cp.a, (adjacent_iff_distance_eq_one Γ).mp cp.firstStep_adj]
    exact hlen
  obtain ⟨a, cp', ha, hend, hb, hl, horient⟩ :=
    exists_criticalPath_through_neighbor_with_orientation h Γ cp cp.a' cp.a cp.firstStep hcrit hadj hnear
  have hc : ⁅z Γ cp'.a,z Γ cp'.a'⁆ ≠ ⊥ := by
    rw [ha,hend,z_act,z_act,← Subgroup.map_commutator]
    intro hh
    apply hcomm
    exact Subgroup.map_injective (MulAut.conj a⁻¹).injective
      (hh.trans (Subgroup.map_bot _).symm)
  let c : SectionEightLocalContext H S P1 P2 :=
    { sectionSeven := ctx.sectionSeven
      sixThree := ctx.sixThree
      Γ := Γ
      criticalPath := cp'
      commutator_ne := hc }
  obtain ⟨x,hx,hgen,hstabilizer⟩ := eight_four_initial_opposite_generation_local c (hl.trans hlen)
  change x ∈ stabilizer Γ cp'.a at hx
  rw [ha,stabilizer_act] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  refine ⟨y⁻¹,(GAt Γ cp.a').inv_mem hy,?_,?_⟩
  · change EAt Γ cp'.a ≤ VAt Γ cp'.firstStep ⊔
      (VAt Γ cp'.firstStep).conjBy ((MulAut.conj a⁻¹) y) at hgen
    rw [ha,hb,residual_act] at hgen
    change (EAt Γ cp.a').conjBy a⁻¹ ≤ v Γ (Γ.act a cp.firstStep) ⊔
      (v Γ (Γ.act a cp.firstStep)).conjBy ((MulAut.conj a⁻¹) y) at hgen
    rw [v_act] at hgen
    have hm := Subgroup.map_mono (f := (MulAut.conj a).toMonoidHom) hgen
    rw [Subgroup.map_sup] at hm
    change ((EAt Γ cp.a').conjBy a⁻¹).conjBy a ≤
      ((VAt Γ cp.firstStep).conjBy a⁻¹).conjBy a ⊔
      (((VAt Γ cp.firstStep).conjBy a⁻¹).conjBy ((MulAut.conj a⁻¹) y)).conjBy a at hm
    rw [Subgroup.conjBy_inv',Subgroup.conjBy_inv',Subgroup.conjBy_conjBy,
      Subgroup.conjBy_conjBy] at hm
    have he : a * ((MulAut.conj a⁻¹) y) * a⁻¹ = y := by simp [mul_assoc]
    rw [he] at hm
    change EAt Γ cp.a' ≤ VAt Γ cp.firstStep ⊔ v Γ (Γ.act y⁻¹ cp.firstStep)
    rw [v_act,inv_inv]
    exact hm
  · change z Γ cp'.a' ⊔
      (stabilizer Γ cp'.a ⊓ (stabilizer Γ cp'.firstStep).conjBy
        ((MulAut.conj a⁻¹) y)) = stabilizer Γ cp'.a at hstabilizer
    rw [ha,hend,hb,z_act,stabilizer_act,stabilizer_act] at hstabilizer
    have hm := congrArg (Subgroup.map (MulAut.conj a).toMonoidHom) hstabilizer
    rw [Subgroup.map_sup,Subgroup.map_inf _ _ _ (MulAut.conj a).injective] at hm
    change ((z Γ cp.a).conjBy a⁻¹).conjBy a ⊔
      (((stabilizer Γ cp.a').conjBy a⁻¹).conjBy a ⊓
        (((stabilizer Γ cp.firstStep).conjBy a⁻¹).conjBy ((MulAut.conj a⁻¹) y)).conjBy a) =
      ((stabilizer Γ cp.a').conjBy a⁻¹).conjBy a at hm
    rw [Subgroup.conjBy_inv',Subgroup.conjBy_inv',
      Subgroup.conjBy_conjBy,Subgroup.conjBy_conjBy] at hm
    have he : a * ((MulAut.conj a⁻¹) y) * a⁻¹ = y := by simp [mul_assoc]
    rw [he] at hm
    change z Γ cp.a ⊔ (stabilizer Γ cp.a' ⊓ stabilizer Γ (Γ.act y⁻¹ cp.firstStep)) =
      stabilizer Γ cp.a'
    rw [stabilizer_act,inv_inv]
    exact hm

/-- Canonical specialization with the same reversed-path actor. -/
public theorem eight_four_endpoint_opposite_generation
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hlen : ctx.criticalPath.length = 2) :
    ∃ g ∈ GAt ctx.Γ ctx.criticalPath.a',
      EAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep ⊔
        VAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep) ∧
      ZAt ctx.Γ ctx.criticalPath.a ⊔
        (GAt ctx.Γ ctx.criticalPath.a' ⊓
          GAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep)) =
        GAt ctx.Γ ctx.criticalPath.a' := by
  exact eight_four_endpoint_opposite_generation_local ctx.toLocalContext hlen

end Stellmacher.SectionEight
