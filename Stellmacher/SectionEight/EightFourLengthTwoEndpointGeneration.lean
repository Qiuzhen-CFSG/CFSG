module
public import Stellmacher.LaterDefs
public import Stellmacher.SectionFiveToSeven.HypothesisTwoToSectionSeven
public import Stellmacher.SectionFiveToSeven.ResidualTransport
public import Stellmacher.SectionFiveToSeven.PrescribedCriticalPairNormalization
public import Stellmacher.SectionFiveToSeven.Result7_6
public import Stellmacher.SectionEight.EightFourInitialTwoConjugateGeneration

/-!
# Two neighbor modules contain the endpoint residual at critical length two

In the original Section Eight noncommuting critical-pair context, if the
critical distance is two, an actual element of the endpoint stabilizer moves
the first-step vertex to a neighbor whose module, together with the original
first-step module, contains the endpoint two-residual. No central-first-step,
faithful-witness choice, or nontrivial fixed-closure premise is needed.

The initial two-conjugate theorem applies to a normalized reversed critical
path. Both endpoints and its first step are transported by the same graph
action. Conjugation covariance carries the actual residual and modules back
to their original ambient subgroups. The pulled-back conjugator is retained,
with the graph-action inverse convention stated explicitly in the result.
The neighbor-only wrapper then follows because this conjugator fixes the
endpoint and transports adjacency.

Source: Stellmacher (8.4)(8), Journal of Algebra 190 (1997), p.39, the opening
sentence of the critical-distance-two case. The full factor-system argument
and removal of the faithful action kernel are proved in the initial leaf.
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
public theorem eight_four_length_two_endpoint_generation
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hlen : ctx.criticalPath.length = 2) :
    ∃ g ∈ GAt ctx.Γ ctx.criticalPath.a',
      EAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep ⊔
        VAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep) := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
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
  let c : SectionEightContext H S0 S P1 P2 :=
    { hypothesisTwo := ctx.hypothesisTwo
      generated := ctx.generated
      Γ := Γ
      criticalPath := cp'
      commutator_ne := hc }
  obtain ⟨x,hx,hgen⟩ := eight_four_initial_two_conjugate_generation c (hl.trans hlen)
  change x ∈ stabilizer Γ cp'.a at hx
  rw [ha,stabilizer_act] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  refine ⟨y⁻¹,(GAt Γ cp.a').inv_mem hy,?_⟩
  change EAt Γ cp'.a ≤ VAt Γ cp'.firstStep ⊔
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


/-- In particular, one neighbor of the endpoint supplies the second module. -/
public theorem eight_four_length_two_endpoint_neighbor_generation
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hlen : ctx.criticalPath.length = 2) :
    ∃ m : ctx.Γ.Vertex, m ∈ neighborhood ctx.Γ ctx.criticalPath.a' ∧
      EAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep ⊔ VAt ctx.Γ m := by
  obtain ⟨g,hg,hgen⟩ := eight_four_length_two_endpoint_generation ctx hlen
  refine ⟨ctx.Γ.act g ctx.criticalPath.firstStep, ?_, hgen⟩
  apply (mem_neighborhood_iff_adjacent ctx.Γ).mpr
  have hnext : ctx.Γ.adjacent ctx.criticalPath.a' ctx.criticalPath.firstStep := by
    have he := ctx.criticalPath.path_adj ⟨1, by omega⟩
    have hi : (⟨1,by omega⟩ : Fin ctx.criticalPath.length).succ =
        ⟨ctx.criticalPath.length,Nat.lt_succ_self _⟩ := Fin.ext (by simp;omega)
    rw [hi,ctx.criticalPath.path_end] at he
    exact ctx.Γ.adjacent_symm (by simpa only [Fin.castSucc_mk,ctx.criticalPath.path_first] using he)
  have h := adjacent_act ctx.Γ g hnext
  have hfix : ctx.Γ.act g ctx.criticalPath.a' = ctx.criticalPath.a' :=
    (Set.ext_iff.mp (ctx.Γ.stabilizer_def ctx.criticalPath.a') g).mp hg
  rwa [hfix] at h

end Stellmacher.SectionEight
