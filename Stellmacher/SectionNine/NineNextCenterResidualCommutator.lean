module
public import Stellmacher.SectionNine.NineNextFaithfulQuotient
public import Stellmacher.SectionFiveToSeven.ResidualTransport

/-!
# The next center belongs to the residual module commutator

At every next-orbit vertex in the ambient Section Nine setting with
critical distance greater than one, its center lies in [V,E]. No quotient
model or assumed fixed-subgroup identity is required.

At the first vertex, O₂(E_next) lies in Q_next and escapes Q_a by (7.6)(b).
If it centralized Z_a, the edge-centralizer identity would put it in Q_a.
Its nontrivial commutator with Z_a is contained in the next center of
order two, hence equals that center. Monotonicity puts it in [V_next,E_next].
Conjugation transports all three literal vertex subgroups to the supplied
next-orbit vertex.

This is the lower inclusion for the residual-module fixed-subgroup
identity in Stellmacher (9.4), printed p.52 / PDF p.42 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_next_center_le_residual_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (vertex : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep vertex) :
    ZAt ctx.Γ vertex ≤ ⁅VAt ctx.Γ vertex,EAt ctx.Γ vertex⁆ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let R := twoCoreIn (EAt Γ cp.firstStep)
  let J := ⁅ZAt Γ cp.a,R⁆
  have hRcore : R ≤ QAt Γ cp.firstStep := by
    change twoCoreIn (e Γ cp.firstStep) ≤ q Γ cp.firstStep
    rw [CosetGraphContext.e,Γ.twoResidualAt_def,q,Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hJne : J ≠ ⊥ := by
    intro hbot
    apply (lemma_seven_six ctx.sectionSeven Γ cp).next_residual_core.1
    rw [← (lemma_seven_four ctx.sectionSeven Γ cp).edge_centralizer]
    exact le_inf (hRcore.trans (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2)
      (Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot))
  have hZaV : ZAt Γ cp.a ≤ VAt Γ cp.firstStep :=
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hnext := nine_next_center_commutator_and_kernel ctx hb cp.firstStep ⟨1,Γ.act_one _⟩
  have hJZ : J ≤ ZAt Γ cp.firstStep :=
    (Subgroup.commutator_mono hZaV hRcore).trans_eq hnext.2.1
  have hJcard : Nat.card J = 2 := by
    have hdiv : Nat.card J ∣ 2 := hnext.1 ▸ Subgroup.card_dvd_of_le hJZ
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
    · exact (hJne (Subgroup.card_eq_one.mp hone)).elim
    · exact htwo
  have hJ : J = ZAt Γ cp.firstStep := Subgroup.eq_of_le_of_card_ge hJZ
    (by rw [hJcard,hnext.1])
  have hbase : ZAt Γ cp.firstStep ≤ ⁅VAt Γ cp.firstStep,EAt Γ cp.firstStep⁆ :=
    hJ.symm.le.trans (Subgroup.commutator_mono hZaV (twoCoreIn_le _))
  obtain ⟨actor,rfl⟩ := horbit
  have hEact : e Γ (Γ.act actor cp.firstStep) =
      (e Γ cp.firstStep).map (MulAut.conj actor⁻¹).toMonoidHom := by
    change Γ.twoResidualAt (Γ.act actor cp.firstStep) =
      (Γ.twoResidualAt cp.firstStep).map (MulAut.conj actor⁻¹).toMonoidHom
    rw [Γ.twoResidualAt_def,Γ.twoResidualAt_def,← twoResidualIn_map_equiv]
    exact congrArg twoResidualIn (stabilizer_act Γ actor cp.firstStep)
  change z Γ (Γ.act actor cp.firstStep) ≤
    ⁅v Γ (Γ.act actor cp.firstStep),e Γ (Γ.act actor cp.firstStep)⁆
  rw [z_act,v_act,hEact,← Subgroup.map_commutator]
  exact Subgroup.map_mono hbase

end Stellmacher.SectionNine
