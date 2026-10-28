module
public import Stellmacher.SectionTen.TenOneSmallModuleResidualFull
public import Theory.ThreeSubgroups

/-!
# The small module commutator with the residual two-core

In the order-eight, SL2(2) branch of the actual Section Ten configuration,
the first module commutator with the first residual two-core is exactly the
first central line. This is an input to the extraspecial-center calculation
in Stellmacher (10.1)(a), Journal of Algebra 190 (1997), printed p.60.

The residual core lies in the local core, so the commutator lies in its
known order-two line. If it were trivial, the containment of the
residual/local-core commutator in the residual core and centrality of the
line would make two cyclic triple commutators trivial. The Three Subgroups
Lemma then annihilates the local-core commutator of the full residual
module. The proved equality [V,E]=V contradicts [V,Q]=Z with |Z|=2.
Thus the commutator is nontrivial and fills the central line.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_module_core_commutator
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⁆ =
        ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let vertex := ctx.criticalPath.firstStep
  let P := GAt ctx.Γ vertex
  let Q := QAt ctx.Γ vertex
  let E := EAt ctx.Γ vertex
  let R := twoCoreIn E
  let V := VAt ctx.Γ vertex
  let Z := ZAt ctx.Γ vertex
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hE : E = twoResidualIn P := ctx.Γ.twoResidualAt_def _
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hRQ : R ≤ Q := by
    change twoCoreIn (ctx.Γ.twoResidualAt vertex) ≤ ctx.Γ.twoCoreAt vertex
    rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoCoreAt_def, residual_core_eq_inter_core]
    exact inf_le_right
  have hEQ : ⁅E,Q⁆ ≤ R := by
    change ⁅E, ctx.Γ.twoCoreAt vertex⁆ ≤ twoCoreIn E
    rw [hE, ctx.Γ.twoCoreAt_def]
    exact residual_commutator_core_le P
  obtain ⟨hZcard,hVQ,_⟩ := nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext hb vertex ⟨1,ctx.Γ.act_one _⟩
  change Nat.card Z = 2 at hZcard
  change ⁅V,Q⁆ = Z at hVQ
  have hPZ : P ≤ Subgroup.centralizer (Z : Set G) :=
    nine_next_center_centralizes_stabilizer ctx.toLocalContext.toSectionNineLocalContext
      vertex ⟨1,ctx.Γ.act_one _⟩
  have hZE : ⁅Z,E⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hEP.trans hPZ)
  have hfull : ⁅V,E⁆ = V :=
    ten_one_small_module_residual_full ctx middle hpath hsmall hmodel
  have hle : ⁅V,R⁆ ≤ Z := (Subgroup.commutator_mono le_rfl hRQ).trans_eq hVQ
  have hne : ⁅V,R⁆ ≠ ⊥ := by
    intro hbot
    have hrotOne : ⁅⁅E,Q⁆,V⁆ = ⊥ := by
      apply bot_unique
      exact (Subgroup.commutator_mono hEQ le_rfl).trans_eq
        ((Subgroup.commutator_comm R V).trans hbot)
    have hrotTwo : ⁅⁅Q,V⁆,E⁆ = ⊥ := by
      rw [Subgroup.commutator_comm Q V, hVQ, hZE]
    have htriple := Subgroup.commutator_commutator_eq_bot_of_rotate hrotOne hrotTwo
    rw [hfull,hVQ] at htriple
    have hone := Subgroup.card_eq_one.mpr htriple
    omega
  apply Subgroup.eq_of_le_of_card_ge hle
  have hcard := (Subgroup.one_lt_card_iff_ne_bot ⁅V,R⁆).mpr hne
  omega

end Stellmacher.SectionTen
