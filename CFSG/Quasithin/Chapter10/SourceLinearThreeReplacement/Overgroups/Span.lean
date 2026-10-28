module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Centralizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Component
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The original component span is contained in every overgroup span

Inside J=K_zT the solvable radical is O₂(J), by the literal wreath quotient.
A normal subgroup containing X cannot be solvable: otherwise the two-perfect
seed X would be a two-group and hence trivial. A C-component of that normal
subgroup lifts to J. Its T-orbit is K_z, by the supplied orbit identities,
so normality gives the desired containment K_z ≤ ⟨X^M₊⟩.

Source: the inclusion before applying 10.2.4 in the last paragraph of
Aschbacher--Smith §10.3, printed p.756. All normality is relative to J.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups
open Chapter3.Section02
open Theory.SpecificGroups.SymmetricFive.WreathComponents
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D}

omit [Finite G] in
private theorem seed_ne_bot (z : G)
    (hstrict : centralizerSeed T L z < componentSpan T L z) :
    centralizerSeed T L z ≠ ⊥ := by
  intro he
  have hspan : componentSpan T L z = ⊥ := by
    simp only [componentSpan, he, conjugateSpanBy_eq_iSup_conj, Subgroup.map_bot, iSup_const]
  exact hstrict.ne (he.trans hspan.symm)

/-- Normality and the original component-orbit identities supply the
previously unstated inclusion K_z ≤ J_z, for any containing overgroup. -/
theorem componentSpan_le_overgroup_span
    (d : CentralizerData T D s)
    (e : (componentJoin T L (d.first * d.second) ⧸
      pCore 2 (componentJoin T L (d.first * d.second))) ≃* W)
    (hstrict : centralizerSeed T L (d.first * d.second) <
      componentSpan T L (d.first * d.second))
    (horbit : ∀ K ∈ Chapter1.cComponentsIn (componentJoin T L (d.first * d.second)),
      componentOrbit K (T : Subgroup G) = componentSpan T L (d.first * d.second))
    {M : Subgroup G} (hJM : componentJoin T L (d.first * d.second) ≤ M) :
    componentSpan T L (d.first * d.second) ≤
      conjugateSpanBy (centralizerSeed T L (d.first * d.second)) M := by
  let z := d.first * d.second
  let X := centralizerSeed T L z
  let J := componentJoin T L z
  let N := conjugateSpanBy X M
  have hXJ : X ≤ J := (le_conjugateSpanBy _ _).trans le_sup_left
  have hJN : J ≤ normalizer (N : Set G) :=
    hJM.trans (le_normalizer_conjugateSpanBy X M)
  let A := N.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer hJN
  have hXn : X ≠ ⊥ := seed_ne_bot z hstrict
  have hns : ¬ Group.IsSolvable A := by
    intro hsol
    have hrad : A ≤ solvableRadical J := le_solvableRadical A inferInstance hsol
    rw [wreath_quotient_radical e] at hrad
    have hXcore : X ≤ (pCore 2 J).map J.subtype := by
      intro x hx
      exact mem_map.mpr ⟨⟨x,hXJ hx⟩,
        hrad (show (⟨x,hXJ hx⟩ : J) ∈ A from le_conjugateSpanBy X M hx),rfl⟩
    have hpX : IsPGroup 2 X := (pCore_isPGroup (p := 2) (G := J)).map J.subtype |>.to_le hXcore
    have hperfect : IsPPerfect 2 X := isPPerfect_embedded_pResidual 2 _
    have hbot : (⊥ : Subgroup X) = ⊤ :=
      hperfect ⊥ inferInstance (hpX.of_equiv QuotientGroup.quotientBot.symm)
    apply hXn
    apply bot_unique
    intro x hx
    have hxbot : (⟨x,hx⟩ : X) ∈ (⊥ : Subgroup X) := hbot.symm ▸ mem_top _
    exact congrArg Subtype.val (mem_bot.mp hxbot)
  obtain ⟨B,hB⟩ := exists_isCComponent_of_not_isSolvable hns
  let C : Subgroup J := B.map A.subtype
  have hC : C.IsCComponent := hB.map_subtype (inferInstance : A.Normal).isSubnormal
  let K : Subgroup G := C.map J.subtype
  have hK : K ∈ Chapter1.cComponentsIn J := by
    refine ⟨map_subtype_le _, ?_⟩
    simpa only [K, subgroupOf, comap_map_eq_self_of_injective J.subtype_injective] using hC
  have hKN : K ≤ N := by
    rintro _ ⟨c,hc,rfl⟩
    exact (map_subtype_le B hc : c ∈ A)
  rw [←horbit K hK]
  exact iSup_conjugates_le_of_le_normalizer K T N hKN (le_sup_right.trans hJN)

/-- The larger span remains an escaping subgroup of M₊. -/
theorem overgroup_span_escapes
    (d : CentralizerData T D s)
    (e : (componentJoin T L (d.first * d.second) ⧸
      pCore 2 (componentJoin T L (d.first * d.second))) ≃* W)
    (hstrict : centralizerSeed T L (d.first * d.second) <
      componentSpan T L (d.first * d.second))
    (hout : ¬ componentSpan T L (d.first * d.second) ≤ D.maximalLocal)
    (horbit : ∀ K ∈ Chapter1.cComponentsIn (componentJoin T L (d.first * d.second)),
      componentOrbit K (T : Subgroup G) = componentSpan T L (d.first * d.second))
    {M : Subgroup G} (hJM : componentJoin T L (d.first * d.second) ≤ M) :
    ¬ conjugateSpanBy (centralizerSeed T L (d.first * d.second)) M ≤ D.maximalLocal :=
  fun hn => hout ((componentSpan_le_overgroup_span d e hstrict horbit hJM).trans hn)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups
