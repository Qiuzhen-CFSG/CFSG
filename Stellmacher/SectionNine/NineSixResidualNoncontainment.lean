module
public import Stellmacher.SectionNine.NineNextFaithfulQuotient
public import Stellmacher.SectionEight.GeneratedEightSixNextConjugateGeometry
public import Stellmacher.SectionEight.GeneratedEightSixSL2ResidualOdd
public import Theory.Frattini.CoprimeAction

/-!
# The initial center escapes the first residual commutator

For the genuine ambient Section Nine geometry, assume the first stabilizer
modulo its two-core is SL₂(2) and its neighbor-center module has order sixteen.
Then the initial center is not contained in the residual commutator of that
module. The theorem retains the literal stabilizer, residual, and module.

If containment held, conjugate generation and stabilizer invariance would
make that commutator the entire module. The quotient by the first center
has order eight, and the core acts trivially on it. Factoring the quotient
conjugation action through SL₂(2) shows that the residual action image has
order dividing three. Coprime fixed-point/commutator decomposition would
then give a trivial fixed subgroup. Orbit counting modulo three contradicts
this, since eight is not congruent to one modulo three.

This proves the noncontainment in source (*) of Stellmacher (9.6), Journal
of Algebra 190 (1997), printed p.53 / PDF p.43, in
`refs/files/stellmacher-n-group.pdf`. It does not assume the source's
intermediate residual-commutator cardinality.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionEight
open scoped IsMulCommutative
universe u

private theorem no_cubic_full_action_on_eight
    {W : Type*} [Group W] [Finite W] [IsMulCommutative W]
    (F : Subgroup (MulAut W)) (hF : Nat.card F ∣ 3) (hW : Nat.card W = 8) :
    commutatorAction F W ≠ ⊤ := by
  intro hfull
  have hcop : Nat.Coprime (Nat.card F) (Nat.card W) := by
    rw [hW]
    exact Nat.Coprime.of_dvd_left hF (by decide : Nat.Coprime 3 8)
  have hcompl :=
    isCompl_fixedPointSubgroup_commutatorAction_of_sup_eq_top_of_coprime_of_isMulCommutative
      (G := W) (A := F) (by rw [hfull]; simp) hcop inferInstance
  have hfixed : fixedPointSubgroup F W = ⊥ := by
    have hdisj := hcompl.disjoint
    rwa [hfull, disjoint_top] at hdisj
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hp : IsPGroup 3 F := IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hF)
  have hcount := hp.card_modEq_card_fixedPoints W
  have hcardFixed : Nat.card (MulAction.fixedPoints F W) = 1 := by
    change Nat.card (fixedPointSubgroup F W) = 1
    rw [hfixed]
    simp
  rw [hW, hcardFixed] at hcount
  norm_num [Nat.ModEq] at hcount

public theorem nine_six_initial_center_not_le_first_residual_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 16) :
    ¬ ZAt ctx.Γ ctx.criticalPath.a ≤
      ⁅VAt ctx.Γ ctx.criticalPath.firstStep, EAt ctx.Γ ctx.criticalPath.firstStep⁆ := by
  classical
  intro hbad
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let U := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let Q := QAt Γ cp.firstStep
  let E := EAt Γ cp.firstStep
  have hPU : P ≤ Subgroup.normalizer (U : Set G) :=
    stabilizer_le_normalizer_v Γ cp.firstStep
  have hEP : E ≤ P := by
    change Γ.twoResidualAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hEN : (E.subgroupOf P).Normal := by
    change ((Γ.twoResidualAt cp.firstStep).subgroupOf P).Normal
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_normal P
  have hPE : P ≤ Subgroup.normalizer (E : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEP).mp hEN
  have hPC : P ≤ Subgroup.normalizer ((⁅U,E⁆ : Subgroup G) : Set G) := by
    intro actor hactor
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPU hactor),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPE hactor)]
  have hfull : ⁅U,E⁆ = U := by
    apply le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp (hEP.trans hPU))
    have hback : cp.a ∈ neighborhood Γ cp.firstStep :=
      (mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)
    conv_lhs => rw [show U = conjugateClosure (ZAt Γ cp.a) P from
      eight_six_neighbor_join_eq_conjugate_closure ctx.sectionSeven Γ _ _ hback]
    apply (Subgroup.closure_le _).mpr
    rintro point ⟨actor, representative, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hPC actor.property) representative).mp
      (hbad representative.property)
  have hdata := nine_next_center_commutator_and_kernel ctx hb cp.firstStep ⟨1, Γ.act_one _⟩
  have hZcard : Nat.card Z = 2 := hdata.1
  have hUQ : ⁅U,Q⁆ = Z := hdata.2.1
  have hQP : Q ≤ P := by
    change Γ.twoCoreAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hZU : Z ≤ U := hUQ.symm.le.trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPU))
  let _ : IsElementaryAbelian 2 U :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).1
  let _ : IsMulCommutative U := inferInstance
  have hN : (Z.subgroupOf U).Normal := inferInstance
  let _ := hN
  let W := U ⧸ Z.subgroupOf U
  have hWcard : Nat.card W = 8 := by
    have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf U)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv, hZcard,
      show Nat.card U = 16 from hcard] at hprod
    change 16 = Nat.card W * 2 at hprod
    omega
  obtain ⟨ρ, _, hρker, hρfull⟩ := Subgroup.exists_quotient_conjugation_full_action
    P U Z E Q hPU (stabilizer_le_normalizer_z Γ cp.firstStep) hN hEP hfull hUQ.le
  obtain ⟨projection, hsurj, hkernel⟩ := hquot
  have hfactor : projection.ker ≤ ρ.ker := hkernel ▸ hρker
  let σ : SL2Two →* MulAut W := projection.liftOfSurjective hsurj ⟨ρ, hfactor⟩
  have hcomp : σ.comp projection = ρ :=
    congrArg Subtype.val ((projection.liftOfSurjective hsurj).symm_apply_apply ⟨ρ, hfactor⟩)
  have hnative : E.subgroupOf P = twoResidualAmbient (⊤ : Subgroup P) := by
    change (Γ.twoResidualAt cp.firstStep).subgroupOf P = _
    rw [Γ.twoResidualAt_def]
    change ((twoResidualSubgroup P).map P.subtype).subgroupOf P = _
    rw [subgroupOf_map_subtype_eq, SectionThree.twoResidualSubgroup_eq_hktPResidual',
      SectionThree.twoResidualAmbient_top_eq_hktPResidual]
  have hresmap : (E.subgroupOf P).map projection = commutator SL2Two := by
    rw [hnative, map_twoResidualAmbient_of_subgroup_image ⊤ projection ⊤
      (Subgroup.map_top_of_surjective projection hsurj),
      eight_six_sl2_residual_eq_commutator]
  have hF : Nat.card ((E.subgroupOf P).map ρ) ∣ 3 := by
    rw [← hcomp, ← Subgroup.map_map, hresmap,
      ← isSL2Two_commutator_card (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)]
    exact Subgroup.card_map_dvd _ σ
  exact no_cubic_full_action_on_eight ((E.subgroupOf P).map ρ) hF hWcard hρfull

end Stellmacher.SectionNine

