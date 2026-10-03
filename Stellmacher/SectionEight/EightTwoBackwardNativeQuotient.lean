module
public import Stellmacher.SectionEight.EightTwoBackwardLocalSetup
public import Stellmacher.SectionEight.EightTwoBackwardNativeCoreData
public import Stellmacher.SectionTwo.TwoFourInitialReduction
public import Stellmacher.SectionOne.OneSevenDihedralQuotient

/-!
# Native quotient hypotheses for the smaller group in (8.2)

The join of the initial two-residual and the next vertex core satisfies
Section Two's standing hypotheses whenever the first-edge core intersection
is normal in the initial stabilizer. With the noncentrality and length
hypotheses of the backward branch, every supplied Sylow whose ambient image
is the next core has a unique maximal overgroup and a native centralizer
quotient isomorphic to SL₂(2). The surjection takes values in a universe lift
so that it can be supplied directly to (2.5).

Solvability and characteristic two descend to the normal join. Its exact
Sylow has nontrivial image, which gives even order. The characteristic-two
condition is transported using the actual subgroup equivalence and
functoriality of the two-core. The imported core-data theorem supplies the
ordinary dihedral quotient and unique maximality. The initial reduction
of (2.4), using the characteristic obstruction, makes the native Thompson
image nontrivial and puts the two-core in the native centralizer kernel.
The named native conjugation action therefore factors through the odd
dihedral quotient and has a nontrivial offender. The small-Sylow case of
(1.7) identifies this action quotient with SL₂(2). Composing its quotient
map with the isomorphism and a universe lift preserves the exact kernel.
No identification of the native module with either vertex module is used.

Source: Stellmacher (8.2), first containment case, Journal of Algebra 190
(1997), pp.37–38, refs/latex/stellmacher-n-group.tex, together with the
standing hypotheses of Section Two, the initial reduction of (2.4), and
the odd-dihedral case of (1.7).

The local companion uses the ambient-retaining Section Eight context.
The legacy public signature is preserved by its exact graph-preserving
`toLocalContext` adapter; supplied Sylow maps and action instances are retained.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SectionTwo
universe u

public theorem eight_two_backward_native_hypotheses_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hnormal : NormalIn
      (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a)) :
    let L := EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep
    SectionTwo.Hypotheses L := by
  let h := ctx.sectionSeven
  let P := GAt ctx.Γ ctx.criticalPath.a
  let L := EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep
  obtain ⟨hLN, _hgen, T, hT, _hobstruction⟩ :=
    eight_two_local_setup_of_core_intersection_normal_local ctx hnormal
  have hsolv : Group.IsSolvable P := (SevenSix.edge_local_data h ctx.Γ ctx.criticalPath).1.2
  let _ : Group.IsSolvable P := hsolv
  let _ : (L.subgroupOf P).Normal := hLN.2
  let equiv : L.subgroupOf P ≃* L := Subgroup.subgroupOfEquivOfLe hLN.1
  have hchar := characteristicTwo_normal_subgroup hsolv
    (SevenSix.edge_characteristic_data h ctx.Γ ctx.criticalPath).1 (L.subgroupOf P)
  have hcharL : Subgroup.centralizer (pCore 2 L : Set L) ≤ pCore 2 L := by
    intro element helement
    have hpre : equiv.symm element ∈ pCore 2 (L.subgroupOf P) := by
      apply hchar
      rw [Subgroup.mem_centralizer_iff]
      intro coreElement hcoreElement
      apply equiv.injective
      simpa only [map_mul, equiv.apply_symm_apply] using
        Subgroup.mem_centralizer_iff.mp helement (equiv coreElement)
          (by rw [← pCore_map_iso 2 equiv]; exact ⟨coreElement, hcoreElement, rfl⟩)
    rw [← pCore_map_iso 2 equiv]
    exact ⟨equiv.symm element, hpre, equiv.apply_symm_apply element⟩
  have hTne : (T : Subgroup L) ≠ ⊥ := by
    intro hbot
    have hQbot : QAt ctx.Γ ctx.criticalPath.firstStep = ⊥ := by
      rw [← hT, hbot, Subgroup.map_bot]
    apply (SevenSix.edge_local_data h ctx.Γ ctx.criticalPath).2.1.1.2.2.1
    exact (ctx.Γ.twoCoreAt_def ctx.criticalPath.firstStep).symm.trans hQbot
  have heven : Even (Nat.card L) := by
    have hdvd : 2 ∣ Nat.card T := T.isPGroup'.card_eq_or_dvd.resolve_left
      (fun hcard => hTne (Subgroup.card_eq_one.mp hcard))
    exact even_iff_two_dvd.mpr (hdvd.trans (Subgroup.card_subgroup_dvd_card (T : Subgroup L)))
  exact ⟨Group.isSolvable_of_surjective (f := equiv.toMonoidHom) equiv.surjective,
    heven, hcharL⟩

private theorem native_quotient_of_dihedral
    {G : Type u} [Group G] [Finite G]
    (h : SectionTwo.Hypotheses G) (T : Sylow 2 G)
    (hcharacteristic : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup G).subtype).Normal)
    (hunique : IsUniqueMaximalContaining (T : Subgroup G) (⊤ : Subgroup G))
    (n : ℕ) (hn : Odd n)
    (eD : (G ⧸ pCore 2 G) ≃* DihedralGroup n) :
    ∃ q : G →* ULift.{u} (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
      Function.Surjective q ∧ q.ker = cSubgroup T := by
  classical
  obtain ⟨hcore, hnot, _⟩ := two_four_initial_reduction h T hcharacteristic hunique
  let _ : (vSubgroup T).Normal := Subgroup.normalClosure_normal
  let C := cSubgroup T
  let _ : C.Normal := by
    dsimp [C, cSubgroup]
    infer_instance
  let X := G ⧸ C
  let quotient : G →* X := QuotientGroup.mk' C
  have hsurj : Function.Surjective quotient := QuotientGroup.mk'_surjective C
  have hker : quotient.ker = cSubgroup T := QuotientGroup.ker_mk' C
  have hJ : (elementaryAbelianMaxJ (T : Subgroup G)).map quotient ≠ ⊥ := by
    intro hbot
    apply hnot
    apply Subgroup.le_centralizer_iff.mp
    change elementaryAbelianMaxJ (T : Subgroup G) ≤ cSubgroup T
    rw [← hker]
    exact (Subgroup.map_eq_bot_iff _).mp hbot
  let _ : IsElementaryAbelian 2 (vSubgroup T) :=
    (vSubgroup_le_twoCore_and_elementaryAbelian h T).2
  let _ := quotientConjugationAction T quotient hsurj hker
  have haction := quotientConjugationAction_hypotheses h T quotient hsurj hker hJ
  let barT : Sylow 2 X := T.mapSurjective hsurj
  have hJaction : SectionOne.oneJ (V := vSubgroup T) (barT : Subgroup X) ≠ ⊥ := by
    intro hbot
    apply hJ
    have hle := elementaryAbelianMaxJ_map_le_oneJ h T quotient hsurj hker
    exact bot_unique (hle.trans_eq hbot)
  have hcoreker : pCore 2 G ≤ quotient.ker := by
    rw [hker, hcore]
    exact inf_le_right
  let factor := QuotientGroup.lift (pCore 2 G) quotient hcoreker
  have hfactor : Function.Surjective factor :=
    QuotientGroup.lift_surjective_of_surjective _ _ hsurj hcoreker
  let projection : DihedralGroup n →* X := factor.comp eD.symm.toMonoidHom
  obtain ⟨equiv⟩ := SectionOne.isSL2Two_of_odd_dihedral_quotient haction barT
    hJaction n hn projection (hfactor.comp eD.symm.surjective)
  let lifted : X ≃* ULift.{u} (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :=
    equiv.trans MulEquiv.ulift.symm
  refine ⟨lifted.toMonoidHom.comp quotient, lifted.surjective.comp hsurj, ?_⟩
  rw [MonoidHom.ker_comp_of_injective quotient lifted.toMonoidHom lifted.injective, hker]

public theorem eight_two_backward_native_quotient_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlen : 1 < ctx.criticalPath.length)
    (hnormal : NormalIn
      (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a)) :
    let L := EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep
    ∀ T : Sylow 2 L,
      (T : Subgroup L).map L.subtype = QAt ctx.Γ ctx.criticalPath.firstStep →
      SectionTwo.Hypotheses L ∧
        IsUniqueMaximalContaining (T : Subgroup L) (⊤ : Subgroup L) ∧
        ∃ q : L →* ULift.{u} (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
          Function.Surjective q ∧ q.ker = SectionTwo.cSubgroup T := by
  intro L T hT
  have h := eight_two_backward_native_hypotheses_local ctx hnormal
  obtain ⟨hunique, n, ⟨eD⟩⟩ :=
    eight_two_backward_native_core_data_local ctx hcenter hlen hnormal T hT
  obtain ⟨_hLN, hgen, _⟩ := eight_two_local_setup_of_core_intersection_normal_local ctx hnormal
  have hcharacteristic := eight_three_characteristic_obstruction_local ctx L T hT hgen
  exact ⟨h, hunique, native_quotient_of_dihedral h T hcharacteristic hunique
    (3 ^ n) ((by decide : Odd 3).pow) eD⟩


public theorem eight_two_backward_native_hypotheses
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hnormal : NormalIn
      (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a)) :
    let L := EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep
    SectionTwo.Hypotheses L := by
  exact eight_two_backward_native_hypotheses_local ctx.toLocalContext hnormal

public theorem eight_two_backward_native_quotient
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlen : 1 < ctx.criticalPath.length)
    (hnormal : NormalIn
      (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a)) :
    let L := EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep
    ∀ T : Sylow 2 L,
      (T : Subgroup L).map L.subtype = QAt ctx.Γ ctx.criticalPath.firstStep →
      SectionTwo.Hypotheses L ∧
        IsUniqueMaximalContaining (T : Subgroup L) (⊤ : Subgroup L) ∧
        ∃ q : L →* ULift.{u} (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
          Function.Surjective q ∧ q.ker = SectionTwo.cSubgroup T := by
  exact eight_two_backward_native_quotient_local ctx.toLocalContext hcenter hlen hnormal

end Stellmacher.SectionEight
