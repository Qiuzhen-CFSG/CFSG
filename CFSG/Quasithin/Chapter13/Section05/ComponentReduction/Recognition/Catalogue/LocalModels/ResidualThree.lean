module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.ComponentAction
public import Theory.SpecificGroups.PSL3Two.InvolutionResidual

/-!
# The L₃(2) residual obstruction on the original source quotient

The actual quotient image of a two-perfect Y ≤ L₁ is still two-perfect.
If the marked involution belongs to the component and that component is
L₃(2), its centralizer cannot contain this nontrivial image. The intrinsic
calculation includes the outer-automorphism quotient, so Y-hat is not
assumed to lie in K-hat. This precedes the later deduction L₁ ≤ K.

The Fitting equality, nontrivial image, centralization and inner marking
are explicit configuration/sieve inputs. The quotient is literally
X/C_X(K*), retaining the original Selected D K and the original Y.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.5.21,
printed pp.923–924 (PDF pp.940–941), conditions (i),(ii) and the L₃(2) step.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels

variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}
  (s : Selected D K) (h : D.Hypothesis) [(componentCentralizer s h).Normal]

/-- A source subgroup's literal image in X/C_X(K*). This agrees definitionally
with the configuration producer's quotient-image convention. -/
noncomputable def sourceHatImage (J : Subgroup G) : Subgroup (Xhat s h) :=
  (J.subgroupOf (X D K)).map (QuotientGroup.mk' (componentCentralizer s h))

/-- The L₃(2) branch contradicts the genuine nontrivial two-residual image.
No containment Y-hat ≤ K-hat or L₁ ≤ K is assumed. -/
theorem source_not_linearThree
    (Y : Subgroup G) (hYL : Y ≤ D.L₁) (hY : IsPPerfect 2 Y)
    (hne : sourceHatImage s h Y ≠ ⊥)
    (hF : sourceHatImage s h K = generalizedFitting (Xhat s h))
    (v : sourceHatImage s h K) (hv : orderOf v = 2)
    (hc : sourceHatImage s h Y ≤ centralizer {(v : Xhat s h)}) :
    ¬ Nonempty (sourceHatImage s h K ≃* Matrix.PSL3Two.PSL) := by
  rintro ⟨e⟩
  have hYX : Y ≤ X D K := hYL.trans (le_sup_left.trans le_sup_right)
  let f := (subgroupOfEquivOfLe hYX).symm
  have hYP : IsPPerfect 2 (Y.subgroupOf (X D K)) :=
    hY.of_surjective f.toMonoidHom f.surjective
  let q := QuotientGroup.mk' (componentCentralizer s h)
  have hhat : IsPPerfect 2 (sourceHatImage s h Y) :=
    hYP.of_surjective (q.subgroupMap (Y.subgroupOf (X D K))) (q.subgroupMap_surjective _)
  exact hne (Matrix.PSL3Two.InvolutionResidual.residual_centralizing_eq_bot_of_fitting
    _ hF (e.trans Matrix.PSL3Two.equiv.symm) v hv _ hhat hc)

/-- The same exclusion with the original subgroup V-hat and its generator
retained. The order-two assertion is derived from the configuration's
cardinality, and condition (ii) supplies centralization of that subgroup. -/
theorem source_not_linearThree_of_marked_actor
    (Y : Subgroup G) (hYL : Y ≤ D.L₁) (hY : IsPPerfect 2 Y)
    (hne : sourceHatImage s h Y ≠ ⊥)
    (hF : sourceHatImage s h K = generalizedFitting (Xhat s h))
    (hcard : Nat.card (sourceHatImage s h D.V) = 2)
    (v : sourceHatImage s h K)
    (hv : zpowers (v : Xhat s h) = sourceHatImage s h D.V)
    (hc : sourceHatImage s h Y ≤ centralizer (sourceHatImage s h D.V : Set (Xhat s h))) :
    ¬ Nonempty (sourceHatImage s h K ≃* Matrix.PSL3Two.PSL) := by
  have ho : orderOf (v : Xhat s h) = 2 := by
    rw [← Nat.card_zpowers, hv, hcard]
  have ho' : orderOf v = 2 :=
    (orderOf_injective (sourceHatImage s h K).subtype Subtype.coe_injective v).symm.trans ho
  apply source_not_linearThree s h Y hYL hY hne hF v ho'
  intro y hy
  apply mem_centralizer_singleton_iff.mpr
  exact (mem_centralizer_iff.mp (hc hy) v (hv ▸ mem_zpowers (v : Xhat s h))).symm

/-- The literal condition (ii) suffices: the source definition
L₁ = O²(L ∩ Gz) discharges two-perfectness, and Y-hat ≠ 1 supplies
nontriviality inside L₁-hat. An arbitrary centralizing Y alone would not
give this contradiction. -/
theorem source_not_linearThree_of_condition_ii
    (Y : Subgroup G) (hYL : Y ≤ D.L₁)
    (hne : sourceHatImage s h Y ≠ ⊥)
    (hF : sourceHatImage s h K = generalizedFitting (Xhat s h))
    (hcard : Nat.card (sourceHatImage s h D.V) = 2)
    (v : sourceHatImage s h K)
    (hv : zpowers (v : Xhat s h) = sourceHatImage s h D.V)
    (hc : sourceHatImage s h D.L₁ ≤ centralizer (sourceHatImage s h D.V : Set (Xhat s h))) :
    ¬ Nonempty (sourceHatImage s h K ≃* Matrix.PSL3Two.PSL) := by
  have hp : IsPPerfect 2 D.L₁ := isPPerfect_embedded_pResidual 2 (D.L ⊓ D.Gz)
  have hYLhat : sourceHatImage s h Y ≤ sourceHatImage s h D.L₁ :=
    map_mono (comap_mono hYL)
  have hnL : sourceHatImage s h D.L₁ ≠ ⊥ := fun he =>
    hne (bot_unique (hYLhat.trans_eq he))
  exact source_not_linearThree_of_marked_actor s h D.L₁ le_rfl hp hnL hF hcard v hv hc

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels
