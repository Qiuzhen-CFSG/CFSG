module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentCentralizer
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Components.ActionSylow
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# The original selected component satisfies condition (*)

F.9 identifies the full preimage of C_H-star(V-star) with N_H(V),
so the original Sylow image centralizes V-star. Subnormal restriction
supplies the required Sylow in K-star; the faithful component action
then puts V-hat in a Sylow two-center of X-hat. Combined with the
centralizer transport, this proves every clause of source (*).

The final constructor selects the actual K and constructs its action
before supplying (*). It retains the original point, module, ambient H,
outside-intersection bound and nonsingular containment hypotheses.
The component exclusions, abelian point span and later natural reduction
remain unproved; this result adds no classification assumption.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The original Sylow-star centrality restricts to K-star and then gives
Sylow-centrality in the actual faithful X-hat action. -/
theorem SourceHypothesis.original_action_module_sylow_central
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking) :
    let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
    ∃ R : Sylow 2 a.action.range, U ≤ (R : Subgroup a.action.range) ∧
      U ≤ centralizer (R : Set a.action.range) := by
  let E := D.fullSetup hZ T z
  have hT : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  let T₀ := E.Tstar H hT
  have hcentral : Nonabelian.Setup.star H V ≤ centralizer (T₀ : Set (Nonabelian.Setup.Hstar H)) := by
    apply le_centralizer_iff.mpr
    rintro _ ⟨t,ht,rfl⟩
    have he : (centralizer (Nonabelian.Setup.star H V : Set (Nonabelian.Setup.Hstar H))).comap
        (QuotientGroup.mk' (pCore 2 H)) = (normalizer (V : Set G)).subgroupOf H :=
      (S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn).2.2.2.2
    change t ∈ (centralizer (Nonabelian.Setup.star H V : Set (Nonabelian.Setup.Hstar H))).comap
      (QuotientGroup.mk' (pCore 2 H))
    rw [he]
    exact hTV ht
  obtain ⟨P,hP⟩ := T₀.exists_subgroupOf_eq_of_subnormal (Nonabelian.Setup.star H c.K) c.component.1
  apply a.exists_sylow_module_central P
  apply hcentral.trans
  apply centralizer_le
  rw [hP,subgroupOf_map_subtype]
  exact inf_le_left

/-- The original selected component now satisfies all clauses of source (*),
with the intrinsic quotient centralizer and the literal marked images. -/
theorem SourceHypothesis.original_selectedComponent_with_condition
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H)) :
    ∃ c : (D.fullSetup hZ T z).SelectedComponent H, ∃ a : c.ActionMarking,
      let A := (((D.fullSetup hZ T z).L₁.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
      let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
      let C := centralizer (U : Set a.action.range)
      Nat.card U = 2 ∧ 3 ∣ Nat.card A ∧
      A.subgroupOf C ≤ (pCore 3 (C ⧸ pCore 2 C)).comap (QuotientGroup.mk' (pCore 2 C)) ∧
      ∃ R : Sylow 2 a.action.range, U ≤ (R : Subgroup a.action.range) ∧
        U ≤ centralizer (R : Set a.action.range) := by
  obtain ⟨c,_,_,⟨a⟩⟩ := S.original_selectedComponent_with_action D hZ z hz hTV hTz hbound hns hH hn
  refine ⟨c,a,?_,?_,
    S.original_action_residual_le_centralizer_twoThreeCore D hZ z hz hTV hTz hbound hH hn c a,
    S.original_action_module_sylow_central D hZ z hz hTV hTz hbound hH hn c a⟩
  · rw [Nat.card_congr (subgroupOfEquivOfLe (map_le_range _ _)).toEquiv]
    exact a.module_card
  · rw [Nat.card_congr (subgroupOfEquivOfLe (map_le_range _ _)).toEquiv]
    exact a.residual_three_dvd

end CFSG.Quasithin.Chapter12.Section06
