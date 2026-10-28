module

public import CFSG.Quasithin.Chapter1.Defs
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.QuotientActions
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.AmbientExclusion.Homocyclic
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Ambient inputs and the remaining center–Frattini restriction

For a simple QTKE group G and H ∈ H(G), the normalizer of O₂(H) is a
proper two-local containing H. Thus H is proper and SQTK. The image of a
C-component in H/O₂(H) remains a C-component, and the nilpotent A.3.6
branch supplies its actual omega actions without additional hypotheses.

These deductions do not prove Proposition 1.2.1(4d). Condition (E) concerns
maximal two-locals of odd index in G; it cannot be imposed on H/O₂(H), which
has trivial two-core and a nontrivial C-component. The imported homocyclic
reduction proves that, when the Fitting subgroup has just one prime and is
C_(p^a) × C_(p^a), the printed center–Frattini equality is equivalent to a = 1.
All positive exponents are allowed as inputs to that equivalence.

The cited source supplies no ambient argument establishing this exponent
restriction: the proof on p.504 only identifies its four alternatives with
A.3.6, whose proof on p.45 explicitly retains higher homocyclic exponents.
The general ambient equality, including the other nilpotent Sylow shapes,
remains unproved here. No ambient realization of the intrinsic counterexample
is claimed, and neither that counterexample nor these reductions refutes the
full source statement.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Notation 1.0.1
and Definition 1.1.2, pp.499–500; Proposition 1.2.1, pp.503–504; and
A.3.4–A.3.6, pp.43–45.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.AmbientExclusion
open CenterFrattiniSource
universe u

private theorem not_quasisimple_of_nilpotent_fitting
    {X : Type u} [Group X] [Finite X] {C : Subgroup X}
    (hC : C.IsCComponent) (hn : A36Nilpotent C) : ¬ IsQuasisimple C := by
  intro hq
  let := hq
  have ht : generalizedFitting C = ⊤ := top_unique
    (component_le_generalizedFitting C ⊤
      ⟨IsSubnormal.top, IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩)
  let : Group.IsNilpotent (generalizedFitting C) := hn.2.1
  let : Group.IsSolvable (⊤ : Subgroup C) := ht ▸ inferInstance
  exact hC.not_isSolvable (Group.isSolvable_of_surjective
    (f := (Subgroup.topEquiv : (⊤ : Subgroup C) ≃* C).toMonoidHom)
    Subgroup.topEquiv.surjective)

/-- Genuine ambient membership supplies properness and SQTK for the local group.
The nilpotent quotient component has all the actual omega actions. These facts
do not assert the extra equality in Proposition 1.2.1(4d). -/
theorem nilpotent_quotient_facts
    {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G) {H : Subgroup G} (hH : H ∈ Chapter1.H G)
    (hQ : IsSQTK 𝒦 (H ⧸ pCore 2 H)) {L : Subgroup H} (hL : L.IsCComponent)
    (hn : A36Nilpotent (L.map (QuotientGroup.mk' (pCore 2 H))))
    (hc : A36Common (L.map (QuotientGroup.mk' (pCore 2 H)))) :
    H ≠ ⊤ ∧ IsSQTK 𝒦 H ∧
      (L.map (QuotientGroup.mk' (pCore 2 H))).IsCComponent ∧
      ¬ IsQuasisimple (L.map (QuotientGroup.mk' (pCore 2 H))) ∧
      OmegaActionData (L.map (QuotientGroup.mk' (pCore 2 H))) := by
  let R := H.pCoreIn 2
  let N := normalizer (R : Set G)
  have hHN : H ≤ N := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hN : IsTwoLocal N := ⟨R, hH, isPGroup_pCoreIn 2 H, rfl⟩
  let := hG.simple
  have hproper : H ≠ ⊤ := by
    intro ht
    exact twoLocal_ne_top_of_nonabelian_simple hG.nonabelian hN
      (top_unique (ht ▸ hHN))
  have hs : IsSQTK 𝒦 H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
      ((hG.twoLocal_sqtk hN).subgroup (H.subgroupOf N))
  let := pCore_isNilpotent (p := 2) (G := H)
  have hbar := hL.map_quotient (pCore 2 H)
  have hnot := not_quasisimple_of_nilpotent_fitting hbar hn
  exact ⟨hproper, hs, hbar, hnot,
    (strengthened_omega_actions hQ (pCore_quotient_pCore_eq_bot 2) hbar
      ⟨.nilpotent hn, hc⟩).2 hnot⟩

/-- Condition (E) cannot be imposed on this quotient: its trivial two-core
and its nontrivial C-component prevent characteristic two. -/
theorem quotient_not_characteristicTwo_of_cComponent
    {H : Type u} [Group H] [Finite H] {L : Subgroup H} (hL : L.IsCComponent) :
    ¬ HasCharacteristicTwo (H ⧸ pCore 2 H) := by
  let := pCore_isNilpotent (p := 2) (G := H)
  have hbar := hL.map_quotient (pCore 2 H)
  intro hc
  have htb : (⊤ : Subgroup (H ⧸ pCore 2 H)) ≤ ⊥ := by
    intro x _
    have hx : x ∈ centralizer (pCore 2 (H ⧸ pCore 2 H) : Set (H ⧸ pCore 2 H)) := by
      rw [pCore_quotient_pCore_eq_bot]
      exact mem_centralizer_iff.mpr (by intro y hy; change y = 1 at hy; simp [hy])
    simpa only [pCore_quotient_pCore_eq_bot] using hc hx
  exact hbar.ne_bot (bot_unique (le_top.trans htb))

end CFSG.Quasithin.Chapter1.Section02.AmbientExclusion
