module
public import Stellmacher.SL2FrattiniDihedralCore
public import Stellmacher.SectionTwo.NestedSL2TwoGeneration
public import Theory.GroupTheory.SpecificGroups.DihedralQuotientSylow

/-!
# A generating Sylow for a two-subgroup outside the local core

Let G be finite and solvable with nontrivial two-core and nested SL2(2)
Frattini quotient. Every two-subgroup A outside O2(G) generates G together
with some Sylow two-subgroup.

Choose a Sylow R containing A. The ordinary dihedral recognition gives a
core quotient whose Sylow subgroups have order at most two. The nontrivial
image of A is therefore the full image of R, giving A join O2(G)=R.
The existing nested-SL2 generation theorem supplies a second Sylow that
generates G with A. All images refer to the literal two-core quotient.

Source: Stellmacher (8.2), Journal of Algebra 190 (1997), p.37, choice of
the backward neighbor from the opposite critical center;
refs/latex/stellmacher-n-group.tex. This theorem isolates the native group
calculation, without any graph or critical-distance assumption.
-/

namespace Stellmacher.SectionTwo
universe u

public theorem exists_sylow_sup_eq_top_of_outside_nestedSL2Two
    {G : Type u} [Group G] [Finite G]
    (hsolv : Group.IsSolvable G) (hcore : pCore 2 G ≠ ⊥)
    (A : Subgroup G) (hAp : IsPGroup 2 A) (hout : ¬ A ≤ pCore 2 G)
    (hA : IsSL2Two ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G))) :
    ∃ T : Sylow 2 G, A ⊔ (T : Subgroup G) = ⊤ := by
  classical
  obtain ⟨R, hAR⟩ := hAp.exists_le_sylow
  obtain ⟨n, ⟨eD⟩⟩ := dihedral_three_power_core_quotient_of_nested hsolv R hcore hA
  let Q := pCore 2 G
  let q : G →* G ⧸ Q := QuotientGroup.mk' Q
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective Q
  let Rbar := R.mapSurjective hq
  have hcard : Nat.card Rbar ≤ 2 :=
    (odd_dihedral_quotient_sylow (3 ^ n) ((by decide : Odd 3).pow)
      eD.symm.toMonoidHom eD.symm.surjective Rbar).1
  have hmapne : A.map q ≠ ⊥ := by
    intro hb
    apply hout
    have hh := (Subgroup.map_eq_bot_iff A).mp hb
    rwa [QuotientGroup.ker_mk'] at hh
  have hcardA : 2 ≤ Nat.card (A.map q) := by
    have hh := (Subgroup.one_lt_card_iff_ne_bot (A.map q)).mpr hmapne
    omega
  have hm : A.map q = (R : Subgroup G).map q :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hAR) (hcard.trans hcardA)
  have hQR : Q ≤ (R : Subgroup G) :=
    (pCore_isPGroup (p := 2) (G := G)).le_sylow_of_normal R
  have hARQ : A ⊔ Q = (R : Subgroup G) := by
    have hh := congrArg (Subgroup.comap q) hm
    rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq,
      QuotientGroup.ker_mk', sup_eq_left.mpr hQR] at hh
  exact exists_sylow_sup_eq_top_of_nestedSL2Two A R hARQ hA

end Stellmacher.SectionTwo
