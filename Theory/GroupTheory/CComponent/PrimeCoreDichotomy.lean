module

public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore

/-!
# C-components over a prime core

A finite p-perfect group with quasisimple quotient by a normal p-subgroup
is a C-component of itself. Lift the quotient component through the
solvable kernel; its normality and p-group quotient force the lift to be
the whole group. This also proves perfectness, rather than assuming it.

A C-component in a group with trivial p-prime core is either an ordinary
component or has generalized Fitting subgroup equal to its p-core. Any
ordinary component inside it fills it by minimality; otherwise its layer
vanishes and the Fitting prime-core theorem applies.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.3(2)–(4),
pp.41–42; used in the block lifting argument of E.6.23, p.254.
-/

public section

namespace Subgroup
open Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A p-perfect extension of a quasisimple group by a p-group is a
C-component of itself. -/
theorem isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (hG : IsPPerfect p G) [IsQuasisimple (G ⧸ N)] :
    (⊤ : Subgroup G).IsCComponent := by
  let : Group.IsNilpotent N := hN.isNilpotent
  have ht : (⊤ : Subgroup (G ⧸ N)).IsCComponent :=
    (show IsComponent (G ⧸ N) ⊤ from
      ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  obtain ⟨C, hC, he⟩ := ht.exists_map_quotient_eq N
  have hn : C.Normal := cComponent_normal_of_quotient_normal hC N
    (he.symm ▸ inferInstance)
  let := hn
  have hs : C ⊔ N = ⊤ := by
    have hh := congrArg (Subgroup.comap (QuotientGroup.mk' N)) he
    simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] using hh
  have hc : C = ⊤ := hG C hn (isPGroup_quotient_of_sup_eq_top C N hN hs)
  exact hc ▸ hC

/-- Subnormal p-perfect subgroups with quasisimple p-core quotient are
genuine C-components of their ambient group. -/
theorem isCComponent_of_isPPerfect_of_quasisimple_core_quotient
    {B : Subgroup G} (hB : B.IsSubnormal) (hp : IsPPerfect p B)
    [IsQuasisimple (B ⧸ pCore p B)] : B.IsCComponent := by
  have ht := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore p B) pCore_isPGroup hp
  simpa only [← MonoidHom.range_eq_map, range_subtype] using ht.map_subtype hB

/-- With trivial p-prime core, a C-component is ordinary or has F* equal
to its intrinsic p-core. This makes no assertion about a Sylow overgroup. -/
theorem IsCComponent.component_or_generalizedFitting_eq_pCore
    {B : Subgroup G} (hB : B.IsCComponent) (ho : pPrimeCore p G = ⊥) :
    IsComponent G B ∨ generalizedFitting B = pCore p B := by
  by_cases hq : IsQuasisimple B
  · exact Or.inl ⟨hB.subnormal, hq⟩
  · right
    have hE : componentLayer B = ⊥ := by
      apply sSup_eq_bot.mpr
      intro J hJ
      have ht := hB.eq_top_of_isCComponent hJ.isCComponent
      let : IsQuasisimple (⊤ : Subgroup B) := ht ▸ hJ.2
      exact (hq (IsQuasisimple.of_mulEquiv topEquiv)).elim
    rw [generalizedFitting, hE, sup_bot_eq,
      Fitting_eq_pcore B p (hB.subnormal.pPrimeCore_eq_bot ho)]

end Subgroup
