module

public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Sylow overgroups inside groups of characteristic p

If a subgroup contains the ambient p-core, restriction of its centralizer
bound gives a self-centralizing intrinsic p-core. In particular, this applies
to every subgroup containing an ambient Sylow p-subgroup. Applied inside a
parabolic, this turns proper-overgroup placement and the parabolic radical
calculation into the generalized Fitting bound, without assuming that the
overgroup is itself parabolic or normal.

Source: the characteristic-p argument used in Aschbacher–Smith B.1.13,
printed p.74, with GLS3, Theorem 2.6.5(e).
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- Restrict a self-centralizing prime core to an overgroup of that core. -/
theorem centralizer_pCore_le_of_pCore_le (H : Subgroup G)
    (hc : centralizer (pCore p G : Set G) ≤ pCore p G)
    (hQH : pCore p G ≤ H) :
    centralizer (pCore p H : Set H) ≤ pCore p H := by
  have hQ : (pCore p G).subgroupOf H ≤ pCore p H :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  intro x hx
  apply hQ
  apply hc
  intro q hq
  exact congrArg Subtype.val
    (hx (⟨q, hQH hq⟩ : H) (hQ hq))

/-- An ambient Sylow overgroup lying in a group of characteristic p has
generalized Fitting subgroup equal to its own p-core. -/
theorem generalizedFitting_eq_pCore_of_sylow_overgroup [Finite G]
    (S : Sylow p G) (X P : Subgroup G)
    (hSX : (S : Subgroup G) ≤ X) (hXP : X ≤ P)
    (hc : centralizer (pCore p P : Set P) ≤ pCore p P) :
    generalizedFitting X = pCore p X := by
  have hQ : pCore p P ≤ X.subgroupOf P :=
    (pCore_isPGroup.le_sylow_of_normal (S.subtype (hSX.trans hXP))).trans
      (comap_mono hSX)
  have hX := centralizer_pCore_le_of_pCore_le (X.subgroupOf P) hc hQ
  exact generalizedFitting_eq_pCore_of_selfCentralizing p
    ((Theory.Quasithin.centralizer_pCore_le_iff p
      (subgroupOfEquivOfLe hXP)).mp hX)

end Theory.GroupTheory
