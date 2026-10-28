module

public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# A quasisimple subgroup at the bottom of two normal two-quotients

Suppose L is normal in N, N is normal in G, L is quasisimple, both
N/L and G/N are two-groups, and O₂(G) = 1. Perfectness identifies L
with the two-residual of N, so its image is normal in G. The two
indices multiply, and the quasisimple two-quotient theorem identifies
that image with F*(G). It is also the literal two-residual of G.

This retains the actual inclusion maps used in the F.6.18/B.5.1
comparison in Aschbacher–Smith, 15.4.18, printed p.1163.
-/

public section
open Subgroup
namespace Theory.GroupTheory

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro H hH hq
  let : H.Normal := hH
  by_contra hne
  let : Nontrivial (A ⧸ H) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (A ⧸ H) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective H)
  let : Group.IsNilpotent (A ⧸ H) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (A ⧸ H) inferInstance

variable {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (L : Subgroup N) [L.Normal]
    [IsQuasisimple L]

/-- Normality in G is obtained from characteristicity in N; normality in N
alone would not suffice. -/
theorem normalTwoTower_normal (hNL : IsPGroup 2 (N ⧸ L)) :
    (L.map N.subtype).Normal := by
  let : L.Characteristic := characteristic_of_isPPerfect_quotient L
    perfect_twoPerfect hNL
  infer_instance

/-- The actual ambient quotient by the embedded component is a two-group. -/
theorem normalTwoTower_quotient (hNL : IsPGroup 2 (N ⧸ L))
    (hGN : IsPGroup 2 (G ⧸ N)) :
    let := normalTwoTower_normal N L hNL
    IsPGroup 2 (G ⧸ L.map N.subtype) := by
  let := normalTwoTower_normal N L hNL
  obtain ⟨a, ha⟩ := hNL.exists_card_eq
  obtain ⟨b, hb⟩ := hGN.exists_card_eq
  apply IsPGroup.of_card (n := a + b)
  rw [← index_eq_card, index_map_subtype, index_eq_card L,
    index_eq_card N, ha, hb, pow_add]

/-- Identify F*(G), with equality of embedded subgroups, not just abstract
isomorphism of the two components. -/
theorem normalTwoTower_fitting (hNL : IsPGroup 2 (N ⧸ L))
    (hGN : IsPGroup 2 (G ⧸ N)) (hcore : pCore 2 G = ⊥) :
    generalizedFitting G = L.map N.subtype := by
  let := normalTwoTower_normal N L hNL
  let : IsQuasisimple (L.map N.subtype) := IsQuasisimple.of_mulEquiv
    (L.equivMapOfInjective N.subtype N.subtype_injective)
  exact generalizedFitting_eq_of_quasisimple_two_quotient _
    (normalTwoTower_quotient N L hNL hGN) hcore

/-- The same embedded subgroup is O²(G). -/
theorem normalTwoTower_residual (hNL : IsPGroup 2 (N ⧸ L))
    (hGN : IsPGroup 2 (G ⧸ N)) : pResidual 2 G = L.map N.subtype := by
  let := normalTwoTower_normal N L hNL
  let : IsQuasisimple (L.map N.subtype) := IsQuasisimple.of_mulEquiv
    (L.equivMapOfInjective N.subtype N.subtype_injective)
  exact pResidual_eq_of_isPPerfect _ perfect_twoPerfect
    (normalTwoTower_quotient N L hNL hGN)

end Theory.GroupTheory
