module

public import Theory.GroupTheory.PGroup.Omega
public import Theory.GroupTheory.PGroup.CentralFourTorsionMetacyclic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Cyclic derived subgroup from central rank-two four-torsion

An identification of the second omega subgroup with `C₄ × C₄` gives exactly
four solutions to `x² = 1`, and bounds every elementary abelian subgroup by
four. This is an intrinsic bound, not an inheritance assertion about normal
subgroups of an ambient group. Centrality of second omega makes all fourth
roots of one central.

The central-fourth-root metacyclic theorem then supplies a cyclic normal
subgroup with cyclic quotient, which contains the derived subgroup. Thus a
finite two-group with central second omega isomorphic to `C₄ × C₄` has cyclic
derived subgroup. Cyclicity of the derived subgroup also passes along
injective homomorphisms, including the change
from a subgroup to its realization inside an overgroup.

This formalizes the cyclic-derived consequence of the metacyclic argument
cited in MacWilliams,
*On 2-groups with no normal abelian subgroups of rank 3*, Trans. AMS 150
(1970), printed p.377, assertion (xvii), referring to Alperin, *Centralizers
of abelian normal subgroups of p-groups*, J. Algebra 1 (1964), pp.110–113.
The metacyclic input is proved in `CentralFourTorsionMetacyclic` through
powerfulness and two generators, rather than assumed from the citation.
-/

open Subgroup

private theorem fourth_power_eq_one_of_square_eq_one {G : Type*} [Group G]
    {x : G} (hx : x ^ 2 = 1) : x ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hx, one_pow]

/-- Central second omega makes every fourth root of one central. -/
public theorem mem_center_of_pow_four_eq_one_of_omega_two_le_center
    {Q : Type*} [Group Q]
    (hcentral : omega Q (p := 2) 2 ≤ center Q)
    {x : Q} (hx : x ^ 4 = 1) : x ∈ center Q :=
  hcentral (subset_closure hx)

/-- Rank-two homocyclic four-torsion gives exactly four square roots of one. -/
public theorem card_square_eq_one_of_omega_two_equiv
    {Q : Type*} [Group Q]
    (e : omega Q (p := 2) 2 ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :
    Nat.card {x : Q // x ^ 2 = 1} = 4 := by
  let f : {x : Q // x ^ 2 = 1} ≃
      {x : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // x ^ 2 = 1} :=
    { toFun := fun x => ⟨e ⟨x, subset_closure
          (fourth_power_eq_one_of_square_eq_one x.property)⟩, by
        rw [← map_pow, ← map_one e]
        congr 1
        exact Subtype.ext x.property⟩
      invFun := fun x => ⟨(e.symm x : Q), by
        have h : (e.symm x) ^ 2 = 1 := by
          rw [← map_pow, x.property, map_one]
        exact congrArg Subtype.val h⟩
      left_inv := fun x => by simp
      right_inv := fun x => by
        apply Subtype.ext
        change e (e.symm x) = x
        exact e.apply_symm_apply x }
  rw [Nat.card_congr f, Nat.card_eq_fintype_card]
  decide

/-- Every elementary abelian subgroup embeds in the four square roots of one.
No normality hypothesis is needed. -/
public theorem elementary_card_le_four_of_omega_two_equiv
    {Q : Type*} [Group Q] [Finite Q]
    (e : omega Q (p := 2) 2 ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    (E : Subgroup Q) [IsElementaryAbelian 2 E] : Nat.card E ≤ 4 := by
  let f : E → {x : Q // x ^ 2 = 1} := fun x =>
    ⟨x, elemPow_eq_one_of_isElementaryAbelian (x : Q) x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : {x : Q // x ^ 2 = 1} => (z : Q)) h
  rw [← card_square_eq_one_of_omega_two_equiv e]
  exact Nat.card_le_card_of_injective f hf

/-- The intrinsic second-omega identification excludes normal elementary eights. -/
public theorem no_normal_elementary_eight_of_omega_two_equiv
    {Q : Type*} [Group Q] [Finite Q]
    (e : omega Q (p := 2) 2 ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :
    ¬ ∃ E : Subgroup Q, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E := by
  rintro ⟨E, -, hE, hcard⟩
  let : IsElementaryAbelian 2 E := hE
  exact (by decide : ¬ (8 : ℕ) ≤ 4)
    (hcard.trans (elementary_card_le_four_of_omega_two_equiv e E))

/-- The cyclic normal subgroup in a metacyclic presentation contains the derived
subgroup, so the latter is cyclic. -/
public theorem isCyclic_commutator_of_cyclic_normal_cyclic_quotient
    {Q : Type*} [Group Q]
    (N : Subgroup Q) [N.Normal] [IsCyclic N] [IsCyclic (Q ⧸ N)] :
    IsCyclic (_root_.commutator Q) := by
  exact isCyclic_of_le (Normal.quotient_commutative_iff_commutator_le.mp
    (inferInstance : IsMulCommutative (Q ⧸ N)))

/-- An injective homomorphism into a group with cyclic derived subgroup also
has cyclic derived subgroup. -/
public theorem MonoidHom.isCyclic_commutator_of_injective
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) [IsCyclic (_root_.commutator H)] :
    IsCyclic (_root_.commutator G) := by
  have hm : (_root_.commutator G).map f ≤ _root_.commutator H := by
    rw [map_commutator_eq]
    exact commutator_mono le_top le_top
  let g : _root_.commutator G →* _root_.commutator H :=
    (f.comp (_root_.commutator G).subtype).codRestrict _
      (fun x => hm (mem_map_of_mem f x.property))
  exact isCyclic_of_injective g (fun x y h =>
    Subtype.ext (hf (congrArg Subtype.val h)))

/-- Transport cyclicity of the derived subgroup to the realization inside an
overgroup, as needed for the four-torsion kernel inside a centralizer. -/
public theorem Subgroup.isCyclic_commutator_subgroupOf_of_le
    {P : Type*} [Group P] {K C : Subgroup P}
    (hKC : K ≤ C) [IsCyclic (_root_.commutator K)] :
    IsCyclic (_root_.commutator (K.subgroupOf C)) := by
  let e : K.subgroupOf C ≃* K := subgroupOfEquivOfLe hKC
  exact e.toMonoidHom.isCyclic_commutator_of_injective e.injective

/-- A finite two-group with central second omega isomorphic to `C₄ × C₄`
has cyclic derived subgroup. -/
public theorem IsPGroup.isCyclic_commutator_of_omega_two_le_center
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (hcentral : omega Q (p := 2) 2 ≤ center Q)
    (e : omega Q (p := 2) 2 ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :
    IsCyclic (_root_.commutator Q) := by
  obtain ⟨N, hN, hcyc, hquot⟩ :=
    hQ.exists_cyclic_normal_cyclic_quotient_of_central_fourth_roots
      (fun _ hx => mem_center_of_pow_four_eq_one_of_omega_two_le_center hcentral hx)
      (card_square_eq_one_of_omega_two_equiv e)
  let := hN
  let := hcyc
  let := hquot
  exact isCyclic_commutator_of_cyclic_normal_cyclic_quotient N

/-- Apply the intrinsic theorem to a subgroup, then realize it inside an
overgroup. In particular, this applies to the four-torsion kernel inside the
centralizer of an elementary subgroup of order four. -/
public theorem Subgroup.isCyclic_commutator_subgroupOf_of_omega_two_le_center
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {K C : Subgroup P} (hKC : K ≤ C)
    (hcentral : omega K (p := 2) 2 ≤ center K)
    (e : omega K (p := 2) 2 ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :
    IsCyclic (_root_.commutator (K.subgroupOf C)) := by
  let := (hP.to_subgroup K).isCyclic_commutator_of_omega_two_le_center hcentral e
  exact isCyclic_commutator_subgroupOf_of_le hKC
