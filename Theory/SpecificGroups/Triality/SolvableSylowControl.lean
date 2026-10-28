module

public import Theory.SpecificGroups.Triality.SolvableSylowControl.RootCapture
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.ParameterRigidity.RankOne
public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.SpecificGroups.Triality.ConcreteBruhat.CartanNormalizer
public import Theory.GroupTheory.SolvableSylowControl.Marked

/-!
# Unrestricted solvable Sylow control for genuine binary triality

Let q > 2. A solvable subgroup containing the full positive Sylow subgroup
lies in the root-defined Borel. For an element in a nonidentity Bruhat cell,
conjugating the overgroup by its left Borel factor puts both U and its Weyl
conjugate in the same solvable subgroup. Root capture supplies a complete
negative folded root subgroup. Together with its positive counterpart, this
contains the image of the faithful pinned SL₂ map. Its field has q or q³
elements, so SL₂ is nontrivial and perfect, a contradiction.

The proved equation N(U) = B and Sylow conjugacy then give intrinsic control
for every supplied Sylow subgroup. No restriction on an odd complement or
prior parabolic containment is required. The exponent-one case is excluded
because the central rank-one group over F₂ is solvable.

Source: GLS3 2.3.4–8 and 2.6.2–7,
`refs/KGroup/GLS3/chapter2.tex`; the Borel placement used in the proof of
Aschbacher–Smith 13.6.6, printed p.927 of `refs/quasithin.pdf`.
-/

public section
noncomputable section
namespace Triality.Standard.SolvableSylowControl
open Parabolics ConcreteBruhat
open Matrix
open scoped MatrixGroups
open OuterOdd.Coverage.ParameterRigidity

private theorem rootField_card_gt_two (P : Parameters) (hq : 2 < P.q) (a : Node) :
    2 < Nat.card (RootField P a) := by
  cases a with
  | arms =>
    rw [card_extensionField]
    exact lt_of_lt_of_le hq (Nat.le_pow (a := P.q) (b := 3) (by decide))
  | central => simpa only [RootField, card_fixedField] using hq

private theorem sl2_not_solvable {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hcard : 2 < Nat.card F) : ¬ Group.IsSolvable SL(2, F) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have h3 : 3 ≤ Fintype.card F := by
    exact Nat.succ_le_of_lt (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨t, ht0, ht1⟩ := ENat.exists_ne_ne_of_three_le (α := F)
    (by rw [ENat.card_eq_coe_fintype_card]; exact_mod_cast h3) 0 1
  let : Group.IsPerfect SL(2, F) := ⟨Matrix.SL2.commutator_eq_top ht0 (by
    intro h
    rcases sq_eq_one_iff.mp h with h | h
    · exact ht1 h
    · exact ht1 (by simpa only [CharTwo.neg_eq] using h))⟩
  let : Nontrivial SL(2, F) := (signed_injective (F := F) true).nontrivial
  exact Group.IsPerfect.not_isSolvable _

private theorem not_solvable_of_negative_roots (P : Parameters) (hp : P.prime = 2)
    (hq : 2 < P.q) (H : Subgroup (Carrier P)) (hU : unipotent P ≤ H)
    (a : Node) (hneg : ∀ t : RootField P a, rootElement P hp false a t ∈ H) :
    ¬ Group.IsSolvable H := by
  intro hsol
  let : Group.IsSolvable H := hsol
  let : CharP (RootField P a) 2 := rootField_charTwo P hp a
  let : Finite (RootField P a) := by cases a <;> dsimp [RootField] <;> infer_instance
  let f := rankOne P hp a
  have hfH : ∀ g, f g ∈ H := by
    intro g
    apply sl2_root_induction (fun g => f g ∈ H) ?_ ?_ ?_ g
    · intro t
      change f (signed true t) ∈ H
      rw [rankOne_signed]
      exact hU (positive_mem_unipotent P hp a t)
    · intro t
      change f (signed false t) ∈ H
      rw [rankOne_signed]
      exact hneg t
    · intro g h hg hh
      simpa only [map_mul] using H.mul_mem hg hh
  have hf : Function.Injective (f.codRestrict H hfH) := by
    intro g h he
    exact rankOne_injective P hp a (congrArg Subtype.val he)
  exact sl2_not_solvable (rootField_card_gt_two P hq a)
    (Group.isSolvable_of_isSolvable_injective hf)

private theorem conjugate_cell_contains_roots {G : Type*} [Group G]
    (U H : Subgroup G) (hU : U ≤ H) (b₁ b₂ n : G)
    (hb₁ : b₁ ∈ Subgroup.normalizer U) (hb₂ : b₂ ∈ Subgroup.normalizer U)
    (hg : b₁ * n * b₂ ∈ H) :
    U ≤ H.map (MulAut.conj b₁⁻¹).toMonoidHom ∧
      U.map (MulAut.conj n).toMonoidHom ≤ H.map (MulAut.conj b₁⁻¹).toMonoidHom := by
  constructor
  · intro u hu
    refine ⟨b₁ * u * b₁⁻¹, hU ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hb₁ u).mp hu
    · change b₁⁻¹ * (b₁ * u * b₁⁻¹) * (b₁⁻¹)⁻¹ = u
      group
  · rintro _ ⟨u, hu, rfl⟩
    have hb₂' : b₂⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
      (Subgroup.normalizer (U : Set G)).inv_mem hb₂
    have hu' : b₂⁻¹ * u * b₂ ∈ U := by
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hb₂' u).mp hu
    refine ⟨(b₁ * n * b₂) * (b₂⁻¹ * u * b₂) * (b₁ * n * b₂)⁻¹,
      H.mul_mem (H.mul_mem hg (hU hu')) (H.inv_mem hg), ?_⟩
    change b₁⁻¹ * ((b₁ * n * b₂) * (b₂⁻¹ * u * b₂) * (b₁ * n * b₂)⁻¹) *
      (b₁⁻¹)⁻¹ = n * u * n⁻¹
    group

/-- In genuine binary triality over a field larger than two, every solvable
overgroup of the full positive subgroup lies in the root-defined Borel. -/
theorem le_borel (P : Parameters) (hp : P.prime = 2) (hq : 2 < P.q)
    (H : Subgroup (Carrier P)) (hsol : Group.IsSolvable H) (hU : unipotent P ≤ H) :
    H ≤ borel P := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  let P := binaryParameters n hn
  intro g hg
  obtain ⟨w, hw⟩ := FixedDescent.exists_mem_cell n hn g
  by_cases hw1 : w = 1
  · subst w
    change g ∈ ConcreteBruhat.cell P rfl 1 at hw
    rw [ConcreteBruhat.cell_one P rfl] at hw
    exact hw
  obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := (mem_cell_iff P rfl w g).mp hw
  let K := H.map (MulAut.conj b₁⁻¹).toMonoidHom
  have hKK := conjugate_cell_contains_roots (unipotent P) H hU b₁ b₂
    (weylRepresentative P rfl w) (borel_le_normalizer_unipotent P rfl hb₁)
    (borel_le_normalizer_unipotent P rfl hb₂) (he ▸ hg)
  obtain ⟨a, ha⟩ := exists_negative_root_le_conjugate P rfl w hw1
  have hns := not_solvable_of_negative_roots P rfl hq K hKK.1 a
    (fun t => hKK.2 (ha t))
  let : Group.IsSolvable H := hsol
  exact (hns (Group.isSolvable_of_surjective
    ((MulAut.conj b₁⁻¹).toMonoidHom.subgroupMap_surjective H))).elim

/-- Solvable Sylow overgroups normalize the very same supplied Sylow subgroup. -/
theorem control (P : Parameters) (hp : P.prime = 2) (hq : 2 < P.q) :
    Theory.GroupTheory.SolvableSylowControl 2 (Carrier P) := by
  apply Theory.GroupTheory.SolvableSylowControl.of_standard
    (unipotentSylow P hp) (borel P)
  · change Subgroup.normalizer ((unipotentSylow P hp : Subgroup (Carrier P)) : Set (Carrier P)) = _
    rw [coe_unipotentSylow]
    exact normalizer_unipotent_eq_borel P hp
  · intro H hsol hU
    rw [coe_unipotentSylow] at hU
    exact le_borel P hp hq H hsol hU

/-- The exponent formulation consumed by the complete binary model catalogue. -/
theorem binary_control (n : ℕ) (hn : 1 < n) :
    Theory.GroupTheory.SolvableSylowControl 2 (Carrier (binaryParameters n (by omega))) := by
  apply control _ rfl
  change 2 < 2 ^ n
  calc
    2 < 2 ^ 2 := by decide
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
end Triality.Standard.SolvableSylowControl
end
