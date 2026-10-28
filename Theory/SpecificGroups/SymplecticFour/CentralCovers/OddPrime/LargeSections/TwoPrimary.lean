module

public import Theory.GroupTheory.PerfectCentralInvolutionExtension
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.TwoPrimary.PlaneModel
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.TwoPrimary.PlaneGeometry
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.TwoPrimary.PlaneSplitting
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TransvectionLifts
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.Transfer
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.Reduction
import Mathlib.Tactic.LinearCombination

/-!
# Exclusion of two-primary kernels of odd symplectic covers

For p > 3 the two rank-one plane groups are perfect. A splitting theorem
for central two-group extensions of SL₂(p) gives lifts of both factors in
the full preimage of a marked plane-pair subgroup. Perfectness makes these
lifts commute, and conjugacy of the plane swap to a one-plane sign supplies
an involutory lift of the swap. This constructs a section over the actual
embedded subgroup of odd index.

For an arbitrary finite perfect central cover of Sp₄(p), a central quotient
isolates any nontrivial two-primary part of its kernel. Apply the constructed
local section and transfer to exclude that quotient. Thus the argument
covers arbitrary kernels, including their odd parts and higher powers of two.

The conditional interfaces retain their explicit geometric and rank-one
splitting inputs. `not_dvd_card_kernel` discharges both using the concrete
coordinate-plane construction in `PlaneGeometry` and the central-extension
splitting theorem in `PlaneSplitting`. The range includes p = 5, without any
extra field-size hypothesis.

Source: Aschbacher–Smith A.2.2(2), printed p.33, and I.1.1–4, pp.407–408;
GLS3 §6.1, the canonical C₂ multiplier row and absence of an exceptional
multiplier for the odd prime fields in question. The generic primary
reduction is reused from `PerfectCentralCovering.PrimaryReduction`; its
module has no dependencies on the Held model.
-/

public section

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.TwoPrimary
open PerfectCentralCovering Subgroup
universe u
variable {p : ℕ} [Fact p.Prime]

private theorem plane_perfect (hp : 3 < p) : Group.IsPerfect (Plane p) := by
  have h2 : (2 : ZMod p) ≠ 0 := fun h =>
    Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p)
      ((ZMod.natCast_eq_zero_iff 2 p).mp h)
  have hsq : (2 : ZMod p) ^ 2 ≠ 1 := by
    intro h
    have h3 : (3 : ZMod p) = 0 := by linear_combination h
    exact Nat.not_dvd_of_pos_of_lt (by decide) hp
      ((ZMod.natCast_eq_zero_iff 3 p).mp h3)
  exact ⟨Matrix.SL2.commutator_eq_top h2 hsq⟩

/-- The rank-one splitting input and the marked plane model construct a
section on the actual odd-index subgroup of Sp₄. -/
theorem exists_section_on_plane_model (hp : 3 < p) (m : PlaneModel p)
    (hsplit : ∀ (D : Type u) [Group D] [Finite D] (q : D →* Plane p),
      Function.Surjective q → q.ker ≤ center D → IsPGroup 2 q.ker →
      ∃ s : Plane p →* D, q.comp s = MonoidHom.id _)
    {E : Type u} [Group E] [Finite E]
    (f : Cover E (Sp (ZMod p))) (hk : IsPGroup 2 f.toMonoidHom.ker) :
    ∃ s : m.inclusion.range →* E,
      f.toMonoidHom.comp s = m.inclusion.range.subtype := by
  let : Group.IsPerfect (Plane p) := plane_perfect hp
  let : Group.IsPerfect (Plane p × Plane p) := ⟨by
    change ⁅(⊤ : Subgroup (Plane p × Plane p)), ⊤⁆ = ⊤
    rw [← top_prod_top, commutator_prod_prod]
    change (commutator (Plane p)).prod (commutator (Plane p)) =
      (⊤ : Subgroup (Plane p)).prod ⊤
    simp⟩
  let j : Plane p × Plane p →* Sp (ZMod p) :=
    m.inclusion.comp SemidirectProduct.inl
  have hj : Function.Injective j := m.injective.comp SemidirectProduct.inl_injective
  let jl := j.comp (MonoidHom.inl (Plane p) (Plane p))
  let jr := j.comp (MonoidHom.inr (Plane p) (Plane p))
  have hjl : Function.Injective jl := hj.comp (fun _ _ h => congrArg Prod.fst h)
  have hjr : Function.Injective jr := hj.comp (fun _ _ h => congrArg Prod.snd h)
  obtain ⟨sl, hsl⟩ := exists_lift_of_splits_central_pGroup hsplit
    f.toMonoidHom f.surjective f.ker_le_center hk jl hjl
  obtain ⟨sr, hsr⟩ := exists_lift_of_splits_central_pGroup hsplit
    f.toMonoidHom f.surjective f.ker_le_center hk jr hjr
  obtain ⟨s, hs⟩ := exists_product_lift_of_factor_lifts
    f.toMonoidHom f.ker_le_center j sl sr hsl hsr
  have hn : ((-1, 1) : Plane p × Plane p) ^ 2 = 1 := by
    ext <;> simp
  obtain ⟨t, ht⟩ := exists_lift_semidirect_of_involution_fusion
    f.toMonoidHom f.surjective f.ker_le_center m.action m.inclusion
    s hs (-1, 1) hn m.swap_conjugate
  let e := MonoidHom.ofInjective m.injective
  refine ⟨t.comp e.symm.toMonoidHom, ?_⟩
  apply MonoidHom.ext
  intro x
  change f.toMonoidHom (t (e.symm x)) = x.val
  exact (DFunLike.congr_fun ht (e.symm x)).trans
    (congrArg Subtype.val (e.apply_symm_apply x))

/-- Reduce an arbitrary finite perfect central cover to a central two-group
kernel, split on the actual plane-pair subgroup, and apply transfer.
The rank-one splitting and geometric model remain explicit inputs. -/
theorem not_dvd_card_kernel_of_plane_model (hp : 3 < p) (m : PlaneModel p)
    (hsplit : ∀ (D : Type u) [Group D] [Finite D] (q : D →* Plane p),
      Function.Surjective q → q.ker ≤ center D → IsPGroup 2 q.ker →
      ∃ s : Plane p →* D, q.comp s = MonoidHom.id _)
    {E : Type u} [Group E] [Finite E]
    (f : Cover E (Sp (ZMod p))) : ¬ 2 ∣ Nat.card f.toMonoidHom.ker := by
  intro hd
  let := f.isPerfect
  obtain ⟨N, hN, q, _, hq, hqz, hqp, hqd⟩ :=
    PrimaryReduction.exists_primary_quotient f.toMonoidHom f.surjective f.ker_le_center hd
  let := hN
  let g : Cover (E ⧸ N) (Sp (ZMod p)) := {
    toMonoidHom := q
    surjective := hq
    isPerfect := inferInstance
    ker_le_center := hqz }
  obtain ⟨s, hs⟩ := exists_section_on_plane_model hp m hsplit g hqp
  exact not_dvd_card_kernel_of_section g m.inclusion.range
    m.odd_index.not_two_dvd_nat s hs hqd

/-- Every finite perfect central cover of the actual Sp₄(Fₚ), for p > 3,
has kernel of odd order. The concrete plane-pair geometry and rank-one
splitting discharge all premises of the local section and transfer argument. -/
theorem not_dvd_card_kernel (hp : 3 < p)
    {E : Type u} [Group E] [Finite E]
    (f : Cover E (Sp (ZMod p))) : ¬ 2 ∣ Nat.card f.toMonoidHom.ker := by
  exact not_dvd_card_kernel_of_plane_model hp (planeModel hp)
    (fun D _ _ q hq hc hk => exists_plane_section hp q hq hc hk) f

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.TwoPrimary
