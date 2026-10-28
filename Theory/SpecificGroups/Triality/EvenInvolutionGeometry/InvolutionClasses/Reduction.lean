module

public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.RootElements
public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow.ElementaryPlacement
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.Coordinates
public import Mathlib.GroupTheory.Sylow

/-!
# Reduction of triality involutions to two radical coordinate cases

A cyclic subgroup of order two lies in a Sylow subgroup. Conjugacy of Sylow
subgroups places its generator in the actual positive subgroup, given its
Sylow witness. The checked Geck square obstruction then places the element
in one of the two literal parabolic radicals. If its first short coordinate
vanishes in the central radical, its supported root product lies in the arms
radical as well. Thus only the arms case and the central case with nonzero
first short coordinate remain. No conjugacy classification is assumed here.

Source: GLS3 2.3.6–8 and §§2.4–2.6 (`refs/KGroup/GLS3/chapter2.tex`), for
the inner triality case of Aschbacher–Smith 16.1.4(1)
(`refs/quasithin.pdf`, printed p.1171). The argument includes q = 2.
-/

public section

noncomputable section
namespace Triality.Standard.EvenInvolutionGeometry
open Parabolics RadicalCoordinates PositiveCoordinates Parabolics.CentralRootSquare
variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn

private theorem rootElement_mem_arms_of_firstShort_eq_zero
    (Q : Parameters) (hp : Q.prime = 2) (v : RootOrbitParameters Q .central)
    (hv : v.1 0 = 0) :
    toCarrier Q (LeviCommutators.rootElement Q hp .central v) ∈ radical Q .arms := by
  apply descendedRootSubgroup_le_radical Q hp .arms
  refine ⟨LeviCommutators.rootElement Q hp .central v, ?_, rfl⟩
  change orderedProduct Q (expand Q (extendOrbit Q .central v)) ∈ rootSubgroup Q .arms
  apply orderedProduct_mem_rootSubgroup Q .arms
    ⟨expand Q (extendOrbit Q .central v), ?_⟩
  intro i hi
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by
    change ¬3 ≤ i.val at hi
    omega
  rcases hi' with rfl | rfl | rfl
  · exact hv
  · change fieldFrobenius Q (v.1 0) = 0
    rw [hv, map_zero]
  · change fieldFrobenius Q (fieldFrobenius Q (v.1 0)) = 0
    rw [hv, map_zero, map_zero]

/-- Zero first short coordinate places a central-radical element in the arms radical. -/
theorem mem_armsRadical_of_firstShort_eq_zero
    (Q : Parameters) (hp : Q.prime = 2) (r : radical Q .central)
    (hr : (firstLayer Q hp r).1 = 0) : r.val ∈ radical Q .arms := by
  let v := (coordinates Q hp).symm r
  have hv : v.1 0 = 0 := hr
  have he : (coordinates Q hp v).val = r.val :=
    congrArg Subtype.val ((coordinates Q hp).apply_symm_apply r)
  rw [← he, coordinates_val]
  exact rootElement_mem_arms_of_firstShort_eq_zero Q hp v hv

theorem involution_isConj_unipotent
    (S0 : Sylow 2 (BinaryCarrier n hn)) (hS0 : (S0 : Subgroup _) = unipotent P)
    (r : BinaryCarrier n hn) (hr : orderOf r = 2) :
    ∃ u : unipotent P, orderOf u.val = 2 ∧ IsConj r u.val := by
  have hcyc : IsPGroup 2 (Subgroup.zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr, pow_one])
  obtain ⟨S, hS⟩ := hcyc.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (BinaryCarrier n hn) S S0
  have hm : (S : Subgroup (BinaryCarrier n hn)).map (MulAut.conj g).toMonoidHom =
      unipotent P := by
    have hh := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hS0] at hh
    exact hh
  have hu : MulAut.conj g r ∈ unipotent P :=
    hm ▸ Subgroup.mem_map_of_mem _ (hS (Subgroup.mem_zpowers r))
  refine ⟨⟨MulAut.conj g r, hu⟩, ?_, isConj_iff.mpr ⟨g, rfl⟩⟩
  exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective r).trans hr

/-- Sylow conjugacy and the genuine square obstruction reduce an involution
 to the arms radical or a central-radical element with nonzero first short coordinate. -/
theorem involution_isConj_radical
    (S0 : Sylow 2 (BinaryCarrier n hn)) (hS0 : (S0 : Subgroup _) = unipotent P)
    (r : BinaryCarrier n hn) (hr : orderOf r = 2) :
    (∃ u : radical P .arms, orderOf u.val = 2 ∧ IsConj r u.val) ∨
    (∃ u : radical P .central, (firstLayer P rfl u).1 ≠ 0 ∧
      orderOf u.val = 2 ∧ IsConj r u.val) := by
  obtain ⟨u, hu, hc⟩ := involution_isConj_unipotent n hn S0 hS0 r hr
  have husq : u ^ 2 = 1 := by
    apply Subtype.ext
    exact (hu ▸ pow_orderOf_eq_one u.val)
  obtain ha | hb := TwoRank.unipotent_mem_radical_or_radical_of_square_eq_one n hn u husq
  · exact Or.inl ⟨⟨u.val, ha⟩, hu, hc⟩
  · let v : radical P .central := ⟨u.val, hb⟩
    by_cases hv : (firstLayer P rfl v).1 = 0
    · exact Or.inl ⟨⟨u.val, mem_armsRadical_of_firstShort_eq_zero P rfl v hv⟩, hu, hc⟩
    · exact Or.inr ⟨v, hv, hu, hc⟩

end Triality.Standard.EvenInvolutionGeometry
