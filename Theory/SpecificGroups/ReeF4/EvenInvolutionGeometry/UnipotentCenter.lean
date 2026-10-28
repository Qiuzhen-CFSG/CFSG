module

public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.UnipotentCenter.Centrality
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.UnipotentCenter.TailIdentification

/-!
# The center of the standard positive Ree subgroup

In the actual model over the field of order `2^(2*m+1)`, the center of the
positive subgroup U is the curve `y₅(t) = centralWord m 4 t`. The established
outer and middle coordinate eliminations leave five curves. Four further
commutator tests eliminate `x₄`, `x₆`, `y₃`, and `y₇`. Conversely the two split
factors of `y₅` commute with every positive root factor. Thus a central
involution is exactly a nonzero point of this curve.

No Sylow, odd-index, involution-classification, or automorphism premise is used.
The independent Sylow identification and conjugacy argument can apply the
standard-U result directly.

Source: Aschbacher–Smith 16.1.6 and the long-root/2-central discussion in
16.5.13, printed pp.1172 and 1201–1202 of `refs/quasithin.pdf`;
root conventions from GLS3 Table 2.4 and 2.4.5(d),
`refs/KGroup/GLS3/chapter2.tex`. All indices in Lean are zero based.
-/

public section
namespace ReeF4.EvenInvolutionGeometry
open Parabolics Subgroup
open NormalizedRootCentralizers.CenterExponent

/-- Every element central in the standard positive subgroup is on the literal
long-root curve, including the identity at parameter zero. -/
theorem eq_longRootElement_of_central_unipotent (m : ℕ) (hm : 1 ≤ m)
    (x : Model m) (hx : x ∈ unipotent m)
    (hc : ∀ u ∈ unipotent m, Commute x u) :
    ∃ t : CoefficientField m, x = longRootElement m t := by
  obtain ⟨p, hp⟩ := exists_positiveWord m x hx
  refine ⟨p.central 1, toSplitGroup_injective m ?_⟩
  rw [hp, longRootElement_coe]
  exact UnipotentCenter.positiveWord_eq_central_fifth m hm p
    (positiveWord_commutes_of_central m x hc p hp)

/-- The exact standard-U central-involution identification. The nonzero
parameter follows from order two, without any Sylow or global class premise. -/
theorem central_involution_eq_longRootElement (m : ℕ) (hm : 1 ≤ m)
    (x : Model m) (hx : x ∈ unipotent m) (ho : orderOf x = 2)
    (hc : ∀ u ∈ unipotent m, Commute x u) :
    ∃ t : CoefficientField m, t ≠ 0 ∧ x = longRootElement m t := by
  obtain ⟨t, ht⟩ := eq_longRootElement_of_central_unipotent m hm x hx hc
  refine ⟨t, ?_, ht⟩
  intro hz
  rw [ht, hz, longRootElement_zero, orderOf_one] at ho
  norm_num at ho

/-- The full center equality in the ambient actual Ree model. -/
theorem unipotent_center_eq_longRootGroup (m : ℕ) (hm : 1 ≤ m) :
    (center (unipotent m)).map (unipotent m).subtype = longRootGroup m := by
  apply le_antisymm
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hc : ∀ u ∈ unipotent m, Commute z.val u := by
      intro u hu
      exact (congrArg Subtype.val (mem_center_iff.mp hz ⟨u, hu⟩)).symm
    obtain ⟨t, ht⟩ := eq_longRootElement_of_central_unipotent m hm z.val z.property hc
    exact (mem_longRootGroup m _).mpr ⟨t, ht.symm⟩
  · intro x hx
    obtain ⟨t, rfl⟩ := (mem_longRootGroup m x).mp hx
    refine ⟨⟨longRootElement m t, longRootElement_mem_unipotent m t⟩,
      mem_center_iff.mpr ?_, rfl⟩
    intro u
    exact Subtype.ext (longRootElement_commute_unipotent m t u u.property).eq.symm

end ReeF4.EvenInvolutionGeometry
