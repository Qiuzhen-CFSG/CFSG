module

public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.RootConjugacy
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.Reduction

/-!
# Two-central triality involutions and the remaining class reductions

Every nonidentity element of the embedded center of a Sylow two-subgroup
is a long-root involution, provided the permitted witness identifying the
positive subgroup as Sylow. Conjugation transports the actual embedded center
to the positive center; its highest-root parametrization and a concrete Weyl
rotation give conjugacy to the specified pinned long-root element.

For general involutions, the Sylow and square-coordinate reductions leave two
independent calculations: normalize a central-radical involution with nonzero
first short coordinate, and move an arms-radical involution either to the
highest root or to that central-radical case. The final theorem below proves
assembly from these explicit inputs; it does not assert their discharge or
unconditional exhaustion by the two root classes. All statements include q = 2.

Source: the inner triality clauses of Aschbacher–Smith 16.1.4(1), 16.1.6 and
16.5.13–14 (`refs/quasithin.pdf`, printed pp.1171–1172 and 1201–1203), using
the genuine root conventions of GLS3 §§2.4–2.6.
-/

public section
noncomputable section

namespace Triality.Standard.EvenInvolutionGeometry
open Parabolics
variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn

/-- The embedded center of any Sylow has only long-root nonidentity elements. -/
theorem isLongRootInvolution_of_mem_center_sylow
    (S0 : Sylow 2 (BinaryCarrier n hn)) (hS0 : (S0 : Subgroup _) = unipotent P)
    (S : Sylow 2 (BinaryCarrier n hn)) {r : BinaryCarrier n hn}
    (hr : r ∈ (Subgroup.center S).map (S : Subgroup _).subtype)
    (hne : r ≠ 1) : IsLongRootInvolution n hn r := by
  obtain ⟨z, hz, rfl⟩ := hr
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (BinaryCarrier n hn) S S0
  let f := MulAut.conj g
  have hm : (S : Subgroup (BinaryCarrier n hn)).map f.toMonoidHom = unipotent P := by
    have hh := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hS0] at hh
    exact hh
  have hfz : f z.val ∈ unipotent P :=
    hm ▸ Subgroup.mem_map_of_mem f.toMonoidHom z.property
  have hc : f z.val ∈ (Subgroup.center (unipotent P)).map (unipotent P).subtype := by
    refine ⟨⟨f z.val, hfz⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro x
    have hx : x.val ∈ (S : Subgroup (BinaryCarrier n hn)).map f.toMonoidHom :=
      hm.symm ▸ x.property
    obtain ⟨y, hy, hxy⟩ := hx
    apply Subtype.ext
    change x.val * f z.val = f z.val * x.val
    rw [← hxy]
    change f y * f z.val = f z.val * f y
    have hyz : y * z.val = z.val * y :=
      congrArg (fun w : S => w.val) (Subgroup.mem_center_iff.mp hz (⟨y, hy⟩ : S))
    exact (map_mul f y z.val).symm.trans ((congrArg f hyz).trans (map_mul f z.val y))
  have hfn : f z.val ≠ 1 := by
    intro h
    exact hne (f.injective (h.trans (map_one f).symm))
  exact (isLongRootInvolution_of_mem_center_unipotent n hn hc hfn).of_isConj n hn
    (isConj_iff.mpr ⟨g, rfl⟩).symm

/-- The two-central involution clause with the literal embedded Sylow center. -/
theorem involution_mem_center_sylow_isLongRoot
    (S0 : Sylow 2 (BinaryCarrier n hn)) (hS0 : (S0 : Subgroup _) = unipotent P)
    (S : Sylow 2 (BinaryCarrier n hn)) {r : BinaryCarrier n hn}
    (hr : orderOf r = 2)
    (hz : r ∈ (Subgroup.center S).map (S : Subgroup _).subtype) :
    IsLongRootInvolution n hn r := by
  apply isLongRootInvolution_of_mem_center_sylow n hn S0 hS0 S hz
  intro h
  simp [h] at hr

end Triality.Standard.EvenInvolutionGeometry

namespace Triality.Standard.EvenInvolutionGeometry
open Parabolics RadicalCoordinates.Centers Parabolics.CentralRootSquare
variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn

private theorem order_two_of_isConj {r s : BinaryCarrier n hn}
    (hr : orderOf r = 2) (h : IsConj r s) : orderOf s = 2 := by
  obtain ⟨g, hg⟩ := h
  exact (SemiconjBy.orderOf_eq g.val hg).symm.trans hr

/-- Assembly of the involution classification from the two remaining concrete
radical reductions. These premises are not asserted in this module. -/
theorem involution_isLongRoot_or_isShortRoot_of_radical_reductions
    (S0 : Sylow 2 (BinaryCarrier n hn)) (hS0 : (S0 : Subgroup _) = unipotent P)
    (hshort : ∀ u : radical P .central, (firstLayer P rfl u).1 ≠ 0 →
      orderOf u.val = 2 → IsShortRootInvolution n hn u.val)
    (harms : ∀ u : radical P .arms, orderOf u.val = 2 →
      (∃ z : highestRoot P, IsConj u.val z.val) ∨
      (∃ v : radical P .central, (firstLayer P rfl v).1 ≠ 0 ∧ IsConj u.val v.val))
    (r : BinaryCarrier n hn) (hr : orderOf r = 2) :
    IsLongRootInvolution n hn r ∨ IsShortRootInvolution n hn r := by
  obtain ⟨u, hu, hc⟩ | ⟨u, hfirst, hu, hc⟩ :=
    involution_isConj_radical n hn S0 hS0 r hr
  · obtain ⟨z, hz⟩ | ⟨v, hfirst, hv⟩ := harms u hu
    · have hzo := order_two_of_isConj n hn hu hz
      have hzne : z.val ≠ 1 := by
        intro h
        simp [h] at hzo
      exact Or.inl ((isLongRootInvolution_of_mem_highestRoot n hn z.property hzne).of_isConj
        n hn (hc.trans hz).symm)
    · exact Or.inr ((hshort v hfirst (order_two_of_isConj n hn hu hv)).of_isConj
        n hn (hc.trans hv).symm)
  · exact Or.inr ((hshort u hfirst hu).of_isConj n hn hc.symm)

end Triality.Standard.EvenInvolutionGeometry
