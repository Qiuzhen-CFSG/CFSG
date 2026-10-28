module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.NilpotentRadical
/-!
# Lifting components through the nilpotent SQTK presentation

Take the solvable residual C of the literal component preimage. Solvable
kernel transport makes C a C-component with the prescribed component image.
Its radical is nilpotent because it maps into the component center, which
lies in F(G). The odd kernel makes O₂(C) central. Apply the exact earlier
A.3.6 implication to C/O₂(C): its nilpotent radical excludes A.3.6(i), and
A.3.6(ii) gives quasisimplicity. A perfect central cover then makes C itself
quasisimple. This proves B.5.2(3) for the actual homomorphism.

Using the common A.3.6 clauses avoids a separate SL₂ multiplier argument.
The retained premise is exactly A.3.6, produced by `qt-a03-sqtk-structure`;
this conditional family does not assert that earlier classification.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.2,
pp.103–104, and A.3.6, pp.43–45.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentLifting
open Chapter1.Section02
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {K : GroupClass.{u}}

/-- The literal residual of a component preimage is a component. The only
retained earlier classification premise is the exact universal A.3.6 input. -/
theorem residual_preimage_isComponent (hA36 : A36Input K)
    (hsq : IsSQTK K H) (f : H →* G) (hf : Function.Surjective f)
    [Group.IsNilpotent ((fittingSubgroup G).comap f)]
    [Group.IsNilpotent f.ker] (ho : Odd (Nat.card f.ker))
    {L : Subgroup G} (hL : IsComponent G L) :
    let C := (solvableResidual (L.comap f)).map (L.comap f).subtype
    IsComponent H C ∧ C.map f = L := by
  let C := (solvableResidual (L.comap f)).map (L.comap f).subtype
  obtain ⟨hc, he⟩ := cComponent_residual_preimage f hf hL.isCComponent
  change C.IsCComponent at hc
  change C.map f = L at he
  have hi : IsComponent G (C.map f) := he.symm ▸ hL
  let : IsQuasisimple (C.map f) := hi.2
  let : Group.IsPerfect C := hc.perfect
  let : Group.IsNilpotent (solvableRadical C) := radical_nilpotent_of_component_image f C hi
  let r := f.subgroupMap C
  have hr : Odd (Nat.card r.ker) := by
    rw [show r.ker = f.ker.subgroupOf C from ker_subgroupMap C f]
    exact ho.of_dvd_nat (card_comap_dvd_of_injective _ C.subtype C.subtype_injective)
  have hcentral : pCore 2 C ≤ center C :=
    twoCore_central_of_odd_kernel r (f.subgroupMap_surjective C) hr
  let : IsQuasisimple (C ⧸ pCore 2 C) := quasisimple_twoCore_quotient_of_a36 hA36 hsq hc
  have hquasi : IsQuasisimple C :=
    (show PerfectCentralCovering.Cover C (C ⧸ pCore 2 C) from
      { toMonoidHom := QuotientGroup.mk' _
        surjective := QuotientGroup.mk'_surjective _
        isPerfect := inferInstance
        ker_le_center := by rwa [QuotientGroup.ker_mk'] }).isQuasisimple
  exact ⟨⟨hc.subnormal, hquasi⟩, he⟩

/-- Every component lifts through an SQTK surjection with nilpotent Fitting
preimage and odd nilpotent kernel, conditionally on A.3.6. -/
theorem component_lifts (hA36 : A36Input K) (hsq : IsSQTK K H)
    (f : H →* G) (hf : Function.Surjective f)
    [Group.IsNilpotent ((fittingSubgroup G).comap f)]
    [Group.IsNilpotent f.ker] (ho : Odd (Nat.card f.ker)) :
    ∀ L, IsComponent G L → ∃ M, IsComponent H M ∧ M.map f = L := by
  intro L hL
  exact ⟨_, residual_preimage_isComponent hA36 hsq f hf ho hL⟩
end CFSG.Quasithin.ChapterB.ComponentLifting
