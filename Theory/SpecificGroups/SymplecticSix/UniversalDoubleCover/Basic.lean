module

public import Theory.SpecificGroups.SymplecticSix.Simplicity
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.CoveringKernelEquiv

/-!
# The canonical universal cover of the binary symplectic six-space group

For the literal matrix group G = Sp₆(2), use the derived subgroup of
F/[F,R], where F is the free group on G and R is the evaluation kernel.
The existing free-central construction supplies finiteness, quasisimplicity
and the full universal property. Its kernel order is not asserted here.

A central extension with a nontrivial element in its kernel and derived
subgroup supplies a lower bound: restrict to the derived subgroup and lift
the canonical universal cover onto it. This is used by the concrete Co₃
commutator witness in the parent module. Kernel comparison also transfers
any eventual order-two calculation to arbitrary chosen universal covers.

Source: Aschbacher–Smith, I.1.1, printed p.407, and the construction from
Aschbacher, section 33, proved in `PerfectCentralCoverExistence`. The Sp₆(2)
row required by A.2.2(4), printed p.33, is omitted from the printed I.1.4;
this module does not infer a multiplier value from that omission.
-/

@[expose] public section

open Theory.GroupTheory
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover
universe u w
/-- The literal binary symplectic matrix group. -/
abbrev Base := Matrix.symplecticGroup (Fin 3) (ZMod 2)
/-- The proved matrix perfectness and simple central quotient. -/
instance base_isQuasisimple : IsQuasisimple Base where
  toIsPerfect := perfect_binary
  simple := isSimpleGroup_binary
/-- The derived subgroup of the tautological free central extension. -/
abbrev CoverGroup := PerfectCentralCovering.UniversalGroup Base
/-- Evaluation on the actual matrices, restricted to the derived subgroup. -/
abbrev projection : CoverGroup →* Base := PerfectCentralCovering.universalProjection Base
/-- The finite quasisimple covering defined by that evaluation. -/
abbrev cover : Covering CoverGroup Base :=
  PerfectCentralCovering.universalQuasisimpleCover Base
/-- Universality in every target universe; no kernel-order hypothesis is used. -/
theorem cover_isUniversal : Covering.IsUniversal.{0, 0, w} cover :=
  PerfectCentralCovering.universalQuasisimpleCover_isUniversal Base

theorem projection_surjective : Function.Surjective projection :=
  PerfectCentralCovering.universalProjection_surjective Base

theorem projection_ker_le_center : projection.ker ≤ Subgroup.center CoverGroup :=
  PerfectCentralCovering.universalProjection_ker_le_center Base

/-- A nontrivial element in the derived subgroup and kernel of a central
extension detects a nontrivial universal kernel. The given extension need
not itself be perfect. -/
theorem kernel_nontrivial_of_central_extension
    {E : Type u} [Group E] (f : E →* Base) (hf : Function.Surjective f)
    (hc : f.ker ≤ Subgroup.center E) (z : E)
    (hz : z ∈ f.ker) (hd : z ∈ commutator E) (hne : z ≠ 1) :
    Nontrivial projection.ker := by
  let d := f.comp (commutator E).subtype
  have hs : Function.Surjective d := by
    have hm : (commutator E).map f = ⊤ := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
      exact Group.IsPerfect.commutator_eq_top
    intro y
    have hy : y ∈ (commutator E).map f := by rw [hm]; trivial
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, hxy⟩
  have hdc : d.ker ≤ Subgroup.center (commutator E) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hc hx) y
  let : Group.IsPerfect (commutator E) :=
    PerfectCentralCovering.commutator_isPerfect_of_surjective_of_ker_le_center f hf hc
  obtain ⟨h, hh, _⟩ := PerfectCentralCovering.universalProjection_existsUnique_lift d hs hdc
  have hsurj : Function.Surjective h :=
    PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect d h
      (hh ▸ PerfectCentralCovering.universalProjection_surjective Base) hdc
  obtain ⟨x, hx⟩ := hsurj ⟨z, hd⟩
  have hxk : x ∈ projection.ker := by
    change PerfectCentralCovering.universalProjection Base x = 1
    rw [← hh]
    change d (h x) = 1
    rw [hx]
    exact hz
  refine ⟨⟨⟨x, hxk⟩, 1, ?_⟩⟩
  intro he
  have he' : x = 1 := congrArg Subtype.val he
  apply hne
  have hv := congrArg Subtype.val hx
  simpa [he'] using hv.symm

/-- Comparison with any chosen universal cover, even when its carrier lies
in a different universe. The commuting square is restricted using the
kernel-comparison API. -/
noncomputable def chosenKernelEquiv
    {L : Type u} [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L Base) (hf : Covering.IsUniversal.{0, u, 0} f) :
    f.toMonoidHom.ker ≃* projection.ker := by
  let a := cover_isUniversal.lift f
  let b := hf.lift cover
  have hba : b.comp a = Covering.id := by
    apply cover_isUniversal.hom_ext cover
    · rw [← Covering.comp_assoc, hf.lift_fac cover, cover_isUniversal.lift_fac f]
    · exact Covering.comp_id cover
  have hinj : Function.Injective a := by
    intro x y hxy
    have hx : b (a x) = x := congrArg (fun q : Covering CoverGroup CoverGroup => q x) hba
    have hy : b (a y) = y := congrArg (fun q : Covering CoverGroup CoverGroup => q y) hba
    exact hx.symm.trans ((congrArg b hxy).trans hy)
  let e := MulEquiv.ofBijective a.toMonoidHom ⟨hinj, a.surjective⟩
  exact (Covering.kerMulEquivOfSquare projection f.toMonoidHom e (MulEquiv.refl Base)
    (fun x => congrArg (fun q : Covering CoverGroup Base => q x)
      (cover_isUniversal.lift_fac f))).symm

/-- Turn an order-two calculation into the required multiplicative equivalence. -/
noncomputable def kernelEquiv_of_card_two (hcard : Nat.card projection.ker = 2) :
    projection.ker ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq hcard (by simp)
end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover
