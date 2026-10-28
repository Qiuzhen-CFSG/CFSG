module
public import Theory.Representation.BinaryOffender.AmbientNonFF
public import Theory.GroupTheory.SolvableRadical.Transport
public import Theory.GroupTheory.ConjugateSpanSylow
/-!
# Non-FF component orbits inside invariant spaces

The inclusion of a component orbit into a larger invariant space identifies
its restricted action image without altering the original covering kernel.
Best offenders on the containing space therefore fix a non-FF inner orbit,
and faithfulness of its component action forces centralization.

A separate kernel argument shows that detecting a component is enough for
faithfulness when its conjugate orbit contains the two-residual and the
ambient solvable radical is trivial. These results apply to the full seed
orbit on the original U/Z in Chapter14's ComponentSupports development.
Source: Aschbacher--Smith B.1.5(4), F.9.18(6--7),14.6.22,
printed pp.69,326,1038.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- Best offenders on a containing invariant space fix an inner space
whose literal restricted image has no FF offenders. -/
theorem IsBestOffender.fixed_of_nonFF_inside_subrepresentation
    (W : Subrepresentation ρ) {A J : Subgroup G}
    (hA : IsBestOffender W.toRepresentation A) (hAJ : A ≤ J)
    (O : Submodule (ZMod 2) V) (hO : J ≤ subspaceStabilizer ρ O)
    (hOW : O ≤ W.toSubmodule)
    (hn : ¬ IsFFModule (imageRepresentation (invariantSubspace ρ J O hO).toRepresentation)) :
    O ≤ fixedSpace ρ A := by
  let O' := O.comap W.toSubmodule.subtype
  have hO' : J ≤ subspaceStabilizer W.toRepresentation O' := by
    apply le_subspaceStabilizer
    intro j hj v hv
    exact (hO hj v.val).2 hv
  let l : O' ≃ₗ[ZMod 2] O := {
    toFun v := ⟨v.val.val,v.property⟩
    invFun v := ⟨⟨v.val,hOW v.property⟩,v.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hn' : ¬ IsFFModule (imageRepresentation
      (invariantSubspace W.toRepresentation J O' hO').toRepresentation) := by
    intro hf
    apply hn
    exact image_isFFModule_of_equivariant
      (invariantSubspace ρ J O hO).toRepresentation
      (invariantSubspace W.toRepresentation J O' hO').toRepresentation
      (MonoidHom.id J) Function.surjective_id l (fun _ _ => rfl) hf
  have hf := hA.fixed_of_nonFF_invariant_image W.toRepresentation hAJ O' hO' hn'
  intro v hv a
  exact congrArg (fun w : W => w.val) (hf (show (⟨v,hOW hv⟩ : W) ∈ O' from hv) a)

/-- Component centralization from a non-FF orbit survives restriction
to any containing invariant space, with its original inclusion. -/
theorem IsBestOffender.centralizes_of_nonFF_orbit_subrepresentation
    (W : Subrepresentation ρ)
    {K P A : Subgroup G} [IsQuasisimple K] (hz : center K = ⊥)
    (hP : IsPGroup 2 P) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K P I) (hIW : I ≤ W.toSubmodule)
    (hA : IsBestOffender W.toRepresentation A) (hAP : A ≤ P)
    (hn : ¬ IsFFModule (imageRepresentation
      (invariantSubspace ρ (K ⊔ P) (orbitSpan ρ P I)
        (sup_le (orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus)
          (orbitSpan_invariant ρ P I))).toRepresentation)) :
    A ≤ centralizer (K : Set G) := by
  let O := orbitSpan ρ P I
  have hO := orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus
  have hOW : O ≤ W.toSubmodule := orbitSpan_le ρ hIW (by
    apply le_subspaceStabilizer
    intro g hg v hv
    exact W.apply_mem_toSubmodule g hv)
  have hfix := hA.fixed_of_nonFF_inside_subrepresentation ρ W
    (hAP.trans (show P ≤ K ⊔ P from le_sup_right)) O
    (sup_le hO (orbitSpan_invariant ρ P I)) hOW hn
  have hf := orbit_component_faithful ρ hz hP hI
  intro a ha
  apply centralizes_of_fixes_faithful_section ρ K O hO
    (fun k hk h => ?_) (hI.normalizes (hAP ha)) (fun v hv => hfix hv ⟨a,ha⟩)
  have he : (invariantSubspace ρ K O hO).toRepresentation ⟨k,hk⟩ = 1 := by
    ext v
    exact h v v.property
  exact congrArg Subtype.val ((injective_iff_map_eq_one _).mp hf ⟨k,hk⟩ he)

omit [FiniteDimensional (ZMod 2) V] in
/-- A component-detecting action is faithful when its orbit contains the
two-residual and the ambient solvable radical is trivial. -/
theorem faithful_of_detects_component_orbit
    (K P : Subgroup G) (hK : IsComponent G K)
    (hrad : solvableRadical G = ⊥)
    (hres : pResidual 2 G ≤ componentOrbit K P)
    (hdetect : ¬ K ≤ ρ.ker) : Function.Injective ρ := by
  have hcore : pCore 2 G = ⊥ := by
    let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
    exact le_bot_iff.mp ((le_solvableRadical (pCore 2 G) inferInstance inferInstance).trans hrad.le)
  have hc : ρ.ker ≤ centralizer (K : Set G) := by
    rcases hK.normal_dichotomy ρ.ker with h | h
    · exact (hdetect h).elim
    · exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h)
  have horbit : componentOrbit K P ≤ centralizer (ρ.ker : Set G) := by
    rw [componentOrbit, ←conjugateSpanBy_eq_iSup_conj]
    apply conjugateSpanBy_le (le_centralizer_iff.mp hc)
    exact le_top.trans (by rw [normalizer_eq_top])
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  apply bot_unique
  exact ((le_centralizer_iff.mp horbit).trans (centralizer_le hres)).trans
    ((centralizer_le (generalizedFitting_le_pResidual_of_pCore_eq_bot hcore)).trans
      (centralizer_generalizedFitting_le_fitting.trans
        ((le_solvableRadical (fittingSubgroup G) inferInstance inferInstance).trans hrad.le)))
omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- A faithful representation and its literal action image have the same FF property. -/
theorem not_ff_image_of_faithful (hf : Function.Injective ρ)
    (hn : ¬ IsFFModule ρ) : ¬ IsFFModule (imageRepresentation ρ) := by
  let e : G ≃* actionImage ρ := MulEquiv.ofBijective (actionHom ρ)
    ⟨fun x y h => hf (congrArg (imageRepresentation ρ) h),
      ρ.asGroupHom.rangeRestrict_surjective⟩
  intro h
  apply hn
  exact h.map_equivariant _ ρ e.symm.toMonoidHom e.symm.injective
    (LinearEquiv.refl _ _) (by
      intro g v
      have he : actionHom ρ (e.symm g) = g := e.apply_symm_apply g
      exact congrArg (fun x => imageRepresentation ρ x v) he.symm)
end Representation.BinaryOffender
