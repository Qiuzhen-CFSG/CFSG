module

public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Solvable
public import Theory.Representation.BinaryOffender.CubicMovedRank
public import Theory.GroupTheory.CComponent.TwoComponent
public import Theory.GroupTheory.PResidual.NormalComplement
public import Theory.Representation.GoldschmidtONan.Basic
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.CentralSectionAction
public import Mathlib.LinearAlgebra.Projection
public import Theory.Representation.BinaryOffender.MovedFaithfulness
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer

/-!
# Original solvable FF natural coordinates and projection

The actual cubic cores move the full natural supports. They lie in the
ambient odd core, so odd-order averaging gives an invariant fixed complement
to the offender moved space. The resulting projection from the original
module is surjective and equivariant under the whole ambient group. Its kernel
is exactly the offender fixed space. Coordinates use the existing internal
factor inclusions and natural intertwiners; paired coordinate axes are proved
to be the original factors, including an actual factor exchange.

Source: Aschbacher–Smith, B.1.8, B.6.9 and E.2.3, printed pp.70,115–117,
216–217 (1 March 2004 manuscript). No projection, splitting or natural chart
is assumed independently of the proved solvable factor witness.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)

private theorem moved_mono_actor {A B : Subgroup G} (h : A ≤ B) :
    subspaceCommutator ρ ⊤ A ≤ subspaceCommutator ρ ⊤ B :=
  Submodule.span_mono (by rintro _ ⟨a,ha,v,hv,rfl⟩; exact ⟨a,h ha,v,hv,rfl⟩)

noncomputable def naturalActorCoordinates :
    offenderSubgroup ρ ≃* (Fin d.count → Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :=
  d.groupProduct.symm.trans (MulEquiv.piCongrRight d.factorModel)

noncomputable def naturalMovedCoordinates :
    subspaceCommutator ρ ⊤ (offenderSubgroup ρ) ≃ₗ[ZMod 2]
      (Fin d.count → Fin 2 → ZMod 2) :=
  d.moduleSum.symm.trans (LinearEquiv.piCongrRight (fun i => d.naturalEquiv i))

/-- The cubic odd core moves the original natural plane. -/
theorem oddCore_moved_eq_support [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (i : Fin d.count) :
    subspaceCommutator ρ ⊤ (d.factorOddCore i) = subspaceCommutator ρ ⊤ (d.factor i) := by
  have hle := moved_mono_actor (ρ := ρ) (d.factorOddCore_le i)
  apply Submodule.eq_of_le_of_finrank_eq hle
  apply le_antisymm (Submodule.finrank_mono hle)
  rw [d.support_finrank]
  exact two_le_finrank_subspaceCommutator_of_card_three ρ _ hf (d.factorOddCore_card i)

include d in
/-- The residual and the full offender subgroup move the same actual subspace. -/
theorem residual_moved_eq [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hr : pResidual 2 G ≤ offenderSubgroup ρ) :
    subspaceCommutator ρ ⊤ (pResidual 2 G) =
      subspaceCommutator ρ ⊤ (offenderSubgroup ρ) := by
  apply le_antisymm (moved_mono_actor (ρ := ρ) hr)
  rw [← d.iSup_support]
  refine iSup_le fun i => ?_
  rw [← d.oddCore_moved_eq_support hf i]
  exact moved_mono_actor (ρ := ρ) (d.factorOddCore_le_residual i)

/-- Each coordinate cubic lies in the actual ambient odd core. -/
theorem factorOddCore_le_ambient_oddCore [Finite G] (i : Fin d.count) :
    d.factorOddCore i ≤ pPrimeCore 2 G := by
  let := offenderSubgroup_normal ρ
  have hs : (d.factor i).IsSubnormal := .step _ _ (d.factor_le_offenderSubgroup i)
    (inferInstance : (offenderSubgroup ρ).Normal).isSubnormal
    (d.factor_normal_in_offenderSubgroup i)
  exact hs.pPrimeCore_map_le

include d in
/-- All natural support is already moved by the odd core. -/
theorem oddCore_moved_eq [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hr : pResidual 2 G ≤ offenderSubgroup ρ) :
    subspaceCommutator ρ ⊤ (pPrimeCore 2 G) =
      subspaceCommutator ρ ⊤ (offenderSubgroup ρ) := by
  apply le_antisymm (moved_mono_actor (ρ := ρ) (pPrimeCore_le_pResidual.trans hr))
  rw [← d.iSup_support]
  refine iSup_le fun i => ?_
  rw [← d.oddCore_moved_eq_support hf i]
  exact moved_mono_actor (d.factorOddCore_le_ambient_oddCore i)

include d in
/-- The source solvable module has its genuine ambient-invariant fixed complement. -/
theorem oddCore_fixed_eq_and_isCompl [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hr : pResidual 2 G ≤ offenderSubgroup ρ) :
    fixedSpace ρ (pPrimeCore 2 G) = fixedSpace ρ (offenderSubgroup ρ) ∧
      IsCompl (fixedSpace ρ (offenderSubgroup ρ))
        (subspaceCommutator ρ ⊤ (offenderSubgroup ρ)) := by
  have ho : Odd (Nat.card (pPrimeCore 2 G)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hc : IsCompl (fixedSpace ρ (pPrimeCore 2 G))
      (subspaceCommutator ρ ⊤ (pPrimeCore 2 G)) :=
    by
      have he : subspaceCommutator ρ ⊤ (pPrimeCore 2 G) =
          Representation.RegularCyclicNormalClosure.displacementSpan ρ (pPrimeCore 2 G) ⊤ := by
        unfold subspaceCommutator Representation.RegularCyclicNormalClosure.displacementSpan
        congr 1
        ext v
        simp only [Set.mem_ofPred_eq]
        constructor <;> rintro ⟨g,hg,w,hw,rfl⟩ <;> exact ⟨g,hg,w,hw,rfl⟩
      rw [he]
      exact Representation.GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) ho
  rw [d.oddCore_moved_eq hf hr] at hc
  have he : fixedSpace ρ (pPrimeCore 2 G) = fixedSpace ρ (offenderSubgroup ρ) := by
    apply le_antisymm
    · intro v hv y
      apply sub_eq_zero.mp
      apply (Submodule.disjoint_def.mp hc.disjoint)
        (ρ y v - v)
      · exact (fixedSpace ρ (pPrimeCore 2 G)).sub_mem
          ((fixedSpace_stable_of_normalizes ρ
            (le_normalizer_of_normal : (⊤ : Subgroup G) ≤ normalizer (pPrimeCore 2 G : Set G))
              (mem_top y) v).mpr hv) hv
      · exact Submodule.subset_span ⟨y,y.property,v,Submodule.mem_top,rfl⟩
    · exact fixedSpace_antitone ρ (pPrimeCore_le_pResidual.trans hr)
  exact ⟨he, he ▸ hc⟩

include d in
/-- The fixed space has the original full moved space as a complement. -/
theorem fixed_isCompl_moved [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hr : pResidual 2 G ≤ offenderSubgroup ρ) :
    IsCompl (fixedSpace ρ (offenderSubgroup ρ))
      (subspaceCommutator ρ ⊤ (offenderSubgroup ρ)) :=
  (d.oddCore_fixed_eq_and_isCompl hf hr).2

include d in
/-- The full offender layer and the two-residual have exactly the same fixed vectors. -/
theorem fixed_residual_eq [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hr : pResidual 2 G ≤ offenderSubgroup ρ) :
    fixedSpace ρ (pResidual 2 G) = fixedSpace ρ (offenderSubgroup ρ) := by
  apply le_antisymm
  · exact (fixedSpace_antitone ρ pPrimeCore_le_pResidual).trans
      (d.oddCore_fixed_eq_and_isCompl hf hr).1.le
  · exact fixedSpace_antitone ρ hr

/-- The full original ambient action on the actual moved support. -/
noncomputable def naturalMovedSubrepresentation : Subrepresentation ρ where
  toSubmodule := subspaceCommutator ρ ⊤ (offenderSubgroup ρ)
  apply_mem_toSubmodule g v hv := by
    let := offenderSubgroup_normal ρ
    exact (subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      (le_normalizer_of_normal : (⊤ : Subgroup G) ≤ normalizer (offenderSubgroup ρ : Set G))
        (mem_top g) v).mpr hv

noncomputable def naturalMovedAction :
    Representation (ZMod 2) G (Fin d.count → Fin 2 → ZMod 2) :=
  d.naturalMovedCoordinates.conjRingEquiv.toMonoidHom.comp
    (naturalMovedSubrepresentation (ρ := ρ)).toRepresentation

noncomputable def naturalMovedProjection [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hr : pResidual 2 G ≤ offenderSubgroup ρ) :
    V →ₗ[ZMod 2] subspaceCommutator ρ ⊤ (offenderSubgroup ρ) :=
  (subspaceCommutator ρ ⊤ (offenderSubgroup ρ)).projectionOnto
    (fixedSpace ρ (offenderSubgroup ρ)) (d.fixed_isCompl_moved hf hr).symm

/-- The canonical projection is equivariant under every original ambient element. -/
theorem naturalMovedProjection_equivariant [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hr : pResidual 2 G ≤ offenderSubgroup ρ)
    (g : G) (v : V) :
    d.naturalMovedProjection hf hr (ρ g v) =
      (naturalMovedSubrepresentation (ρ := ρ)).toRepresentation g
        (d.naturalMovedProjection hf hr v) := by
  let hc := (d.fixed_isCompl_moved hf hr).symm
  obtain ⟨w,hw,c,hc',rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ subspaceCommutator ρ ⊤ (offenderSubgroup ρ) ⊔
      fixedSpace ρ (offenderSubgroup ρ) from hc.sup_eq_top.symm ▸ Submodule.mem_top)
  have hwg : ρ g w ∈ subspaceCommutator ρ ⊤ (offenderSubgroup ρ) :=
    (naturalMovedSubrepresentation (ρ := ρ)).apply_mem_toSubmodule g hw
  have hcg : ρ g c ∈ fixedSpace ρ (offenderSubgroup ρ) := by
    let := offenderSubgroup_normal ρ
    exact (fixedSpace_stable_of_normalizes ρ
      (le_normalizer_of_normal : (⊤ : Subgroup G) ≤ normalizer (offenderSubgroup ρ : Set G))
        (mem_top g) c).mpr hc'
  change _ = (naturalMovedSubrepresentation (ρ := ρ)).toRepresentation g _
  simp only [naturalMovedProjection, map_add, Submodule.projectionOnto_apply_of_mem_left _ hw,
    Submodule.projectionOnto_apply_of_mem_right _ hc', add_zero,
    Submodule.projectionOnto_apply_of_mem_left _ hwg,
    Submodule.projectionOnto_apply_of_mem_right _ hcg]
  rfl

noncomputable def naturalQuotientMap [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hr : pResidual 2 G ≤ offenderSubgroup ρ) :
    V →ₗ[ZMod 2] (Fin d.count → Fin 2 → ZMod 2) :=
  d.naturalMovedCoordinates.toLinearMap.comp (d.naturalMovedProjection hf hr)

theorem naturalQuotientMap_surjective [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hr : pResidual 2 G ≤ offenderSubgroup ρ) :
    Function.Surjective (d.naturalQuotientMap hf hr) :=
  d.naturalMovedCoordinates.surjective.comp (Submodule.projectionOnto_surjective _)

theorem naturalQuotientMap_ker [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hr : pResidual 2 G ≤ offenderSubgroup ρ) :
    (d.naturalQuotientMap hf hr).ker = fixedSpace ρ (offenderSubgroup ρ) := by
  ext v
  change d.naturalMovedCoordinates (d.naturalMovedProjection hf hr v) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  exact Submodule.projectionOnto_apply_eq_zero_iff _

theorem naturalQuotientMap_equivariant [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hr : pResidual 2 G ≤ offenderSubgroup ρ)
    (g : G) (v : V) :
    d.naturalQuotientMap hf hr (ρ g v) = d.naturalMovedAction g
      (d.naturalQuotientMap hf hr v) := by
  change d.naturalMovedCoordinates (d.naturalMovedProjection hf hr (ρ g v)) =
    d.naturalMovedCoordinates ((naturalMovedSubrepresentation (ρ := ρ)).toRepresentation g
      (d.naturalMovedCoordinates.symm (d.naturalMovedCoordinates
        (d.naturalMovedProjection hf hr v))))
  rw [LinearEquiv.symm_apply_apply, d.naturalMovedProjection_equivariant]


theorem naturalMovedAction_coordinates (g : G)
    (w : subspaceCommutator ρ ⊤ (offenderSubgroup ρ)) :
    d.naturalMovedAction g (d.naturalMovedCoordinates w) =
      d.naturalMovedCoordinates ((naturalMovedSubrepresentation (ρ := ρ)).toRepresentation g w) := by
  change d.naturalMovedCoordinates ((naturalMovedSubrepresentation (ρ := ρ)).toRepresentation g
    (d.naturalMovedCoordinates.symm (d.naturalMovedCoordinates w))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- A single original plane has exactly its marked natural coordinate. -/
theorem naturalMovedCoordinates_single (i : Fin d.count)
    (v : subspaceCommutator ρ ⊤ (d.factor i)) :
    d.naturalMovedCoordinates (d.moduleSum (Pi.single i v)) =
      Pi.single i (d.naturalEquiv i v) := by
  change (fun j => d.naturalEquiv j (d.moduleSum.symm (d.moduleSum (Pi.single i v)) j)) = _
  rw [LinearEquiv.symm_apply_apply]
  ext j
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

/-- Original coordinate inclusions intertwine, including their action on every other support. -/
theorem naturalMovedAction_factor (i : Fin d.count) (g : d.factor i)
    (v : Fin d.count → Fin 2 → ZMod 2) :
    d.naturalMovedAction (g : G) v = fun j =>
      if j = i then Representation.specialLinearNatural 2
        (d.factorModel i g) (v j) else v j := by
  classical
  let D := (i : Fin d.count) → subspaceCommutator ρ ⊤ (d.factor i)
  let op : Module.End (ZMod 2) (Fin d.count → Fin 2 → ZMod 2) :=
    LinearMap.pi fun j => if j = i then
      (Representation.specialLinearNatural 2 (d.factorModel i g)).comp (LinearMap.proj j)
      else LinearMap.proj j
  have he : (d.naturalMovedAction g).comp (d.naturalMovedCoordinates.toLinearMap.comp d.moduleSum.toLinearMap) =
      op.comp (d.naturalMovedCoordinates.toLinearMap.comp d.moduleSum.toLinearMap) := by
    apply LinearMap.pi_ext
    intro j w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [d.naturalMovedAction_coordinates]
    change d.naturalMovedCoordinates
      ((naturalMovedSubrepresentation (ρ := ρ)).toRepresentation g
        (d.moduleSum (Pi.single j w))) = op (d.naturalMovedCoordinates (d.moduleSum (Pi.single j w)))
    by_cases hij : j = i
    · subst j
      have ha : (naturalMovedSubrepresentation (ρ := ρ)).toRepresentation g
          (d.moduleSum (Pi.single i w)) = d.moduleSum (Pi.single i
            ((d.naturalEquiv i).symm (Representation.specialLinearNatural 2
              (d.factorModel i g) (d.naturalEquiv i w)))) := by
        apply Subtype.ext
        change ρ g (d.moduleSum (Pi.single i w) : V) = _
        rw [d.moduleSum_single, d.moduleSum_single, d.naturalEquiv_action]
      rw [ha, d.naturalMovedCoordinates_single, LinearEquiv.apply_symm_apply,
        d.naturalMovedCoordinates_single]
      ext k
      by_cases hk : k = i
      · subst k
        simp [op]
      · simp [op,hk]
    · have ha : (naturalMovedSubrepresentation (ρ := ρ)).toRepresentation g
          (d.moduleSum (Pi.single j w)) = d.moduleSum (Pi.single j w) := by
        apply Subtype.ext
        change ρ g (d.moduleSum (Pi.single j w) : V) = _
        rw [d.moduleSum_single, d.factor_fixes_other_support (Ne.symm hij) g w.property]
      rw [ha, d.naturalMovedCoordinates_single]
      ext k
      by_cases hk : k = i
      · subst k
        simp [op,Ne.symm hij]
      · simp [op,hk]
  have hh := LinearMap.congr_fun he (d.moduleSum.symm (d.naturalMovedCoordinates.symm v))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at hh
  rw [hh]
  ext j
  by_cases h : j = i <;> simp [op,h]


/-- The coordinatewise natural action, with no ambient action imposed. -/
noncomputable def coordinateNaturalAction (n : ℕ) :
    Representation (ZMod 2) (Fin n → Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
      (Fin n → Fin 2 → ZMod 2) where
  toFun g := LinearMap.pi fun i =>
    (Representation.specialLinearNatural 2 (g i)).comp (LinearMap.proj i)
  map_one' := by
    apply LinearMap.ext
    intro v
    funext i j
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext i j
    change (Representation.specialLinearNatural 2 (g i * h i) (v i)) j = _
    rw [map_mul]
    rfl

/-- The marked product acts coordinatewise on the same ambient model. -/
theorem naturalMovedAction_natural (g : offenderSubgroup ρ)
    (v : Fin d.count → Fin 2 → ZMod 2) :
    d.naturalMovedAction (g : G) v =
      coordinateNaturalAction d.count (d.naturalActorCoordinates g) v := by
  have he : d.naturalMovedAction.comp d.productInclusion =
      (coordinateNaturalAction d.count).comp (MulEquiv.piCongrRight d.factorModel).toMonoidHom := by
    apply MonoidHom.pi_ext
    intro i a
    apply LinearMap.ext
    intro w
    change d.naturalMovedAction (d.productInclusion (Pi.mulSingle i a)) w = _
    rw [d.productInclusion_single, d.naturalMovedAction_factor]
    ext j k
    by_cases hij : j = i
    · subst j
      simp [coordinateNaturalAction]
    · simp [coordinateNaturalAction,hij]
  have hh := LinearMap.congr_fun (DFunLike.congr_fun he (d.groupProduct.symm g)) v
  simpa only [MonoidHom.comp_apply, productInclusion, MulEquiv.coe_toMonoidHom,
    Subgroup.subtype_apply, MulEquiv.apply_symm_apply, naturalActorCoordinates,
    MulEquiv.trans_apply] using hh


/-- The moved model is faithful, using the actual core-free residual. -/
theorem naturalMovedAction_injective [Finite G] (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (hr : pResidual 2 G ≤ offenderSubgroup ρ) :
    Function.Injective d.naturalMovedAction := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply normal_eq_bot_of_fixes_displacements ρ hf hcore (pResidual 2 G)
    d.naturalMovedAction.ker (Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot hcore)
  intro n hn k hk v
  have hw : ρ k v - v ∈ subspaceCommutator ρ ⊤ (offenderSubgroup ρ) :=
    Submodule.subset_span ⟨k,hr hk,v,Submodule.mem_top,rfl⟩
  have he := d.naturalMovedAction_coordinates n ⟨_,hw⟩
  rw [show d.naturalMovedAction n = 1 from hn, Module.End.one_apply] at he
  exact congrArg Subtype.val (d.naturalMovedCoordinates.injective he.symm)


/-- Count two coordinates are kept as the literal ordered pair. -/
noncomputable def pairActorCoordinates (hc : d.count = 2) :
    offenderSubgroup ρ ≃* (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ×
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :=
  (d.naturalActorCoordinates.trans
    (MulEquiv.arrowCongr (finCongr hc) (MulEquiv.refl _))).trans
      { toEquiv := finTwoArrowEquiv _
        map_mul' _ _ := rfl }

noncomputable def pairSpaceCoordinates (hc : d.count = 2) :
    (Fin d.count → Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :=
  (LinearEquiv.piCongrLeft' (ZMod 2) (fun _ : Fin d.count => Fin 2 → ZMod 2)
    (finCongr hc)).trans (LinearEquiv.finTwoArrow (ZMod 2) _)

noncomputable def pairMovedAction (hc : d.count = 2) :
    Representation (ZMod 2) G ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :=
  (d.pairSpaceCoordinates hc).conjRingEquiv.toMonoidHom.comp d.naturalMovedAction

noncomputable def pairQuotientMap [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hr : pResidual 2 G ≤ offenderSubgroup ρ)
    (hc : d.count = 2) : V →ₗ[ZMod 2] ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :=
  (d.pairSpaceCoordinates hc).toLinearMap.comp (d.naturalQuotientMap hf hr)

theorem pairMovedAction_natural (hc : d.count = 2) (g : offenderSubgroup ρ)
    (v w : Fin 2 → ZMod 2) :
    d.pairMovedAction hc g (v,w) =
      (((d.pairActorCoordinates hc g).1).val.mulVec v,
        ((d.pairActorCoordinates hc g).2).val.mulVec w) := by
  change d.pairSpaceCoordinates hc (d.naturalMovedAction g ((d.pairSpaceCoordinates hc).symm (v,w))) = _
  rw [d.naturalMovedAction_natural]
  rfl

theorem pairQuotientMap_surjective [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hr : pResidual 2 G ≤ offenderSubgroup ρ)
    (hc : d.count = 2) : Function.Surjective (d.pairQuotientMap hf hr hc) :=
  (d.pairSpaceCoordinates hc).surjective.comp (d.naturalQuotientMap_surjective hf hr)

theorem pairQuotientMap_equivariant [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hr : pResidual 2 G ≤ offenderSubgroup ρ)
    (hc : d.count = 2) (g : G) (v : V) :
    d.pairQuotientMap hf hr hc (ρ g v) =
      d.pairMovedAction hc g (d.pairQuotientMap hf hr hc v) := by
  change d.pairSpaceCoordinates hc (d.naturalQuotientMap hf hr (ρ g v)) =
    d.pairSpaceCoordinates hc (d.naturalMovedAction g
      ((d.pairSpaceCoordinates hc).symm (d.pairSpaceCoordinates hc (d.naturalQuotientMap hf hr v))))
  rw [LinearEquiv.symm_apply_apply, d.naturalQuotientMap_equivariant]


theorem pairMovedAction_injective [Finite G] (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (hr : pResidual 2 G ≤ offenderSubgroup ρ)
    (hc : d.count = 2) : Function.Injective (d.pairMovedAction hc) :=
  (d.pairSpaceCoordinates hc).conjRingEquiv.injective.comp
    (d.naturalMovedAction_injective hf hcore hr)

theorem pairQuotientMap_ker [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hr : pResidual 2 G ≤ offenderSubgroup ρ)
    (hc : d.count = 2) : (d.pairQuotientMap hf hr hc).ker =
      fixedSpace ρ (offenderSubgroup ρ) := by
  ext v
  change d.pairSpaceCoordinates hc (d.naturalQuotientMap hf hr v) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  exact iff_of_eq (congrArg (fun W : Submodule (ZMod 2) V => v ∈ W) (d.naturalQuotientMap_ker hf hr))

theorem pair_first_factor (hc : d.count = 2) :
    ((⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))).prod ⊥).map
      ((offenderSubgroup ρ).subtype.comp (d.pairActorCoordinates hc).symm.toMonoidHom) =
        d.factor ((finCongr hc).symm 0) := by
  classical
  apply le_antisymm
  · rintro _ ⟨⟨a,b⟩,hab,rfl⟩
    have hb : b = 1 := hab.2
    subst b
    have he : (d.pairActorCoordinates hc).symm (a,1) =
        d.groupProduct (Pi.mulSingle ((finCongr hc).symm 0)
          ((d.factorModel ((finCongr hc).symm 0)).symm a)) := by
      apply (d.pairActorCoordinates hc).injective
      rw [MulEquiv.apply_symm_apply]
      apply Prod.ext
      · simp [pairActorCoordinates,naturalActorCoordinates, MulEquiv.arrowCongr, finTwoArrowEquiv, piFinTwoEquiv, finCongr]; first | rfl | exact (MulEquiv.apply_symm_apply _ _).symm
      · simp [pairActorCoordinates,naturalActorCoordinates, MulEquiv.arrowCongr, finTwoArrowEquiv, piFinTwoEquiv, finCongr]
    change ((d.pairActorCoordinates hc).symm (a,1) : G) ∈ _
    rw [he,d.groupProduct_single]
    exact Subtype.property _
  · intro a ha
    refine ⟨(d.factorModel ((finCongr hc).symm 0) ⟨a,ha⟩,1),⟨mem_top _,mem_bot.mpr rfl⟩,?_⟩
    change ((d.pairActorCoordinates hc).symm _ : G) = a
    have he : (d.pairActorCoordinates hc).symm
        (d.factorModel ((finCongr hc).symm 0) ⟨a,ha⟩,1) =
        d.groupProduct (Pi.mulSingle ((finCongr hc).symm 0) ⟨a,ha⟩) := by
      apply (d.pairActorCoordinates hc).injective
      rw [MulEquiv.apply_symm_apply]
      apply Prod.ext <;> simp [pairActorCoordinates,naturalActorCoordinates, MulEquiv.arrowCongr, finTwoArrowEquiv, piFinTwoEquiv, finCongr]; rfl
    rw [he,d.groupProduct_single]

theorem pair_second_factor (hc : d.count = 2) :
    ((⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))).prod ⊤).map
      ((offenderSubgroup ρ).subtype.comp (d.pairActorCoordinates hc).symm.toMonoidHom) =
        d.factor ((finCongr hc).symm 1) := by
  classical
  apply le_antisymm
  · rintro _ ⟨⟨a,b⟩,hab,rfl⟩
    have ha : a = 1 := hab.1
    subst a
    have he : (d.pairActorCoordinates hc).symm (1,b) =
        d.groupProduct (Pi.mulSingle ((finCongr hc).symm 1)
          ((d.factorModel ((finCongr hc).symm 1)).symm b)) := by
      apply (d.pairActorCoordinates hc).injective
      rw [MulEquiv.apply_symm_apply]
      apply Prod.ext <;> simp [pairActorCoordinates,naturalActorCoordinates, MulEquiv.arrowCongr, finTwoArrowEquiv, piFinTwoEquiv, finCongr]; first | rfl | exact (MulEquiv.apply_symm_apply _ _).symm
    change ((d.pairActorCoordinates hc).symm (1,b) : G) ∈ _
    rw [he,d.groupProduct_single]
    exact Subtype.property _
  · intro a ha
    refine ⟨(1,d.factorModel ((finCongr hc).symm 1) ⟨a,ha⟩),⟨mem_bot.mpr rfl,mem_top _⟩,?_⟩
    change ((d.pairActorCoordinates hc).symm _ : G) = a
    have he : (d.pairActorCoordinates hc).symm
        (1,d.factorModel ((finCongr hc).symm 1) ⟨a,ha⟩) =
        d.groupProduct (Pi.mulSingle ((finCongr hc).symm 1) ⟨a,ha⟩) := by
      apply (d.pairActorCoordinates hc).injective
      rw [MulEquiv.apply_symm_apply]
      apply Prod.ext <;> simp [pairActorCoordinates,naturalActorCoordinates, MulEquiv.arrowCongr, finTwoArrowEquiv, piFinTwoEquiv, finCongr]; rfl
    rw [he,d.groupProduct_single]


/-- A one-way exchange of a two-factor source family exchanges both factors. -/
theorem pair_factor_exchange (hc : d.count = 2) (g : G)
    (h : (d.factor ((finCongr hc).symm 0)).map (MulAut.conj g).toMonoidHom =
      d.factor ((finCongr hc).symm 1)) :
    (d.factor ((finCongr hc).symm 1)).map (MulAut.conj g).toMonoidHom =
      d.factor ((finCongr hc).symm 0) := by
  obtain ⟨j,hj⟩ := d.exists_factor_map_conj g ((finCongr hc).symm 1)
  have htwo : j = (finCongr hc).symm 0 ∨ j = (finCongr hc).symm 1 := by
    have hh : (finCongr hc) j = 0 ∨ (finCongr hc) j = 1 := by
      have ht : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
      exact ht _
    exact hh.imp (fun hh => (finCongr hc).injective (hh.trans ((finCongr hc).apply_symm_apply 0).symm))
      (fun hh => (finCongr hc).injective (hh.trans ((finCongr hc).apply_symm_apply 1).symm))
  rcases htwo with rfl | rfl
  · exact hj
  · have he := d.factor_injective
      (Subgroup.map_injective (MulAut.conj g).injective (h.trans hj.symm))
    have h01 := (finCongr hc).symm.injective he
    exact (show (0 : Fin 2) ≠ 1 by decide) h01 |>.elim

end CFSG.Quasithin.ChapterB.SolvableFFFactors
