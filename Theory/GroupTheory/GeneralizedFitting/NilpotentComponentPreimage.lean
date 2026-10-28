module

public import Theory.GroupTheory.CComponent.FittingCentralizer
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.GeneralizedFitting.CentralCoverLift
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
/-!
# Component preimages with nilpotent Fitting preimage

For a surjection whose Fitting preimage is nilpotent, the solvable radical
of a subgroup mapping onto a component is nilpotent: its image is central
in that component, whose center lies in the ambient Fitting subgroup.
An odd kernel also forces its two-core to be central. The literal residual
of a component preimage is a C-component mapping onto the component.

Once these C-components are known to be quasisimple, the final lemma gives
the generalized Fitting image equality. The quasisimplicity deduction
requires additional structure and is deliberately left to the consumer.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.2,
pp.103–104, and the C-component calculus A.3.3, pp.42–43.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {H G : Type*} [Group H] [Group G] [Finite H] [Finite G]

private theorem nilpotent_of_injective {A B : Type*} [Group A] [Group B]
    [Group.IsNilpotent B] (f : A →* B) (hf : Function.Injective f) :
    Group.IsNilpotent A :=
  Subgroup.isNilpotent_of_ker_le_center f
    (by rw [(MonoidHom.ker_eq_bot_iff f).mpr hf]; exact bot_le)

omit [Finite G] in
/-- A nilpotent Fitting preimage is exactly the source Fitting subgroup. -/
theorem fitting_comap_eq_of_nilpotent (f : H →* G) (hf : Function.Surjective f)
    [Group.IsNilpotent ((fittingSubgroup G).comap f)] :
    (fittingSubgroup G).comap f = fittingSubgroup H := by
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, inferInstance⟩
  · apply map_le_iff_le_comap.mp
    exact le_sSup ⟨Normal.map inferInstance f hf,
      Group.nilpotent_of_surjective (f.subgroupMap _) (f.subgroupMap_surjective _)⟩

/-- A component center lies in the ambient Fitting subgroup via its inclusion. -/
theorem IsComponent.center_map_le_fitting {L : Subgroup G} (hL : IsComponent G L) :
    (center L).map L.subtype ≤ fittingSubgroup G := by
  let : CommGroup (center L) := IsMulCommutative.instCommGroup
  exact (map_mono (show center L ≤ fittingSubgroup L from
    le_sSup ⟨inferInstance, inferInstance⟩)).trans
    (fittingSubgroup_map_subtype_le_of_isSubnormal L hL.1)

/-- The radical of any subgroup covering a component lies in the nilpotent
Fitting preimage, and is consequently nilpotent. -/
theorem radical_nilpotent_of_component_image (f : H →* G)
    [Group.IsNilpotent ((fittingSubgroup G).comap f)]
    (C : Subgroup H) (hC : IsComponent G (C.map f)) :
    Group.IsNilpotent (solvableRadical C) := by
  let := hC.2
  have hrad : (solvableRadical C).map (f.subgroupMap C) ≤ center (C.map f) :=
    (map_solvableRadical_le_of_surjective _ (f.subgroupMap_surjective C)).trans
      IsQuasisimple.solvableRadical_le_center
  let j : solvableRadical C →* (fittingSubgroup G).comap f :=
    (C.subtype.comp (solvableRadical C).subtype).codRestrict _ (by
      intro x
      exact hC.center_map_le_fitting
        ⟨(f.subgroupMap C) x, hrad ⟨x, x.property, rfl⟩, rfl⟩)
  exact nilpotent_of_injective j (fun a b he => Subtype.ext (Subtype.ext
    (congrArg (fun z : (fittingSubgroup G).comap f => (z : H)) he)))

/-- Odd kernels make the two-core embed in a quasisimple image; its image is
central, so the two-core itself is central. -/
theorem twoCore_central_of_odd_kernel [IsQuasisimple G]
    (f : H →* G) (hf : Function.Surjective f) (ho : Odd (Nat.card f.ker)) :
    pCore 2 H ≤ center H := by
  have hm : (pCore 2 H).map f ≤ center G :=
    (show (pCore 2 H).map f ≤ pCore 2 G from
      le_sSup ⟨Normal.map inferInstance f hf, pCore_isPGroup.map f⟩).trans
      (IsQuasisimple.pCore_le_center 2)
  have hd : Disjoint (pCore 2 H) f.ker := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [hn]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr ho.not_two_dvd_nat).pow_left n
  have hc : ⁅(⊤ : Subgroup H), pCore 2 H⁆ = ⊥ := by
    apply le_bot_iff.mp
    apply hd.le_bot.trans' (le_inf (commutator_le_right _ _) ?_)
    apply (Subgroup.map_eq_bot_iff _).mp
    rw [map_commutator]
    exact le_bot_iff.mp ((commutator_mono le_top hm).trans
      (commutator_center_right (⊤ : Subgroup G)).le)
  intro x hx
  apply mem_center_iff.mpr
  intro y
  exact (commutatorElement_eq_one_iff_mul_comm.mp
    (mem_bot.mp (hc ▸ commutator_mem_commutator (mem_top y) hx)))

/-- Solvable kernels carry a nilpotent radical onto the target radical. -/
theorem radical_nilpotent_of_surjective (f : H →* G) (hf : Function.Surjective f)
    [Group.IsSolvable f.ker] [Group.IsNilpotent (solvableRadical H)] :
    Group.IsNilpotent (solvableRadical G) := by
  have hm : (solvableRadical H).map f = solvableRadical G := by
    rw [← comap_solvableRadical_eq_of_solvable_ker f hf,
      map_comap_eq_self_of_surjective hf]
  rw [← hm]
  exact Group.nilpotent_of_surjective (f.subgroupMap _) (f.subgroupMap_surjective _)

omit [Finite G] in
/-- The canonical residual of the literal preimage lifts C-components across
any solvable kernel. -/
theorem cComponent_residual_preimage (f : H →* G) (hf : Function.Surjective f)
    [Group.IsSolvable f.ker] {L : Subgroup G} (hL : L.IsCComponent) :
    let C := (solvableResidual (L.comap f)).map (L.comap f).subtype
    C.IsCComponent ∧ C.map f = L := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hb := hL.map_equiv e.symm
  obtain ⟨C, hC, hm, he⟩ := hb.solvableResidual_preimage_eq f.ker
  have hpre : (L.map e.symm.toMonoidHom).comap (QuotientGroup.mk' f.ker) =
      L.comap f := by
    ext x
    change (QuotientGroup.mk' f.ker x ∈ L.map e.symm.toMonoidHom) ↔ f x ∈ L
    rw [mem_map_equiv]
    rfl
  have hmap : C.map f = L := by
    have hh := congrArg (map e.toMonoidHom) hm
    have hcomp : e.toMonoidHom.comp (QuotientGroup.mk' f.ker) = f := rfl
    have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by
      ext x; exact e.apply_symm_apply x
    simpa only [map_map, hcomp, hid, map_id] using hh
  rw [hpre] at he
  exact ⟨he ▸ hC, he ▸ hmap⟩

omit [Finite G] in
/-- Once components lift, the nilpotent Fitting preimage gives equality of
the actual generalized Fitting images. -/
theorem generalizedFitting_map_eq_of_component_lifts (f : H →* G)
    (hf : Function.Surjective f) [Group.IsNilpotent ((fittingSubgroup G).comap f)]
    (hlift : ∀ L, IsComponent G L → ∃ M, IsComponent H M ∧ M.map f = L) :
    (generalizedFitting H).map f = generalizedFitting G := by
  apply le_antisymm (map_generalizedFitting_le_of_surjective f hf)
  apply sup_le
  · rw [← map_comap_eq_self_of_surjective hf (fittingSubgroup G),
      fitting_comap_eq_of_nilpotent f hf]
    exact map_mono (fitting_le_generalizedFitting H)
  · apply sSup_le
    intro L hL
    obtain ⟨M, hM, rfl⟩ := hlift L hL
    exact map_mono (component_le_generalizedFitting H M hM)
end Theory.GroupTheory
