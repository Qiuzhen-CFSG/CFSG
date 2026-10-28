module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RepresentationTheory.Basic

/-!
# Binary permutation modules

The permutation module consists of functions to `ZMod 2`. Its augmentation
kernel is the even-weight core; quotienting by the constant functions gives
the deleted module. The natural module is the image of the core in this quotient.
The augmentation of the all-one vector determines the odd/even dichotomy.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), §B.3, especially Lemma B.3.1.
-/

@[expose] public section

namespace BinaryPermutation

open Module

variable (Ω : Type*) [Fintype Ω]

/-- The full binary permutation module. -/
abbrev Full := Ω → ZMod 2

/-- Coordinate permutation, with the usual left-action convention. -/
def representation : Representation (ZMod 2) (Equiv.Perm Ω) (Full Ω) where
  toFun g := (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) g.symm).toLinearMap
  map_one' := by ext v i; rfl
  map_mul' g h := by ext v i; rfl

omit [Fintype Ω] in
@[simp] theorem representation_apply (g : Equiv.Perm Ω) (v : Full Ω) (i : Ω) :
    representation Ω g v i = v (g.symm i) := rfl

/-- Sum of the coordinates. -/
def augmentation : Full Ω →ₗ[ZMod 2] ZMod 2 where
  toFun v := ∑ i, v i
  map_add' v w := Finset.sum_add_distrib
  map_smul' c v := by simp [Finset.mul_sum]

/-- The even-weight core. -/
def core : Submodule (ZMod 2) (Full Ω) := (augmentation Ω).ker

/-- The fixed all-one vector. -/
def allOne : Full Ω := fun _ => 1

/-- The line of constant vectors. -/
def constants : Submodule (ZMod 2) (Full Ω) := Submodule.span (ZMod 2) {allOne Ω}

/-- The full module modulo its constant line. -/
abbrev Deleted := Full Ω ⧸ constants Ω

/-- The image of the core in the deleted module. -/
def natural : Submodule (ZMod 2) (Deleted Ω) := (core Ω).map (constants Ω).mkQ

@[simp] theorem mem_core (v : Full Ω) :
    v ∈ core Ω ↔ ∑ i, v i = 0 := Iff.rfl

@[simp] theorem augmentation_allOne :
    augmentation Ω (allOne Ω) = (Fintype.card Ω : ZMod 2) := by
  simp [augmentation, allOne]

@[simp] theorem augmentation_permute (g : Equiv.Perm Ω) (v : Full Ω) :
    augmentation Ω (representation Ω g v) = augmentation Ω v := by
  exact Equiv.sum_comp g.symm v

theorem core_invariant (g : Equiv.Perm Ω) {v : Full Ω} (hv : v ∈ core Ω) :
    representation Ω g v ∈ core Ω := by
  change augmentation Ω _ = 0
  rw [augmentation_permute]
  exact hv

omit [Fintype Ω] in
@[simp] theorem permute_allOne (g : Equiv.Perm Ω) :
    representation Ω g (allOne Ω) = allOne Ω := by ext i; rfl

omit [Fintype Ω] in
theorem constants_invariant (g : Equiv.Perm Ω) {v : Full Ω} (hv : v ∈ constants Ω) :
    representation Ω g v ∈ constants Ω := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul, permute_allOne]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem constants_le_core_iff : constants Ω ≤ core Ω ↔ Even (Fintype.card Ω) := by
  rw [constants, Submodule.span_le, Set.singleton_subset_iff]
  change augmentation Ω (allOne Ω) = 0 ↔ _
  rw [augmentation_allOne, ZMod.natCast_eq_zero_iff_even]

theorem core_isCompl_constants (h : Odd (Fintype.card Ω)) :
    IsCompl (core Ω) (constants Ω) := by
  have hsum : augmentation Ω (allOne Ω) = 1 := by
    rw [augmentation_allOne, h.natCast_zmod_two]
  refine ⟨Submodule.disjoint_def.mpr ?_, ?_⟩
  · intro v hv hc
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hc
    have hc : c = 0 := by
      change augmentation Ω (c • allOne Ω) = 0 at hv
      simpa [hsum] using hv
    simp [hc]
  · apply codisjoint_iff.mpr
    apply Submodule.eq_top_iff'.mpr
    intro v
    apply Submodule.mem_sup.mpr
    refine ⟨v - augmentation Ω v • allOne Ω, ?_, augmentation Ω v • allOne Ω, ?_, ?_⟩
    · change augmentation Ω _ = 0
      simp [hsum]
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact sub_add_cancel _ _

theorem augmentation_surjective [Nonempty Ω] : Function.Surjective (augmentation Ω) := by
  classical
  intro c
  let i := Classical.choice (inferInstance : Nonempty Ω)
  refine ⟨Pi.single i c, ?_⟩
  simp [augmentation]

theorem finrank_full : finrank (ZMod 2) (Full Ω) = Fintype.card Ω := by
  simp [Full]

theorem finrank_core [Nonempty Ω] :
    finrank (ZMod 2) (core Ω) = Fintype.card Ω - 1 := by
  have h := (augmentation Ω).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (augmentation_surjective Ω)] at h
  simp only [finrank_top, finrank_self, finrank_full] at h
  change 1 + finrank (ZMod 2) (core Ω) = Fintype.card Ω at h
  omega

omit [Fintype Ω] in
theorem allOne_ne_zero [Nonempty Ω] : allOne Ω ≠ 0 := by
  intro h
  have := congrFun h (Classical.choice (inferInstance : Nonempty Ω))
  exact one_ne_zero this

omit [Fintype Ω] in
theorem finrank_constants [Nonempty Ω] : finrank (ZMod 2) (constants Ω) = 1 :=
  finrank_span_singleton (allOne_ne_zero Ω)

theorem finrank_deleted [Nonempty Ω] :
    finrank (ZMod 2) (Deleted Ω) = Fintype.card Ω - 1 := by
  have h := (constants Ω).finrank_quotient_add_finrank
  rw [finrank_constants, finrank_full] at h
  change finrank (ZMod 2) (Deleted Ω) + 1 = Fintype.card Ω at h
  omega

/-- For odd degree the core fills the deleted module. -/
theorem natural_eq_top (h : Odd (Fintype.card Ω)) : natural Ω = ⊤ := by
  apply (Submodule.map_mkQ_eq_top _ _).mpr
  exact (core_isCompl_constants Ω h).symm.sup_eq_top

/-- The odd-degree core is linearly isomorphic to the deleted module. -/
noncomputable def coreEquivDeleted (h : Odd (Fintype.card Ω)) :
    core Ω ≃ₗ[ZMod 2] Deleted Ω :=
  ((constants Ω).quotientEquivOfIsCompl (core Ω)
    (core_isCompl_constants Ω h).symm).symm

theorem finrank_natural_odd [Nonempty Ω] (h : Odd (Fintype.card Ω)) :
    finrank (ZMod 2) (natural Ω) = Fintype.card Ω - 1 := by
  rw [natural_eq_top Ω h, finrank_top, finrank_deleted]

theorem finrank_natural_even [Nonempty Ω] (h : Even (Fintype.card Ω)) :
    finrank (ZMod 2) (natural Ω) = Fintype.card Ω - 2 := by
  have hr := ((constants Ω).mkQ.domRestrict (core Ω)).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at hr
  rw [(Submodule.comapSubtypeEquivOfLe ((constants_le_core_iff Ω).mpr h)).finrank_eq,
    finrank_constants, finrank_core] at hr
  change finrank (ZMod 2) (natural Ω) + 1 = Fintype.card Ω - 1 at hr
  omega

/-- The coordinate action on the even-weight core. -/
def coreRepresentation : Representation (ZMod 2) (Equiv.Perm Ω) (core Ω) where
  toFun g := (representation Ω g).restrict (fun _ hv => core_invariant Ω g hv)
  map_one' := by ext v i; rfl
  map_mul' g h := by ext v i; rfl

@[simp] theorem coreRepresentation_apply (g : Equiv.Perm Ω) (v : core Ω) :
    (coreRepresentation Ω g v : Full Ω) = representation Ω g v := rfl

/-- The coordinate action modulo the constant line. -/
def deletedRepresentation : Representation (ZMod 2) (Equiv.Perm Ω) (Deleted Ω) where
  toFun g := (constants Ω).mapQ (constants Ω) (representation Ω g)
    (fun _ hv => constants_invariant Ω g hv)
  map_one' := by
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ v => rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ v => rfl

omit [Fintype Ω] in
@[simp] theorem deletedRepresentation_mk (g : Equiv.Perm Ω) (v : Full Ω) :
    deletedRepresentation Ω g ((constants Ω).mkQ v) =
      (constants Ω).mkQ (representation Ω g v) := rfl

theorem natural_invariant (g : Equiv.Perm Ω) {v : Deleted Ω} (hv : v ∈ natural Ω) :
    deletedRepresentation Ω g v ∈ natural Ω := by
  obtain ⟨u, hu, rfl⟩ := hv
  exact ⟨representation Ω g u, core_invariant Ω g hu, rfl⟩

/-- The coordinate action on the natural module. -/
def naturalRepresentation : Representation (ZMod 2) (Equiv.Perm Ω) (natural Ω) where
  toFun g := (deletedRepresentation Ω g).restrict (fun _ hv => natural_invariant Ω g hv)
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun (deletedRepresentation Ω).map_one v.val
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun ((deletedRepresentation Ω).map_mul g h) v.val

@[simp] theorem naturalRepresentation_apply (g : Equiv.Perm Ω) (v : natural Ω) :
    (naturalRepresentation Ω g v : Deleted Ω) = deletedRepresentation Ω g v := rfl

@[simp] theorem coreEquivDeleted_apply (h : Odd (Fintype.card Ω)) (v : core Ω) :
    coreEquivDeleted Ω h v = (constants Ω).mkQ v := rfl

/-- The odd-degree identification with the natural module. -/
noncomputable def coreEquivNatural (h : Odd (Fintype.card Ω)) :
    core Ω ≃ₗ[ZMod 2] natural Ω :=
  (coreEquivDeleted Ω h).trans (LinearEquiv.ofTop _ (natural_eq_top Ω h)).symm

@[simp] theorem coreEquivNatural_apply (h : Odd (Fintype.card Ω)) (v : core Ω) :
    (coreEquivNatural Ω h v : Deleted Ω) = (constants Ω).mkQ v := rfl

/-- The odd-degree identification respects the full symmetric-group action. -/
theorem coreEquivNatural_equivariant (h : Odd (Fintype.card Ω))
    (g : Equiv.Perm Ω) (v : core Ω) :
    coreEquivNatural Ω h (coreRepresentation Ω g v) =
      naturalRepresentation Ω g (coreEquivNatural Ω h v) := by
  apply Subtype.ext
  rfl

theorem core_lt_top [Nonempty Ω] : core Ω < ⊤ := by
  apply lt_of_le_of_ne le_top
  intro heq
  have hd := finrank_core Ω
  rw [heq, finrank_top, finrank_full] at hd
  have hp := Fintype.card_pos (α := Ω)
  omega

theorem constants_lt_core [Nonempty Ω] (h : Even (Fintype.card Ω))
    (hn : 4 ≤ Fintype.card Ω) : constants Ω < core Ω := by
  apply lt_of_le_of_ne ((constants_le_core_iff Ω).mpr h)
  intro heq
  have hd := finrank_constants Ω
  rw [heq, finrank_core] at hd
  omega

end BinaryPermutation
