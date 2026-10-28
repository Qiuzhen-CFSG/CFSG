module
public import Theory.Representation.BinaryPermutation.FivePairExtension
public import Theory.Representation.BinaryOffender.SplitMoved
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# Natural modules on the actual alternating factors of a symmetric-five pair

The paired class-sum section identifies each literal A5 commutator with
its own natural core. The original quotient map restricts to the coordinate
inclusion on that section; its range is the actual moved subspace. Enlarging
the actor to its symmetric factor leaves this same moved space unchanged.

Source: Aschbacher–Smith E.2.3(3), printed pp.216–217.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation.FivePair
open FiveCentralExtension

private theorem core_alternating_moved :
    subspaceCommutator (coreRepresentation (Fin 5)) ⊤ (alternatingGroup (Fin 5)) = ⊤ := by
  apply top_unique
  intro v _
  have hzero : 20 • v = 0 := by
    rw [←Nat.cast_smul_eq_nsmul (R := ZMod 2)]
    change (20 : ZMod 2) • v = 0
    rw [show (20 : ZMod 2) = 0 from rfl,zero_smul]
  have hv : v = ∑ g ∈ cubes, (coreRepresentation (Fin 5) g v-v) := by
    rw [Finset.sum_sub_distrib,core_sum,Finset.sum_const,cubes_card,hzero,sub_zero]
  rw [hv]
  exact Submodule.sum_mem _ fun g hg => Submodule.subset_span
    ⟨g,cubes_even g hg,v,Submodule.mem_top,rfl⟩

/-- The actual first alternating factor moves precisely the first natural plane. -/
theorem action_left_moved :
    subspaceCommutator action ⊤ ((alternatingGroup (Fin 5)).prod ⊥) =
      (LinearMap.inl (ZMod 2) Core Core).range := by
  let p := LinearMap.fst (ZMod 2) Core Core
  let s := LinearMap.inl (ZMod 2) Core Core
  let σ := (coreRepresentation (Fin 5)).comp (MonoidHom.fst Sym Sym)
  have hh := moved_eq_map_of_fixed_kernel_section action σ p s (fun _ => rfl)
    (fun _ _ => by ext <;> simp [s,σ])
    ((alternatingGroup (Fin 5)).prod ⊥) (by
      intro v hv g hg
      have hg2 : g.2 = 1 := hg.2
      apply Prod.ext
      · change coreRepresentation (Fin 5) g.1 v.1 = v.1
        change v.1 = 0 at hv
        simp [hv]
      · change coreRepresentation (Fin 5) g.2 v.2 = v.2
        simp [hg2])
  have hmap : ((alternatingGroup (Fin 5)).prod (⊥ : Subgroup Sym)).map (MonoidHom.fst Sym Sym) =
      alternatingGroup (Fin 5) := by
    ext g
    constructor
    · rintro ⟨a,ha,rfl⟩; exact ha.1
    · intro hg; exact ⟨(g,1),⟨hg,by simp⟩,rfl⟩
  have hc := subspaceCommutator_map_embedding σ (coreRepresentation (Fin 5))
    (MonoidHom.fst Sym Sym) (LinearMap.id : Core →ₗ[ZMod 2] Core)
    (fun _ _ => rfl) ((alternatingGroup (Fin 5)).prod ⊥) ⊤
  simp only [Submodule.map_id,hmap,core_alternating_moved] at hc
  rw [hh,hc,Submodule.map_top]

/-- The actual second alternating factor moves precisely the second natural plane. -/
theorem action_right_moved :
    subspaceCommutator action ⊤ ((⊥ : Subgroup Sym).prod (alternatingGroup (Fin 5))) =
      (LinearMap.inr (ZMod 2) Core Core).range := by
  let p := LinearMap.snd (ZMod 2) Core Core
  let s := LinearMap.inr (ZMod 2) Core Core
  let σ := (coreRepresentation (Fin 5)).comp (MonoidHom.snd Sym Sym)
  have hh := moved_eq_map_of_fixed_kernel_section action σ p s (fun _ => rfl)
    (fun _ _ => by ext <;> simp [s,σ])
    ((⊥ : Subgroup Sym).prod (alternatingGroup (Fin 5))) (by
      intro v hv g hg
      have hg1 : g.1 = 1 := hg.1
      apply Prod.ext
      · change coreRepresentation (Fin 5) g.1 v.1 = v.1
        simp [hg1]
      · change coreRepresentation (Fin 5) g.2 v.2 = v.2
        change v.2 = 0 at hv
        simp [hv])
  have hmap : ((⊥ : Subgroup Sym).prod (alternatingGroup (Fin 5))).map (MonoidHom.snd Sym Sym) =
      alternatingGroup (Fin 5) := by
    ext g
    constructor
    · rintro ⟨a,ha,rfl⟩; exact ha.2
    · intro hg; exact ⟨(1,g),⟨by simp,hg⟩,rfl⟩
  have hc := subspaceCommutator_map_embedding σ (coreRepresentation (Fin 5))
    (MonoidHom.snd Sym Sym) (LinearMap.id : Core →ₗ[ZMod 2] Core)
    (fun _ _ => rfl) ((⊥ : Subgroup Sym).prod (alternatingGroup (Fin 5))) ⊤
  simp only [Submodule.map_id,hmap,core_alternating_moved] at hc
  rw [hh,hc,Submodule.map_top]

/-- Enlarging the first alternating axis to its symmetric factor leaves
its moved natural plane unchanged. -/
theorem action_left_full_moved :
    subspaceCommutator action ⊤ ((⊤ : Subgroup Sym).prod ⊥) =
      (LinearMap.inl (ZMod 2) Core Core).range := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,_,rfl⟩
    refine ⟨coreRepresentation (Fin 5) g.1 v.1-v.1,?_⟩
    have hg2 : g.2 = 1 := hg.2
    apply Prod.ext
    · rfl
    · change 0 = coreRepresentation (Fin 5) g.2 v.2-v.2
      simp [hg2]
  · rw [←action_left_moved]
    apply Submodule.span_mono
    rintro _ ⟨g,hg,v,hv,rfl⟩
    exact ⟨g,⟨mem_top _,hg.2⟩,v,hv,rfl⟩

/-- Enlarging the second alternating axis likewise leaves its moved plane unchanged. -/
theorem action_right_full_moved :
    subspaceCommutator action ⊤ ((⊥ : Subgroup Sym).prod ⊤) =
      (LinearMap.inr (ZMod 2) Core Core).range := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,_,rfl⟩
    refine ⟨coreRepresentation (Fin 5) g.2 v.2-v.2,?_⟩
    have hg1 : g.1 = 1 := hg.1
    apply Prod.ext
    · change 0 = coreRepresentation (Fin 5) g.1 v.1-v.1
      simp [hg1]
    · rfl
  · rw [←action_right_moved]
    apply Submodule.span_mono
    rintro _ ⟨g,hg,v,hv,rfl⟩
    exact ⟨g,⟨hg.1,mem_top _⟩,v,hv,rfl⟩

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
/-- The two literal alternating commutators are natural four-dimensional
modules, realized by sections preserving the original quotient map. -/
theorem exists_moved_sections
    (ρ : Representation (ZMod 2) (Sym × Sym) V)
    (p : V →ₗ[ZMod 2] (Core × Core)) (hp : Function.Surjective p)
    (he : ∀ g v, p (ρ g v) = action g (p v))
    (hk : ∀ v, p v = 0 → ∀ g : Sym × Sym, ρ g v = v) :
    ∃ s₁ s₂ : Core →ₗ[ZMod 2] V,
      (∀ v, p (s₁ v) = (v,0)) ∧ (∀ v, p (s₂ v) = (0,v)) ∧
      (∀ g v, s₁ (coreRepresentation (Fin 5) g.1 v) = ρ g (s₁ v)) ∧
      (∀ g v, s₂ (coreRepresentation (Fin 5) g.2 v) = ρ g (s₂ v)) ∧
      s₁.range = subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 5)).prod ⊥) ∧
      s₂.range = subspaceCommutator ρ ⊤ ((⊥ : Subgroup Sym).prod (alternatingGroup (Fin 5))) := by
  obtain ⟨s,hs,hse⟩ := exists_section ρ p hp he hk
  refine ⟨s.comp (LinearMap.inl _ _ _),s.comp (LinearMap.inr _ _ _),?_,?_,?_,?_,?_,?_⟩
  · exact fun v => hs (v,0)
  · exact fun v => hs (0,v)
  · intro g v
    simpa only [LinearMap.comp_apply,LinearMap.inl_apply,action_apply,map_zero] using hse g (v,0)
  · intro g v
    simpa only [LinearMap.comp_apply,LinearMap.inr_apply,action_apply,map_zero] using hse g (0,v)
  · rw [LinearMap.range_comp]
    simpa only [action_left_moved] using
      (moved_eq_map_of_fixed_kernel_section ρ action p s hs hse
        ((alternatingGroup (Fin 5)).prod ⊥) (fun v hv g _ => hk v hv g)).symm
  · rw [LinearMap.range_comp]
    simpa only [action_right_moved] using
      (moved_eq_map_of_fixed_kernel_section ρ action p s hs hse
        ((⊥ : Subgroup Sym).prod (alternatingGroup (Fin 5))) (fun v hv g _ => hk v hv g)).symm
/-- Both symmetric factors and their alternating residuals have the same
original moved support through the split central extension. -/
theorem full_residual_moved_eq
    (ρ : Representation (ZMod 2) (Sym × Sym) V)
    (p : V →ₗ[ZMod 2] (Core × Core)) (hp : Function.Surjective p)
    (he : ∀ g v, p (ρ g v) = action g (p v))
    (hk : ∀ v, p v = 0 → ∀ g : Sym × Sym, ρ g v = v) :
    subspaceCommutator ρ ⊤ ((⊤ : Subgroup Sym).prod ⊥) =
      subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 5)).prod ⊥) ∧
    subspaceCommutator ρ ⊤ ((⊥ : Subgroup Sym).prod ⊤) =
      subspaceCommutator ρ ⊤ ((⊥ : Subgroup Sym).prod (alternatingGroup (Fin 5))) := by
  obtain ⟨s,hs,hse⟩ := exists_section ρ p hp he hk
  have hm (K : Subgroup (Sym × Sym)) := moved_eq_map_of_fixed_kernel_section
    ρ action p s hs hse K (fun v hv g _ => hk v hv g)
  constructor
  · rw [hm,hm,action_left_full_moved,action_left_moved]
  · rw [hm,hm,action_right_full_moved,action_right_moved]

end BinaryPermutation.FivePair
