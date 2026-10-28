module
public import Theory.Representation.BinaryPermutation.FiveCentralExtension
/-!
# A natural moved subgroup gives the whole five-letter quotient

The central sum of the twenty three-cycle operators is identity on the
natural moved subgroup and has its whole range there. It is therefore an
equivariant projection. Its kernel is exactly the alternating fixed space,
which constructs the original whole-module natural quotient without an
assumed direct-sum decomposition.

Source: Aschbacher–Smith E.2.3(1),(3), printed pp.216–217.
-/
public section
open Representation Representation.BinaryOffender Subgroup
namespace BinaryPermutation.FiveCentralExtension
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
theorem exists_quotient_of_natural_moved
    (ρ : Representation (ZMod 2) Sym V)
    (i : core (Fin 5) →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (he : ∀ g v, i (coreRepresentation (Fin 5) g v) = ρ g (i v))
    (hr : i.range = subspaceCommutator ρ ⊤ (alternatingGroup (Fin 5))) :
    ∃ p : V →ₗ[ZMod 2] core (Fin 5), Function.Surjective p ∧
      (∀ g v, p (ρ g v) = coreRepresentation (Fin 5) g (p v)) ∧
      p.ker = fixedSpace ρ (alternatingGroup (Fin 5)) := by
  have hp_i (v : core (Fin 5)) : projector ρ (i v) = i v := by
    simp only [projector,LinearMap.sum_apply,←he,←map_sum]
    rw [core_sum]
  have hpr (v : V) : projector ρ v ∈ i.range := by
    rw [hr]
    have hz : 20 • v = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
      change (20 : ZMod 2) • v = 0
      rw [show (20 : ZMod 2) = 0 from rfl,zero_smul]
    have hh : projector ρ v = ∑ g ∈ cubes, (ρ g v-v) := by
      simp only [projector,LinearMap.sum_apply,Finset.sum_sub_distrib,Finset.sum_const,cubes_card,hz,sub_zero]
    rw [hh]
    exact Submodule.sum_mem _ fun g hg => Submodule.subset_span
      ⟨g,cubes_even g hg,v,Submodule.mem_top,rfl⟩
  let e := LinearEquiv.ofInjective i hi
  let p := e.symm.toLinearMap.comp ((projector ρ).codRestrict i.range hpr)
  have hip (v : V) : i (p v) = projector ρ v := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨projector ρ v,hpr v⟩)
  have hpi (v : core (Fin 5)) : p (i v) = v := by
    apply hi
    rw [hip,hp_i]
  have hpfix (v : V) : v-projector ρ v ∈ fixedSpace ρ (alternatingGroup (Fin 5)) := by
    intro g
    have hd : ρ (g:Sym) v-v ∈ i.range := by
      rw [hr]
      exact Submodule.subset_span ⟨g,g.property,v,Submodule.mem_top,rfl⟩
    obtain ⟨w,hw⟩ := hd
    have hw' : i w = ρ (g:Sym) v-v := hw
    have hproj : projector ρ (i w) = i w := hp_i w
    have hproj' : projector ρ (ρ (g:Sym) v-v) = ρ (g:Sym) v-v := by
      calc
        projector ρ (ρ (g:Sym) v-v) = projector ρ (i w) := congrArg (projector ρ) hw'.symm
        _ = i w := hproj
        _ = ρ (g:Sym) v-v := hw'
    rw [map_sub,projector_equivariant] at hproj'
    rw [map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mpr hproj'.symm
  refine ⟨p,fun v => ⟨i v,hpi v⟩,?_,?_⟩
  · intro g v
    apply hi
    rw [hip,he,hip,projector_equivariant]
  · ext v
    change p v = 0 ↔ _
    constructor
    · intro hv
      have hz : projector ρ v = 0 := by rw [←hip,hv,map_zero]
      simpa only [hz,sub_zero] using hpfix v
    · intro hv
      apply hi
      rw [hip,map_zero]
      simp only [projector,LinearMap.sum_apply]
      calc
        _ = ∑ _g ∈ cubes,v := Finset.sum_congr rfl (fun g hg => hv ⟨g,cubes_even g hg⟩)
        _ = 0 := by
          rw [Finset.sum_const,cubes_card,←Nat.cast_smul_eq_nsmul (R := ZMod 2)]
          change (20 : ZMod 2) • v = 0
          rw [show (20 : ZMod 2) = 0 from rfl,zero_smul]
end BinaryPermutation.FiveCentralExtension
