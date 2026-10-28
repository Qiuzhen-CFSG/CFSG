module
public import Theory.Representation.BinaryPermutation.FiveCentralExtension
public import Theory.Representation.BinaryOffender.FixedQuotientEquality
import Mathlib.Tactic

/-!
# A paired natural five-letter quotient splits

The two class sums of twenty three-cycles act as the two coordinate
projections on the natural pair and vanish on its fixed kernel. Their sum
gives a section of the literal quotient map, equivariant for the whole
product. In particular every fixed codimension is preserved.

Source: Aschbacher–Smith C.1.24 and E.2.3(3), pp.130–131 and216–217.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation.FivePair
open FiveCentralExtension
abbrev Core := BinaryPermutation.core (Fin 5)
abbrev action : Representation (ZMod 2) (Sym × Sym) (Core × Core) :=
  Representation.prod ((coreRepresentation (Fin 5)).comp (MonoidHom.fst Sym Sym))
    ((coreRepresentation (Fin 5)).comp (MonoidHom.snd Sym Sym))

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

def projector (ρ : Representation (ZMod 2) (Sym × Sym) V) : V →ₗ[ZMod 2] V :=
  FiveCentralExtension.projector (ρ.comp (MonoidHom.inl Sym Sym)) +
    FiveCentralExtension.projector (ρ.comp (MonoidHom.inr Sym Sym))

private theorem twenty_smul (v : V) : 20 • v = 0 := by
  rw [←Nat.cast_smul_eq_nsmul (R := ZMod 2)]
  change (20 : ZMod 2) • v = 0
  rw [show (20 : ZMod 2) = 0 from rfl,zero_smul]

theorem action_apply (g : Sym × Sym) (v : Core × Core) :
    action g v = (coreRepresentation (Fin 5) g.1 v.1,coreRepresentation (Fin 5) g.2 v.2) := rfl

private theorem projector_left (v : Core × Core) :
    FiveCentralExtension.projector (action.comp (MonoidHom.inl Sym Sym)) v = (v.1,0) := by
  simp only [FiveCentralExtension.projector,LinearMap.sum_apply,MonoidHom.comp_apply,
    MonoidHom.inl_apply,action_apply,map_one,Module.End.one_apply]
  apply Prod.ext
  · simpa only [Prod.fst_sum] using core_sum v.1
  · simpa only [Prod.snd_sum,Finset.sum_const,cubes_card] using twenty_smul v.2

private theorem projector_right (v : Core × Core) :
    FiveCentralExtension.projector (action.comp (MonoidHom.inr Sym Sym)) v = (0,v.2) := by
  simp only [FiveCentralExtension.projector,LinearMap.sum_apply,MonoidHom.comp_apply,
    MonoidHom.inr_apply,action_apply,map_one,Module.End.one_apply]
  apply Prod.ext
  · simpa only [Prod.fst_sum,Finset.sum_const,cubes_card] using twenty_smul v.1
  · simpa only [Prod.snd_sum] using core_sum v.2

theorem projector_action (v : Core × Core) : projector action v = v := by
  rw [projector,LinearMap.add_apply,projector_left,projector_right]
  ext <;> simp

private theorem projection_commutes
    (ρ : Representation (ZMod 2) (Sym × Sym) V)
    (i : Sym →* Sym × Sym) (g : Sym × Sym)
    (hcomm : ∀ a : Sym, i a * g = g * i a) (v : V) :
    FiveCentralExtension.projector (ρ.comp i) (ρ g v) =
      ρ g (FiveCentralExtension.projector (ρ.comp i) v) := by
  simp only [FiveCentralExtension.projector,LinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro a _
  change ρ (i a) (ρ g v) = ρ g (ρ (i a) v)
  simp only [←Module.End.mul_apply,←map_mul,hcomm]

theorem projector_equivariant (ρ : Representation (ZMod 2) (Sym × Sym) V)
    (g : Sym × Sym) (v : V) : projector ρ (ρ g v) = ρ g (projector ρ v) := by
  have hl (v : V) : FiveCentralExtension.projector (ρ.comp (MonoidHom.inl Sym Sym)) (ρ g v) =
      ρ g (FiveCentralExtension.projector (ρ.comp (MonoidHom.inl Sym Sym)) v) := by
    have hg : g = (g.1,1) * (1,g.2) := by ext <;> simp
    conv_lhs => rw [hg,map_mul,Module.End.mul_apply]
    rw [show ρ (g.1,1) = (ρ.comp (MonoidHom.inl Sym Sym)) g.1 from rfl,
      FiveCentralExtension.projector_equivariant]
    rw [projection_commutes ρ (MonoidHom.inl Sym Sym) (1,g.2) (by intro; ext <;> simp)]
    simp only [MonoidHom.comp_apply,MonoidHom.inl_apply]
    rw [←Module.End.mul_apply,←map_mul,←hg]
  have hr (v : V) : FiveCentralExtension.projector (ρ.comp (MonoidHom.inr Sym Sym)) (ρ g v) =
      ρ g (FiveCentralExtension.projector (ρ.comp (MonoidHom.inr Sym Sym)) v) := by
    have hg : g = (1,g.2) * (g.1,1) := by ext <;> simp
    conv_lhs => rw [hg,map_mul,Module.End.mul_apply]
    rw [show ρ (1,g.2) = (ρ.comp (MonoidHom.inr Sym Sym)) g.2 from rfl,
      FiveCentralExtension.projector_equivariant]
    rw [projection_commutes ρ (MonoidHom.inr Sym Sym) (g.1,1) (by intro; ext <;> simp)]
    simp only [MonoidHom.comp_apply,MonoidHom.inr_apply]
    rw [←Module.End.mul_apply,←map_mul,←hg]
  change _ + _ = ρ g (_ + _)
  rw [map_add,hl,hr]

variable (ρ : Representation (ZMod 2) (Sym × Sym) V)
  (p : V →ₗ[ZMod 2] (Core × Core)) (hp : Function.Surjective p)
  (he : ∀ g v, p (ρ g v) = action g (p v))
  (hk : ∀ v, p v = 0 → ∀ g : Sym × Sym, ρ g v = v)

include he in
theorem quotient_projector (v : V) : p (projector ρ v) = p v := by
  calc
    p (projector ρ v) = projector action (p v) := by
      simp only [projector,LinearMap.add_apply,FiveCentralExtension.projector,
        LinearMap.sum_apply,map_add,map_sum,MonoidHom.comp_apply,he]
    _ = p v := projector_action _

include hk in
private theorem projector_kernel {v : V} (hv : p v = 0) : projector ρ v = 0 := by
  change FiveCentralExtension.projector (ρ.comp (MonoidHom.inl Sym Sym)) v +
    FiveCentralExtension.projector (ρ.comp (MonoidHom.inr Sym Sym)) v = 0
  simp only [FiveCentralExtension.projector,LinearMap.sum_apply,MonoidHom.comp_apply,hk v hv,
    Finset.sum_const,cubes_card,twenty_smul,add_zero]

include hp he hk in
theorem exists_section : ∃ s : (Core × Core) →ₗ[ZMod 2] V,
    (∀ v, p (s v) = v) ∧ (∀ g v, s (action g v) = ρ g (s v)) := by
  have hker : p.ker ≤ (projector ρ).ker := fun v hv => projector_kernel ρ p hk hv
  let s := (p.ker.liftQ (projector ρ) hker).comp (p.quotKerEquivOfSurjective hp).symm.toLinearMap
  have hs (v : V) : s (p v) = projector ρ v := by
    simp [s,LinearMap.quotKerEquivOfSurjective_symm_apply]
  refine ⟨s,?_,?_⟩
  · intro v
    obtain ⟨w,rfl⟩ := hp v
    rw [hs,quotient_projector ρ p he]
  · intro g v
    obtain ⟨w,rfl⟩ := hp v
    rw [←he,hs,hs]
    exact projector_equivariant ρ g w

include hp he hk in
/-- Every fixed vector in the literal paired quotient lifts to a fixed vector;
the original fixed kernel contributes no extra codimension. -/
theorem fixedSpace_eq_comap (A : Subgroup (Sym × Sym)) :
    fixedSpace ρ A = (fixedSpace action A).comap p := by
  obtain ⟨s,hs,hse⟩ := exists_section ρ p hp he hk
  apply le_antisymm
  · intro v hv a
    change action a (p v) = p v
    rw [←he]
    exact congrArg p (hv a)
  · intro v hv a
    have hkv : p (v - s (p v)) = 0 := by rw [map_sub,hs,sub_self]
    have hh := hk (v - s (p v)) hkv a
    rw [map_sub,←hse] at hh
    have ha : action a (p v) = p v := hv a
    rw [ha] at hh
    change ρ (a : Sym × Sym) v = v
    simpa only [sub_add_cancel] using congrArg (fun w => w + s (p v)) hh

include hp he hk in
theorem fixedCodim_eq [FiniteDimensional (ZMod 2) V] (A : Subgroup (Sym × Sym)) :
    fixedCodim ρ A = fixedCodim action A := by
  let f := (fixedSpace action A).mkQ.comp p
  have hf : Function.Surjective f := (fixedSpace action A).mkQ_surjective.comp hp
  have hker : f.ker = fixedSpace ρ A := by
    rw [fixedSpace_eq_comap ρ p hp he hk]
    ext v
    change (fixedSpace action A).mkQ (p v) = 0 ↔ p v ∈ fixedSpace action A
    exact Submodule.Quotient.mk_eq_zero _
  have hh := (f.quotKerEquivOfSurjective hf).finrank_eq
  rw [hker] at hh
  exact hh

end BinaryPermutation.FivePair
