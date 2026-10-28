module

public import Theory.Representation.BinaryOffender.DualDisplacement
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.BinaryOffender.Embedding

/-!
# A two-dimensional offender cannot act faithfully on two summands

The moved dimensions add on a direct sum. If their sum is at most two,
faithfulness makes each moved space a line. Counting displacement maps then
bounds the actor rank by the first fixed codimension. The offender inequality
requires the sum of both positive fixed codimensions to fit in that same rank,
a contradiction. No classification or quadratic-action hypothesis is needed.

Source application: Aschbacher–Smith 13.7.15(1–2), printed pp.943–944,
where this excludes the reducible B.5.1 action rows.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)

theorem subspaceCommutator_top_eq_coinvariants (A : Subgroup G) :
    subspaceCommutator ρ ⊤ A = Coinvariants.ker (ρ.comp A.subtype) := by
  unfold subspaceCommutator Coinvariants.ker
  congr 1
  ext v
  constructor
  · rintro ⟨a,ha,w,_,rfl⟩
    exact ⟨(⟨a,ha⟩,w),rfl⟩
  · rintro ⟨⟨a,w⟩,rfl⟩
    exact ⟨a,a.property,w,Submodule.mem_top,rfl⟩

theorem fixedCodim_dual_eq_moved_finrank (A : Subgroup G) :
    fixedCodim ρ.dual A = Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) := by
  rw [subspaceCommutator_top_eq_coinvariants]
  exact finrank_dual_quotient_invariants (ρ.comp A.subtype)

theorem subspaceCommutator_prod (A : Subgroup G) :
    subspaceCommutator (ρ.prod σ) ⊤ A =
      (subspaceCommutator ρ ⊤ A).prod (subspaceCommutator σ ⊤ A) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,_,rfl⟩
    exact ⟨Submodule.subset_span ⟨a,ha,v.1,Submodule.mem_top,rfl⟩,
      Submodule.subset_span ⟨a,ha,v.2,Submodule.mem_top,rfl⟩⟩
  · intro v hv
    have left (x : V) (hx : x ∈ subspaceCommutator ρ ⊤ A) :
        (x,0) ∈ subspaceCommutator (ρ.prod σ) ⊤ A := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a,ha,w,_,rfl⟩ := hx
        have h : ρ.prod σ a (w,0) - (w,0) ∈ subspaceCommutator (ρ.prod σ) ⊤ A :=
          Submodule.subset_span ⟨a,ha,(w,0),Submodule.mem_top,rfl⟩
        change (ρ a w - w, σ a 0 - 0) ∈ subspaceCommutator (ρ.prod σ) ⊤ A at h
        simpa only [map_zero, sub_zero] using h
      | zero => exact Submodule.zero_mem _
      | add x y _ _ hx hy => simpa only [Prod.mk_add_mk, add_zero] using Submodule.add_mem _ hx hy
      | smul c x _ hx => simpa only [Prod.smul_mk, smul_zero] using Submodule.smul_mem _ c hx
    have right (y : W) (hy : y ∈ subspaceCommutator σ ⊤ A) :
        (0,y) ∈ subspaceCommutator (ρ.prod σ) ⊤ A := by
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a,ha,w,_,rfl⟩ := hy
        have h : ρ.prod σ a (0,w) - (0,w) ∈ subspaceCommutator (ρ.prod σ) ⊤ A :=
          Submodule.subset_span ⟨a,ha,(0,w),Submodule.mem_top,rfl⟩
        change (ρ a 0 - 0, σ a w - w) ∈ subspaceCommutator (ρ.prod σ) ⊤ A at h
        simpa only [map_zero, sub_zero] using h
      | zero => exact Submodule.zero_mem _
      | add x y _ _ hx hy => simpa only [Prod.mk_add_mk, add_zero] using Submodule.add_mem _ hx hy
      | smul c x _ hx => simpa only [Prod.smul_mk, smul_zero] using Submodule.smul_mem _ c hx
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using
      Submodule.add_mem (subspaceCommutator (ρ.prod σ) ⊤ A) (left v.1 hv.1) (right v.2 hv.2)

variable [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]

theorem moved_finrank_prod (A : Subgroup G) :
    Module.finrank (ZMod 2) (subspaceCommutator (ρ.prod σ) ⊤ A) =
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) +
      Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ A) := by
  rw [subspaceCommutator_prod]
  let e : (subspaceCommutator ρ ⊤ A).prod (subspaceCommutator σ ⊤ A) ≃ₗ[ZMod 2]
      (subspaceCommutator ρ ⊤ A) × (subspaceCommutator σ ⊤ A) :=
    { toFun := fun v => (⟨v.val.1,v.property.1⟩,⟨v.val.2,v.property.2⟩)
      invFun := fun v => ⟨(v.1.val,v.2.val),v.1.property,v.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  simpa only [Module.finrank_prod] using e.finrank_eq

/-- The genuine obstruction for the source's two noncentral faithful factors. -/
theorem not_offender_prod_of_moved_le_two [Finite G]
    (hf : Function.Injective ρ) (hg : Function.Injective σ)
    (A : Subgroup G) (hA : IsOffender (ρ.prod σ) A)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator (ρ.prod σ) ⊤ A) ≤ 2) : False := by
  have hp := fixedCodim_pos_of_faithful ρ hf hA.1.1
  have hq := fixedCodim_pos_of_faithful σ hg hA.1.1
  have hpd := fixedCodim_pos_of_faithful ρ.dual (faithful_dual ρ hf) hA.1.1
  have hqd := fixedCodim_pos_of_faithful σ.dual (faithful_dual σ hg) hA.1.1
  rw [moved_finrank_prod, ← fixedCodim_dual_eq_moved_finrank,
    ← fixedCodim_dual_eq_moved_finrank] at hd
  have hline : fixedCodim ρ.dual A = 1 := by omega
  have hb := rank_le_fixedCodim_mul_dual ρ hf A
  rw [hline,mul_one] at hb
  have hc := hA.2
  rw [fixedCodim_prod] at hc
  omega

omit [FiniteDimensional (ZMod 2) W] in
/-- Passing to an invariant embedded module cannot increase its moved dimension. -/
theorem moved_finrank_map_le_of_embedding
    {D : Type*} [Group D] (τ : Representation (ZMod 2) D W)
    (f : G →* D) (e : W →ₗ[ZMod 2] V) (he : Function.Injective e)
    (hact : ∀ g w, ρ g (e w) = e (τ (f g) w)) (A : Subgroup G) :
    Module.finrank (ZMod 2) (subspaceCommutator τ ⊤ (A.map f)) ≤
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) := by
  let T := subspaceCommutator τ ⊤ (A.map f)
  let S := subspaceCommutator ρ ⊤ A
  have hle : T.map e ≤ S := by
    rw [← subspaceCommutator_map_embedding ρ τ f e hact]
    apply Submodule.span_mono
    rintro v ⟨a,ha,w,_,hv⟩
    exact ⟨a,ha,w,Submodule.mem_top,hv⟩
  let j : T →ₗ[ZMod 2] S := (e.comp T.subtype).codRestrict S
    (fun v => hle ⟨v,v.property,rfl⟩)
  exact LinearMap.finrank_le_finrank_of_injective (f := j)
    (fun x y h => Subtype.ext (he (congrArg Subtype.val h)))

/-- The plane obstruction also applies to an actual invariant product summand. -/
theorem not_offender_faithful_product_embedding
    {D X Y : Type*} [Group D] [Finite D]
    [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y]
    (π : Representation (ZMod 2) D X) (τ : Representation (ZMod 2) D Y)
    (hfπ : Function.Injective π) (hfτ : Function.Injective τ)
    (f : G →* D) (hf : Function.Injective f)
    (e : X × Y →ₗ[ZMod 2] V) (he : Function.Injective e)
    (hact : ∀ g w, ρ g (e w) = e ((π.prod τ) (f g) w))
    {A : Subgroup G} (hA : IsOffender ρ A)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 2) : False := by
  have hoff := hA.map_of_embedding ρ (π.prod τ) f e he hact hf
  exact not_offender_prod_of_moved_le_two π τ hfπ hfτ (A.map f) hoff
    ((moved_finrank_map_le_of_embedding ρ (π.prod τ) f e he hact A).trans hd)
end Representation.BinaryOffender
