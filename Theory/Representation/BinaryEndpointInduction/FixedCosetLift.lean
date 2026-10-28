module
public import Theory.Representation.BinaryEndpointInduction.ParabolicSeedMarking

/-!
# Literal fifteen coordinates for an endpoint-fixed seed

The same representatives and right-coset transitions used for the natural
seed give a fifteen-coordinate cover when the endpoint fixes a vector.
The exact inverse left actors and the original seed are retained.
-/
public noncomputable section
open Matrix Representation
open scoped MatrixGroups
namespace BinaryEndpointInduction
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

private def fixedCosetLift (τ : Representation (ZMod 2) SL(4,ZMod 2) W)
    (w : W) : (Fin 15 → ZMod 2) →ₗ[ZMod 2] W where
  toFun x := ∑ i : Fin 15, x i • τ (cosetRepresentative i)⁻¹ w
  map_add' x y := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum,RingHom.id_apply]

private theorem fixedCosetLift_single (τ : Representation (ZMod 2) SL(4,ZMod 2) W)
    (w : W) (i : Fin 15) (c : ZMod 2) :
    fixedCosetLift τ w (Pi.single i c) = c • τ (cosetRepresentative i)⁻¹ w := by
  change (∑ j : Fin 15, (Pi.single i c : Fin 15 → ZMod 2) j • τ (cosetRepresentative j)⁻¹ w) = _
  simp [Pi.single_apply]

variable (M : Fin 6 → Matrix (Fin 15) (Fin 15) (ZMod 2))
  (hM : ∀ a i j, M a i j = if transitionIndex a i=j then 1 else 0)
  (τ : Representation (ZMod 2) SL(4,ZMod 2) W) (w : W)
  (hfix : ∀ p : endpointParabolic, τ p.val w=w)

include hM hfix

private theorem fixedCosetLift_intertwine (a : Fin 6) (x : Fin 15 → ZMod 2) :
    fixedCosetLift τ w (x ᵥ* M a)=τ (cosetActor a)⁻¹ (fixedCosetLift τ w x) := by
  have hsingle (i : Fin 15) (c : ZMod 2) :
      Pi.single i c ᵥ* M a=Pi.single (transitionIndex a i) c := by
    ext j
    simp only [Matrix.single_vecMul]
    change c * M a i j=(Pi.single (transitionIndex a i) c : Fin 15 → ZMod 2) j
    rw [hM]
    by_cases hj : transitionIndex a i=j
    · simp [hj]
    · simp [hj,Ne.symm hj]
  have hone (i : Fin 15) (c : ZMod 2) :
      fixedCosetLift τ w (Pi.single i c ᵥ* M a)=
        τ (cosetActor a)⁻¹ (fixedCosetLift τ w (Pi.single i c)) := by
    rw [hsingle,fixedCosetLift_single τ w (transitionIndex a i) c,
      fixedCosetLift_single τ w i c,map_smul]
    apply congrArg (fun y : W => c • y)
    have hcorr := hfix (⟨(transitionCorrection a i)⁻¹,
      endpointParabolic.inv_mem (transitionCorrection_mem_endpoint a i)⟩ : endpointParabolic)
    change τ (transitionCorrection a i)⁻¹ w=w at hcorr
    calc
      τ (cosetRepresentative (transitionIndex a i))⁻¹ w =
          τ (cosetRepresentative (transitionIndex a i))⁻¹ (τ (transitionCorrection a i)⁻¹ w) :=
        congrArg (τ (cosetRepresentative (transitionIndex a i))⁻¹) hcorr.symm
      _ = τ (cosetActor a)⁻¹ (τ (cosetRepresentative i)⁻¹ w) := by
        rw [←Module.End.mul_apply,←τ.map_mul,←Module.End.mul_apply,←τ.map_mul]
        have he := congrArg (fun g : SL(4,ZMod 2) => g⁻¹) (coset_transition a i)
        simp only [_root_.mul_inv_rev] at he
        exact congrArg (fun g => τ g w) he.symm
  have hx : ∑ i : Fin 15, Pi.single i (x i)=x := Finset.univ_sum_single x
  conv_lhs => rw [←hx]
  change fixedCosetLift τ w ((M a).vecMulLinear (∑ i : Fin 15, Pi.single i (x i))) = _
  rw [map_sum,map_sum]
  simp_rw [Matrix.vecMulLinear_apply,hone]
  rw [←map_sum,←map_sum,hx]

/-- Every spanning endpoint-fixed seed has an onto cover in the literal
fifteen right-coset coordinates, with the original inverse-actor action. -/
theorem exists_fixed_coset_cover
    (hspan : Submodule.span (ZMod 2) (Set.range (fun g : SL(4,ZMod 2) => τ g w))=⊤) :
    ∃ F : (Fin 15 → ZMod 2) →ₗ[ZMod 2] W,
      Function.Surjective F ∧
      (∀ i : Fin 15, F (Pi.single i 1)=τ (cosetRepresentative i)⁻¹ w) ∧
      ∀ (a : Fin 6) (x : Fin 15 → ZMod 2),
        F (x ᵥ* M a)=τ (cosetActor a)⁻¹ (F x) := by
  let F := fixedCosetLift τ w
  let R := F.range
  let : Finite R := Finite.of_surjective F.rangeRestrict F.surjective_rangeRestrict
  have hstable (a : Fin 6) (v : W) (hv : v ∈ R) : τ (cosetActor a)⁻¹ v ∈ R := by
    obtain ⟨x,rfl⟩ := hv
    exact ⟨x ᵥ* M a,fixedCosetLift_intertwine M hM τ w hfix a x⟩
  have hiff (a : Fin 6) (v : W) : v ∈ R ↔ τ (cosetActor a)⁻¹ v ∈ R := by
    refine ⟨hstable a v,?_⟩
    let f : R → R := fun x => ⟨τ (cosetActor a)⁻¹ x,hstable a x x.property⟩
    have hfi : Function.Injective f := by
      intro x y he
      exact Subtype.ext ((τ.apply_bijective _).injective (congrArg Subtype.val he))
    intro hv
    obtain ⟨x,hx⟩ := Finite.surjective_of_injective hfi ⟨τ (cosetActor a)⁻¹ v,hv⟩
    have he : (x : W)=v := (τ.apply_bijective _).injective (congrArg Subtype.val hx)
    exact he ▸ x.property
  let H : Subgroup SL(4,ZMod 2) := {
    carrier := {g | ∀ v : W, v ∈ R ↔ τ g v ∈ R}
    one_mem' := by intro v; simp
    mul_mem' := by
      intro g h hg hh v
      simpa only [τ.map_mul,Module.End.mul_apply] using (hh v).trans (hg (τ h v))
    inv_mem' := by
      intro g hg v
      simpa only [τ.self_inv_apply] using (hg (τ g⁻¹ v)).symm }
  have hactors (a : Fin 6) : cosetActor a ∈ H := by
    have hi : (cosetActor a)⁻¹ ∈ H := hiff a
    simpa only [inv_inv] using H.inv_mem hi
  have htop : H=⊤ := by
    apply top_unique
    rw [←generator_closure]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact cosetActor_generators.1 ▸ hactors 0
    · have he : g=cycleGenerator := Set.mem_singleton_iff.mp hg
      subst g
      exact cosetActor_generators.2 ▸ hactors 1
  refine ⟨F,?_,?_,fixedCosetLift_intertwine M hM τ w hfix⟩
  · apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [←hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨g,rfl⟩
    have hg : g ∈ H := htop ▸ Subgroup.mem_top g
    apply (hg w).mp
    refine ⟨Pi.single 0 1,?_⟩
    rw [fixedCosetLift_single,cosetRepresentative_zero,inv_one,map_one]
    simp
  · intro i
    rw [fixedCosetLift_single,one_smul]

end BinaryEndpointInduction
