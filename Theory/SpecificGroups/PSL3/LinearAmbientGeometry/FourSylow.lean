module
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.InvolutiveAction
public import Theory.SpecificGroups.PSL3Four.SylowModel
public import Theory.FieldTheory.FiniteAutomorphismOrder

/-!
# A faithful marked lift of the exceptional Sylow group

A degree-two field has exactly one nonidentity field automorphism. An actual
split extension of UT₃(F) by that involution therefore admits a faithful map
from the native UT₃(F₄)⋊C₂ model, onto the specified subgroup. The same map
carries the whole unipotent group, both root planes, the highest root and
the central involution. The ambient group is arbitrary and no recognition
or centralizer bound is assumed.

The lift uses the standard semidirect-product universal property. Its kernel
is trivial because the chosen outer involution is outside S; its range is the
specified set product S⟨t⟩. Named generator equations avoid unfolding the
concrete finite-field construction in the cyclic action.
Source: Aschbacher--Smith §5.3.7, printed pp.660--661 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Matrix.PSL3.LinearAmbientGeometry
open Matrix.PSL3Even.UnipotentGeometry
namespace FourSylow
open Matrix.PSL3Four
variable {F : Type*} [Field F] [Finite F]

private def fieldCoordinates (θ : Matrix.PSL3Four.F ≃+* F) : SylowModel.U ≃* U F where
  toFun u := ⟨θ u.x,θ u.y,θ u.c⟩
  invFun u := ⟨θ.symm u.x,θ.symm u.y,θ.symm u.c⟩
  left_inv u := by apply SylowModel.U.ext <;> exact θ.symm_apply_apply _
  right_inv u := by apply U.ext <;> exact θ.apply_symm_apply _
  map_mul' u v := by apply U.ext <;> dsimp <;> simp only [map_add,map_mul]

private theorem field_frobenius (hF : Nat.card F=4) (σ : F ≃+* F) (hσ : σ≠1)
    (θ : Matrix.PSL3Four.F ≃+* F) (x : Matrix.PSL3Four.F) :
    σ (θ x)=θ (fieldFrobenius x) := by
  let a := (θ.symm.trans fieldFrobenius).trans θ
  have ha : a≠1 := by
    intro hh
    obtain ⟨y,hy⟩ := exists_fieldFrobenius_ne
    apply hy
    apply θ.injective
    have hy' := DFunLike.congr_fun hh (θ y)
    simpa [a] using hy'
  have hc : Nat.card (F ≃+* F)=2 :=
    FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hF
  have he : σ=a := ((Nat.card_eq_two_iff' (1 : F ≃+* F)).mp hc).unique hσ ha
  simpa [a] using DFunLike.congr_fun he (θ x)

variable {G : Type*} [Group G]

/-- An actual split extension with the specified field involution is the
exceptional Sylow model, with the complete unipotent embedding retained. -/
theorem exists_lift
    (S T : Subgroup G) (hST : S≤T) (e : U F ≃* S)
    (hF : Nat.card F=4) (σ : F ≃+* F) (hσ : σ≠1)
    (t : G) (ht : t∈T) (ht2 : t^2=1) (htS : t∉S)
    (hsplit : (T : Set G)=(S : Set G)*(zpowers t : Set G))
    (hact : ∀ u : U F, t*markedHom F S e u*t⁻¹=
      markedHom F S e ⟨σ u.x,σ u.y,σ u.c⟩) :
    ∃ (θ : Matrix.PSL3Four.F ≃+* F) (f : SylowModel.T →* G),
      Function.Injective f ∧ f.range=T ∧
      (∀ u : SylowModel.U, f (SylowModel.inclusion u)=
        markedHom F S e ⟨θ u.x,θ u.y,θ u.c⟩) ∧
      f (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)))=t := by
  let := Fintype.ofFinite F
  let := Fintype.ofFinite Matrix.PSL3Four.F
  let θ : Matrix.PSL3Four.F ≃+* F := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card] using card_F.trans hF.symm)
  let j : SylowModel.U →* G := (markedHom F S e).comp (fieldCoordinates θ).toMonoidHom
  have hj : Function.Injective j := (markedHom_injective F S e).comp (fieldCoordinates θ).injective
  have hjr : j.range=S := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr (fieldCoordinates θ).surjective,
      ←MonoidHom.range_eq_map,range_markedHom]
  let k := involutionHom t ht2
  have hkτ : k SylowModel.τ=t := involutionHom_generator t ht2
  have hc : ∀ a : C2, j.comp (SylowModel.action a).toMonoidHom =
      (MulAut.conj (k a)).toMonoidHom.comp j := by
    intro a
    rcases SylowModel.c2_cases a with rfl | rfl
    · ext u
      change j ((SylowModel.action 1) u) = k 1*j u*(k 1)⁻¹
      rw [map_one,map_one]
      simp
    · ext u
      change j ((SylowModel.action SylowModel.τ) u)=k SylowModel.τ*j u*(k SylowModel.τ)⁻¹
      rw [SylowModel.action_τ,hkτ]
      rw [show j u=markedHom F S e ((fieldCoordinates θ) u) from rfl,hact]
      apply congrArg (markedHom F S e)
      apply U.ext <;> exact (field_frobenius hF σ hσ θ _).symm
  let f : SylowModel.T →* G := SemidirectProduct.lift j k hc
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro u hu
    have he : j u.left*k u.right=1 := hu
    rcases u with ⟨u,a⟩
    rcases SylowModel.c2_cases a with rfl | rfl
    · have hj1 : j u=1 := by
        simpa only [map_one,mul_one] using he
      have hu1 : u=1 := hj (hj1.trans j.map_one.symm)
      exact mem_bot.mpr (SemidirectProduct.ext hu1 rfl)
    · have ht' : t=(j u)⁻¹ := by
        rw [hkτ] at he
        calc
          t = (j u)⁻¹*(j u*t) := by group
          _ = (j u)⁻¹ := by rw [he,mul_one]
      exact (htS (ht' ▸ S.inv_mem (hjr ▸ (show j u∈j.range from ⟨u,rfl⟩)))).elim
  have hfr : f.range=T := by
    apply le_antisymm
    · rintro x ⟨u,rfl⟩
      apply T.mul_mem (hST (hjr ▸ (show j u.left∈j.range from ⟨u.left,rfl⟩)))
      rcases SylowModel.c2_cases u.right with hh | hh
      · rw [hh,map_one]
        exact T.one_mem
      · rw [hh,hkτ]
        exact ht
    · intro x hx
      change x ∈ (T : Set G) at hx
      rw [hsplit] at hx
      obtain ⟨s,hs,v,hv,rfl⟩ := hx
      apply f.range.mul_mem
      · obtain ⟨u,rfl⟩ := hjr.symm ▸ hs
        exact ⟨SemidirectProduct.inl u,SemidirectProduct.lift_inl j k hc u⟩
      · apply (zpowers_le.mpr ?_ : zpowers t ≤ f.range) hv
        exact ⟨SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)),by
          rw [SemidirectProduct.lift_inr,involutionHom_generator]⟩
  refine ⟨θ,f,hfi,hfr,?_,?_⟩
  · intro u
    exact SemidirectProduct.lift_inl j k hc u
  · rw [SemidirectProduct.lift_inr,involutionHom_generator]

/-- The split identification carries all three marked root subgroups through
one map; in particular both planes retain their original ordering. -/
theorem exists_marked_lift
    (S T : Subgroup G) (hST : S≤T) (e : U F ≃* S)
    (hF : Nat.card F=4) (σ : F ≃+* F) (hσ : σ≠1)
    (t : G) (ht : t∈T) (ht2 : t^2=1) (htS : t∉S)
    (hsplit : (T : Set G)=(S : Set G)*(zpowers t : Set G))
    (hact : ∀ u : U F, t*markedHom F S e u*t⁻¹=
      markedHom F S e ⟨σ u.x,σ u.y,σ u.c⟩) :
    ∃ f : SylowModel.T →* G, Function.Injective f ∧ f.range=T ∧
      SylowModel.S.map f=S ∧
      SylowModel.V₁.map f=(V₁ F).map (markedHom F S e) ∧
      SylowModel.V₂.map f=(V₂ F).map (markedHom F S e) ∧
      SylowModel.Z.map f=(Z F).map (markedHom F S e) ∧
      f SylowModel.z=markedHom F S e ⟨0,0,1⟩ := by
  obtain ⟨θ,f,hfi,hfr,hf,htf⟩ := exists_lift S T hST e hF σ hσ t ht ht2 htS hsplit hact
  let j := markedHom F S e
  have hS : SylowModel.S.map f=S := by
    apply le_antisymm
    · rintro x ⟨u,⟨v,rfl⟩,rfl⟩
      rw [hf]
      exact (e _).property
    · intro x hx
      obtain ⟨u,hu⟩ := (range_markedHom F S e).symm ▸ hx
      refine ⟨SylowModel.inclusion ⟨θ.symm u.x,θ.symm u.y,θ.symm u.c⟩,⟨_,rfl⟩,?_⟩
      rw [hf]
      simpa only [θ.apply_symm_apply] using hu
  have hV₁ : SylowModel.V₁.map f=(V₁ F).map j := by
    apply le_antisymm
    · rintro x ⟨u,⟨v,rfl⟩,rfl⟩
      rw [MonoidHom.comp_apply,hf]
      exact mem_map_of_mem j (by simp [SylowModel.axis₁])
    · rintro x ⟨u,hu,rfl⟩
      have hy : u.y=0 := (mem_V₁ F u).mp hu
      refine ⟨SylowModel.inclusion ⟨θ.symm u.x,0,θ.symm u.c⟩,?_,?_⟩
      · exact ⟨Multiplicative.ofAdd (θ.symm u.x,θ.symm u.c),rfl⟩
      · rw [hf]
        apply congrArg j
        apply U.ext <;> simp [hy]
  have hV₂ : SylowModel.V₂.map f=(V₂ F).map j := by
    apply le_antisymm
    · rintro x ⟨u,⟨v,rfl⟩,rfl⟩
      rw [MonoidHom.comp_apply,hf]
      exact mem_map_of_mem j (by simp [SylowModel.axis₂])
    · rintro x ⟨u,hu,rfl⟩
      have hx : u.x=0 := (mem_V₂ F u).mp hu
      refine ⟨SylowModel.inclusion ⟨0,θ.symm u.y,θ.symm u.c⟩,?_,?_⟩
      · exact ⟨Multiplicative.ofAdd (θ.symm u.y,θ.symm u.c),rfl⟩
      · rw [hf]
        apply congrArg j
        apply U.ext <;> simp [hx]
  have hZ : SylowModel.Z.map f=(Z F).map j := by
    rw [←SylowModel.V₁_inf_V₂,←root_planes_inter,
      Subgroup.map_inf _ _ _ hfi,hV₁,hV₂,
      Subgroup.map_inf _ _ _ (markedHom_injective F S e)]
  refine ⟨f,hfi,hfr,hS,hV₁,hV₂,hZ,?_⟩
  change f (SylowModel.inclusion ⟨0,0,1⟩)=_
  rw [hf]
  simp only [map_zero,map_one]

end FourSylow
end Matrix.PSL3.LinearAmbientGeometry
