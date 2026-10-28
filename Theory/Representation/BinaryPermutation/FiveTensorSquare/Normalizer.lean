module
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Centralizer
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Automorphisms
public import Theory.Representation.BinaryPermutation.Faithful
/-!
# The full normalizer of the deleted A₅ tensor square

Every product automorphism preserves or exchanges the two simple factors.
Aut(A₅)=S₅ realizes its factor markings by coordinate permutations. Correcting
a normalizing linear map by the corresponding wreath actor leaves the trivial
linear centralizer. Tensor contractions also prove faithfulness of the entire
wreath action. The final theorem transfers an actual faithful ambient action
with normal marked A₅² subgroup to this literal model.

Source: Aschbacher–Smith D.3.7, printed pp.197–199.
-/
@[expose] public noncomputable section
open scoped TensorProduct
open Representation Subgroup
namespace BinaryPermutation.FiveTensorSquare
private theorem core_faithful : Function.Injective (coreRepresentation (Fin 5)) := by
  intro g h hgh
  apply naturalRepresentation_injective (Fin 5) (by decide)
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := (coreEquivNatural (Fin 5) (by decide)).surjective v
  rw [←coreEquivNatural_equivariant,←coreEquivNatural_equivariant,hgh]

theorem tensorWreathHom_injective : Function.Injective tensorWreathHom := by
  apply (injective_iff_map_eq_one tensorWreathHom).mpr
  intro w hw
  have hh (u v : C) : tensorWreathMap w (u ⊗ₜ[ZMod 2] v) = u ⊗ₜ[ZMod 2] v :=
    congrArg (fun e : V ≃ₗ[ZMod 2] V => e (u ⊗ₜ[ZMod 2] v)) hw
  rcases index_cases w.right with hr | hr
  · have h := tensor_identity_factors (coreEquiv (w.left 1)) (coreEquiv (w.left swapIndex))
      (fun u v => by simpa only [tensorWreathMap_tmul,hr,ite_true,coreEquiv,LinearEquiv.ofBijective_apply] using hh u v)
    have hc (g : Sym) (hg : coreEquiv g = LinearEquiv.refl (ZMod 2) C) : g = 1 := by
      apply core_faithful
      apply LinearMap.ext
      intro v
      exact congrArg (fun e : C ≃ₗ[ZMod 2] C => e v) hg
    apply RegularWreathProduct.ext
    · funext i
      rcases index_cases i with rfl | rfl
      · exact hc _ h.1
      · exact hc _ h.2
    · exact hr
  · exact (tensor_exchange_ne_identity (coreEquiv (w.left 1))
      (coreEquiv (w.left swapIndex)) (fun u v => by
        simpa only [tensorWreathMap_tmul,hr,swapIndex_ne_one,ite_false,coreEquiv,LinearEquiv.ofBijective_apply] using hh u v)).elim

theorem tensorWreathAction_injective : Function.Injective tensorWreathAction := by
  intro a b hab
  apply tensorWreathHom_injective
  apply LinearEquiv.ext
  intro v
  exact LinearMap.congr_fun hab v

private theorem core_intertwines (s : Sym) (g : Alt) (u : C) :
    coreRepresentation (Fin 5) s (δ g u) =
      δ (MulAut.conjNormal s g) (coreRepresentation (Fin 5) s u) := by
  change coreRepresentation (Fin 5) s (coreRepresentation (Fin 5) g.val u) =
    coreRepresentation (Fin 5) (s*g.val*s⁻¹) (coreRepresentation (Fin 5) s u)
  simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]

/-- Every automorphism of the alternating product is realized by a concrete
wreath actor on the deleted tensor square. -/
theorem exists_wreath_intertwiner (φ : MulAut (Alt × Alt)) :
    ∃ w : Wreath, ∀ g v,
      tensorWreathHom w (deletedAction g v) =
        deletedAction (φ g) (tensorWreathHom w v) := by
  rcases product_automorphism_alternatives φ with ⟨α,β,hφ⟩ | ⟨α,β,hφ⟩
  · obtain ⟨s,hs⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
      5 (by decide) (by decide)).surjective α
    obtain ⟨t,ht⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
      5 (by decide) (by decide)).surjective β
    refine ⟨base (s,t), fun g v => ?_⟩
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul u v =>
      change tensorWreathAction (base (s,t)) (δ g.1 u ⊗ₜ[ZMod 2] δ g.2 v) = _
      rw [tensorWreathAction_base,hφ]
      change _ = deletedAction (α g.1,β g.2)
        (tensorWreathAction (base (s,t)) (u ⊗ₜ[ZMod 2] v))
      rw [tensorWreathAction_base]
      change _ = δ (α g.1) _ ⊗ₜ[ZMod 2] δ (β g.2) _
      rw [core_intertwines,core_intertwines,hs,ht]
    | add u v hu hv => simp only [map_add,hu,hv]
  · obtain ⟨s,hs⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
      5 (by decide) (by decide)).surjective α
    obtain ⟨t,ht⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
      5 (by decide) (by decide)).surjective β
    let w : Wreath := ⟨fun i => if i = 1 then s else t,swapIndex⟩
    have hw (u v : C) : tensorWreathHom w (u ⊗ₜ[ZMod 2] v) =
        coreRepresentation (Fin 5) s v ⊗ₜ[ZMod 2] coreRepresentation (Fin 5) t u := by
      change tensorWreathMap w _ = _
      simp [tensorWreathMap_tmul,w]
    refine ⟨w, fun g v => ?_⟩
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul u v =>
      change tensorWreathHom w (δ g.1 u ⊗ₜ[ZMod 2] δ g.2 v) = _
      rw [hw,hφ,hw]
      change _ = δ (α g.2) _ ⊗ₜ[ZMod 2] δ (β g.1) _
      rw [core_intertwines,core_intertwines,hs,ht]
    | add u v hu hv => simp only [map_add,hu,hv]

/-- Every normalizer of the marked alternating product is the literal wreath
actor, without a factor-preservation assumption. -/
theorem tensor_normalizer (f : V ≃ₗ[ZMod 2] V) (φ : MulAut (Alt × Alt))
    (hf : ∀ g v, f (deletedAction g v) = deletedAction (φ g) (f v)) :
    ∃ w : Wreath, tensorWreathHom w = f := by
  obtain ⟨w,hw⟩ := exists_wreath_intertwiner φ
  let t := tensorWreathHom w
  have hts (g : Alt × Alt) (v : V) :
      t.symm (deletedAction (φ g) v) = deletedAction g (t.symm v) := by
    apply t.injective
    rw [t.apply_symm_apply,hw,t.apply_symm_apply]
  have hF := deleted_centralizer (f.trans t.symm) (fun g v => by
    change t.symm (f (deletedAction g v)) = _
    rw [hf,hts]
    rfl)
  refine ⟨w,?_⟩
  apply LinearEquiv.ext
  intro v
  have he := congrArg (fun e : V ≃ₗ[ZMod 2] V => t (e v)) hF
  simpa only [LinearEquiv.trans_apply,t.apply_symm_apply,LinearEquiv.refl_apply] using he.symm

/-- The actual alternating-product image in the linear group. -/
def deletedHom : Alt × Alt →* (V ≃ₗ[ZMod 2] V) :=
  tensorWreathHom.comp alternatingBase

theorem deletedHom_apply (g : Alt × Alt) (v : V) :
    deletedHom g v = deletedAction g v :=
  LinearMap.congr_fun (DFunLike.congr_fun tensorWreathAction_comp_alternatingBase g) v

theorem alternatingBase_injective : Function.Injective alternatingBase := by
  intro a b hab
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg (fun w : Wreath => w.left 1) hab
  · have he := congrArg (fun w : Wreath => w.left swapIndex) hab
    simpa [alternatingBase,baseHom,base] using he

theorem deletedHom_injective : Function.Injective deletedHom :=
  tensorWreathHom_injective.comp alternatingBase_injective

/-- Full image-normalizer coverage, with no automorphism witness assumed. -/
theorem normalizer_image (f : V ≃ₗ[ZMod 2] V)
    (hf : f ∈ Subgroup.normalizer (deletedHom.range : Set (V ≃ₗ[ZMod 2] V))) :
    ∃ w : Wreath, tensorWreathHom w = f := by
  let e := MonoidHom.ofInjective deletedHom_injective
  let φ := e.trans ((deletedHom.range.normalizerMonoidHom ⟨f,hf⟩).trans e.symm)
  have hconj (g : Alt × Alt) : deletedHom (φ g) = f * deletedHom g * f⁻¹ := by
    change deletedHom (e.symm _) = _
    rw [MonoidHom.apply_ofInjective_symm]
    rfl
  apply tensor_normalizer f φ
  intro g v
  rw [← deletedHom_apply,← deletedHom_apply,hconj]
  change f (deletedHom g v) = f (deletedHom g (f.symm (f v)))
  rw [f.symm_apply_apply]

/-- Any group of actual linear normalizers embeds in the concrete wreath
actor; the original actions agree on every vector. -/
theorem lift_to_wreath {H : Type*} [Group H] (a : H →* (V ≃ₗ[ZMod 2] V))
    (ha : ∀ h, a h ∈ Subgroup.normalizer (deletedHom.range : Set (V ≃ₗ[ZMod 2] V))) :
    ∃ q : H →* Wreath, tensorWreathHom.comp q = a := by
  classical
  choose q hq using fun h => normalizer_image (a h) (ha h)
  let Q : H →* Wreath := {
    toFun := q
    map_one' := tensorWreathHom_injective (by rw [hq,map_one,map_one])
    map_mul' h k := tensorWreathHom_injective (by simp only [map_mul,hq]) }
  exact ⟨Q,MonoidHom.ext hq⟩

/-- Source transfer: a faithful full actor normalizing the marked A₅ product
embeds in the wreath group, with its entire action intertwined. -/
theorem faithful_actor_embedding {H U : Type*} [Group H]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (hρ : Function.Injective ρ)
    (i : Alt × Alt →* H) [i.range.Normal]
    (e : Representation.Equiv (ρ.comp i) deletedAction) :
    ∃ q : H →* Wreath, Function.Injective q ∧
      Nonempty (ρ.Equiv (tensorWreathAction.comp q)) := by
  have he_symm (v : U) : e.toLinearEquiv.symm (e v) = v := e.toLinearEquiv.symm_apply_apply v
  have he_apply (v : V) : e (e.toLinearEquiv.symm v) = v := e.toLinearEquiv.apply_symm_apply v
  let a : H →* (V ≃ₗ[ZMod 2] V) := {
    toFun h := e.toLinearEquiv.symm.trans
      ((LinearEquiv.ofBijective (ρ h) (ρ.apply_bijective h)).trans e.toLinearEquiv)
    map_one' := by
      apply LinearEquiv.ext
      intro v
      change e (ρ 1 (e.toLinearEquiv.symm v)) = v
      rw [map_one,Module.End.one_apply,he_apply]
    map_mul' h k := by
      apply LinearEquiv.ext
      intro v
      change e (ρ (h*k) (e.toLinearEquiv.symm v)) =
        e (ρ h (e.toLinearEquiv.symm (e (ρ k (e.toLinearEquiv.symm v)))))
      rw [he_symm,map_mul,Module.End.mul_apply] }
  have hai (g : Alt × Alt) : a (i g) = deletedHom g := by
    apply LinearEquiv.ext
    intro v
    change e (ρ (i g) (e.toLinearEquiv.symm v)) = _
    have he := Representation.IntertwiningMap.isIntertwining
      (ρ.comp i) deletedAction e.toIntertwiningMap g (e.toLinearEquiv.symm v)
    change e (ρ (i g) (e.toLinearEquiv.symm v)) = deletedAction g (e (e.toLinearEquiv.symm v)) at he
    rw [he_apply] at he
    exact he.trans (deletedHom_apply g v).symm
  have ha (h : H) : a h ∈ Subgroup.normalizer (deletedHom.range : Set (V ≃ₗ[ZMod 2] V)) := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    constructor
    · rintro ⟨g,rfl⟩
      obtain ⟨k,hk⟩ := (inferInstance : i.range.Normal).conj_mem (i g) ⟨g,rfl⟩ h
      refine ⟨k,?_⟩
      rw [←hai,hk,map_mul,map_mul,map_inv,hai]
    · intro hx
      obtain ⟨g,hg⟩ := hx
      obtain ⟨k,hk⟩ := (inferInstance : i.range.Normal).conj_mem (i g) ⟨g,rfl⟩ h⁻¹
      refine ⟨k,?_⟩
      rw [←hai,hk]
      simp only [map_mul,map_inv,inv_inv,hai,hg]
      group
  obtain ⟨q,hq⟩ := lift_to_wreath a ha
  have hiq : Function.Injective q := by
    intro h k hhk
    apply hρ
    apply LinearMap.ext
    intro v
    apply e.toLinearEquiv.injective
    have hh : a h = a k := by
      rw [←hq]
      exact congrArg tensorWreathHom hhk
    have hv := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (e v)) hh
    change e (ρ h (e.toLinearEquiv.symm (e v))) =
      e (ρ k (e.toLinearEquiv.symm (e v))) at hv
    change e (ρ h v) = e (ρ k v)
    simpa only [he_symm] using hv
  refine ⟨q,hiq,⟨Representation.Equiv.mk e.toLinearEquiv ?_⟩⟩
  intro h
  apply LinearMap.ext
  intro v
  have hh : tensorWreathHom (q h) = a h := DFunLike.congr_fun hq h
  change e (ρ h v) = tensorWreathHom (q h) (e v)
  rw [hh]
  change e (ρ h v) = e (ρ h (e.toLinearEquiv.symm (e v)))
  rw [he_symm]
end BinaryPermutation.FiveTensorSquare
