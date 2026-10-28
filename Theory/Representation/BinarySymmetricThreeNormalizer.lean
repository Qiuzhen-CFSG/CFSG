module
public import Theory.GroupTheory.NormalSymmetricThree
public import Theory.Representation.InvertedCubicTensor
public import Theory.Representation.ResidualMovedGeneration
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.Plane

/-!
# Normalizers of a fully moved binary four-space for S₃

The inverter-fixed multiplicity space has dimension two. Any actor commuting
with S₃ acts faithfully there, and hence embeds in the permutations of its
three nonzero vectors. A normal S₃ splits off that centralizer. Consequently
the original linear normalizer has order dividing 36, and an overgroup with
four dividing its order is S₃ × C₂ or S₃ × S₃.

Full commutator generation removes the cubic fixed space via the actual
two-residual, so the linear-normalizer consumers assume no extra fixed-space
hypothesis. All action images remain the original representation images.

Source: Aschbacher--Smith, 15.1.2, proper seed-span case, printed p.1085.
-/

public noncomputable section
open Subgroup
namespace InvertedCubicTensor
variable {G V : Type*} [Group G] [AddCommGroup V] [Module F V]
  (σ : Representation F S₃ V) (κ : Representation F G V)
  (hc : ∀ g h v, κ g (σ h v) = σ h (κ g v))

theorem multiplicity_injective (h : ∀ v, σ cubic v = v → v = 0)
    (hf : Function.Injective κ) : Function.Injective (multiplicity σ κ hc) := by
  intro a b he
  apply hf
  ext v
  obtain ⟨w,rfl⟩ := (pairEquiv σ h).surjective v
  rw [←pairEquiv_equivariant σ κ hc h, ←pairEquiv_equivariant σ κ hc h]
  rw [he]

theorem multiplicity_finrank [FiniteDimensional F V]
    (h : ∀ v, σ cubic v = v → v = 0) :
    2 * Module.finrank F (multiplicitySpace σ) = Module.finrank F V := by
  have hh := (pairEquiv σ h).finrank_eq
  rw [Module.finrank_prod] at hh
  omega

end InvertedCubicTensor

namespace Representation.BinarySymmetricThreeNormalizer
open InvertedCubicTensor Theory.GroupTheory.NormalSymmetricThree
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

omit [Finite G] in
theorem exists_centralizer_embedding (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (h4 : Module.finrank (ZMod 2) V = 4)
    (H : Subgroup G) (j : H ≃* S₃)
    (hfree : ∀ v, ρ (j.symm cubic : G) v = v → v = 0) :
    ∃ f : centralizer (H : Set G) →* S₃, Function.Injective f := by
  let σ := ρ.comp (H.subtype.comp j.symm.toMonoidHom)
  let κ := ρ.comp (centralizer (H : Set G)).subtype
  have hc (g : centralizer (H : Set G)) (h : S₃) (v : V) :
      κ g (σ h v) = σ h (κ g v) := by
    change ρ (g:G) (ρ (j.symm h : G) v) = ρ (j.symm h : G) (ρ (g:G) v)
    rw [← Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
    exact congrArg (fun a => ρ a v) ((g.property _ (j.symm h).property).symm)
  have hk : Function.Injective κ := hf.comp (centralizer (H : Set G)).subtype_injective
  have hn : Module.finrank (ZMod 2) (multiplicitySpace σ) = 2 := by
    have hh := multiplicity_finrank σ hfree
    change 2 * Module.finrank (ZMod 2) (multiplicitySpace σ) = Module.finrank (ZMod 2) V at hh
    omega
  let b : multiplicitySpace σ ≃ₗ[ZMod 2] BinaryFourPlus.Plane :=
    (Module.finBasisOfFinrankEq (ZMod 2) _ hn).equivFun
  let μ := multiplicity σ κ hc
  let a := LinearMap.GeneralLinearGroup.congrLinearEquiv b
  let l := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) BinaryFourPlus.Plane
  let f : centralizer (H : Set G) →* S₃ := BinaryFourPlus.planeAutEquiv.toMonoidHom.comp
    (l.toMonoidHom.comp (a.toMonoidHom.comp μ.asGroupHom))
  refine ⟨f,BinaryFourPlus.planeAutEquiv.injective.comp (l.injective.comp
    (a.injective.comp ?_))⟩
  intro x y he
  apply multiplicity_injective σ κ hc hfree hk
  exact congrArg Units.val he

omit [Finite G] in
theorem centralizer_card_dvd_six (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (h4 : Module.finrank (ZMod 2) V = 4)
    (H : Subgroup G) (j : H ≃* S₃)
    (hfree : ∀ v, ρ (j.symm cubic : G) v = v → v = 0) :
    Nat.card (centralizer (H : Set G)) ∣ 6 := by
  obtain ⟨f,hf⟩ := exists_centralizer_embedding ρ hf h4 H j hfree
  have hd := Subgroup.card_dvd_of_injective f hf
  simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin,Nat.factorial] using hd

omit [Finite G] in
theorem exists_pair_embedding (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (h4 : Module.finrank (ZMod 2) V = 4)
    (H : Subgroup G) [H.Normal] (j : H ≃* S₃)
    (hfree : ∀ v, ρ (j.symm cubic : G) v = v → v = 0) :
    ∃ f : G →* S₃ × S₃, Function.Injective f ∧ ∀ h : H, f h = (j h,1) := by
  obtain ⟨e,he⟩ := exists_product_equiv H j
  obtain ⟨c,hc⟩ := exists_centralizer_embedding ρ hf h4 H j hfree
  let f : G →* S₃ × S₃ := (j.toMonoidHom.prodMap c).comp e.symm.toMonoidHom
  refine ⟨f,?_,?_⟩
  · intro a b hab
    apply e.symm.injective
    exact Prod.ext (j.injective (congrArg Prod.fst hab))
      (hc (congrArg Prod.snd hab))
  · intro h
    have hh : e (h,1) = (h:G) := by simpa only [coe_one,mul_one] using he h 1
    rw [←hh]
    change (j.toMonoidHom.prodMap c) (e.symm (e (h,1))) = (j h,1)
    rw [e.symm_apply_apply]
    simp

omit [Finite G] in
theorem card_dvd_thirty_six (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (h4 : Module.finrank (ZMod 2) V = 4)
    (H : Subgroup G) [H.Normal] (j : H ≃* S₃)
    (hfree : ∀ v, ρ (j.symm cubic : G) v = v → v = 0) : Nat.card G ∣ 36 := by
  obtain ⟨e,_⟩ := exists_product_equiv H j
  have hH : Nat.card H = 6 := by
    rw [Nat.card_congr j.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  rw [←Nat.card_congr e.toEquiv,Nat.card_prod,hH]
  exact Nat.mul_dvd_mul_left 6 (centralizer_card_dvd_six ρ hf h4 H j hfree)

omit [Finite G] in
theorem normal_symmetricThree_cases (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (h4 : Module.finrank (ZMod 2) V = 4)
    (H : Subgroup G) [H.Normal] (j : H ≃* S₃)
    (hfree : ∀ v, ρ (j.symm cubic : G) v = v → v = 0)
    (hfour : 4 ∣ Nat.card G) :
    Nonempty (G ≃* (S₃ × Multiplicative (ZMod 2))) ∨ Nonempty (G ≃* (S₃ × S₃)) := by
  obtain ⟨e,_⟩ := exists_product_equiv H j
  let C := centralizer (H : Set G)
  have hH : Nat.card H = 6 := by
    rw [Nat.card_congr j.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have he : Nat.card G = 6 * Nat.card C := by
    rw [←Nat.card_congr e.toEquiv,Nat.card_prod,hH]
  have hd : Nat.card C ∣ 6 := centralizer_card_dvd_six ρ hf h4 H j hfree
  have hle : Nat.card C ≤ 6 := Nat.le_of_dvd (by decide) hd
  have hc : Nat.card C = 2 ∨ Nat.card C = 6 := by
    rw [he] at hfour
    interval_cases hn : Nat.card C <;> norm_num [hn] at *
  rcases hc with hc | hc
  · left
    let c : C ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hc (by
      rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)]
      exact Nat.card_zmod 2)
    exact ⟨e.symm.trans (j.prodCongr c)⟩
  · right
    obtain ⟨f,hf⟩ := exists_centralizer_embedding ρ hf h4 H j hfree
    have hb : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr ⟨hf,by
      rw [hc,Nat.card_eq_fintype_card,Fintype.card_perm]
      decide⟩
    exact ⟨e.symm.trans (j.prodCongr (MulEquiv.ofBijective f hb))⟩

end Representation.BinarySymmetricThreeNormalizer



namespace Representation.BinarySymmetricThreeNormalizer
open InvertedCubicTensor BinaryOffender
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem fixedFree_of_full (σ : Representation (ZMod 2) S₃ V)
    (hm : subspaceCommutator σ ⊤ ⊤ = ⊤) :
    ∀ v, σ cubic v = v → v = 0 := by
  apply fixedFree_of_commutator_eq_top σ
  have hr : pResidual 2 S₃ ≤ alternatingGroup (Fin 3) := by
    apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    change (alternatingGroup (Fin 3)).index = 2 ^ 1
    simp
  have hp := commutator_pResidual_eq_top σ ⊤ hm
  have he : (pResidual 2 (⊤ : Subgroup S₃)).map (⊤ : Subgroup S₃).subtype = pResidual 2 S₃ := by
    have ht : (topEquiv : (⊤ : Subgroup S₃) ≃* S₃).toMonoidHom = (⊤ : Subgroup S₃).subtype := by
      ext x
      rfl
    rw [← ht]
    exact Subgroup.map_pResidual 2 topEquiv
  rw [he] at hp
  apply top_unique
  apply hp.ge.trans
  apply Submodule.span_mono
  rintro _ ⟨g,hg,v,hv,rfl⟩
  exact ⟨g,hr hg,v,hv,rfl⟩

theorem linear_normalizer_card_dvd_thirty_six (σ : Representation (ZMod 2) S₃ V)
    (hf : Function.Injective σ) (h4 : Module.finrank (ZMod 2) V = 4)
    (hm : subspaceCommutator σ ⊤ ⊤ = ⊤) :
    Nat.card (normalizer (σ.asGroupHom.range : Set (Module.End (ZMod 2) V)ˣ)) ∣ 36 := by
  let L := (Module.End (ZMod 2) V)ˣ
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let : Finite L := Finite.of_injective Units.val Units.val_injective
  let N := normalizer (σ.asGroupHom.range : Set L)
  let : Finite N := inferInstance
  let H := σ.asGroupHom.range.subgroupOf N
  let ρ : Representation (ZMod 2) N V := (Units.coeHom _).comp N.subtype
  have hfi : Function.Injective σ.asGroupHom := by
    intro a b he
    exact hf (congrArg Units.val he)
  let j : H ≃* S₃ := (subgroupOfEquivOfLe σ.asGroupHom.range.le_normalizer).trans
    (MonoidHom.ofInjective hfi).symm
  have hρ : Function.Injective ρ := by
    intro a b he
    apply Subtype.ext
    exact Units.ext he
  exact card_dvd_thirty_six ρ hρ h4 H j (fixedFree_of_full σ hm)

end Representation.BinarySymmetricThreeNormalizer


namespace Representation.BinarySymmetricThreeNormalizer
open InvertedCubicTensor BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem linear_normalizer_card_dvd_of_equiv (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (h4 : Module.finrank (ZMod 2) V = 4)
    (e : G ≃* S₃) (hm : subspaceCommutator ρ ⊤ ⊤ = ⊤) :
    Nat.card (normalizer (ρ.asGroupHom.range : Set (Module.End (ZMod 2) V)ˣ)) ∣ 36 := by
  let σ : Representation (ZMod 2) S₃ V := ρ.comp e.symm.toMonoidHom
  have hσ : Function.Injective σ := hf.comp e.symm.injective
  have hfull : subspaceCommutator σ ⊤ ⊤ = ⊤ := by
    rw [subspaceCommutator_comp_map,Subgroup.map_top_of_surjective _ e.symm.surjective]
    exact hm
  have hr : σ.asGroupHom.range = ρ.asGroupHom.range := by
    ext x
    constructor
    · rintro ⟨g,rfl⟩
      refine ⟨e.symm g,?_⟩
      apply Units.ext
      rfl
    · rintro ⟨g,rfl⟩
      refine ⟨e g,?_⟩
      apply Units.ext
      change ρ (e.symm (e g)) = ρ g
      rw [e.symm_apply_apply]
  rw [←hr]
  exact linear_normalizer_card_dvd_thirty_six σ hσ h4 hfull

theorem linear_normalizer_overgroup_cases (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (h4 : Module.finrank (ZMod 2) V = 4)
    (e : G ≃* S₃) (hm : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (A : Subgroup (Module.End (ZMod 2) V)ˣ) (hRA : ρ.asGroupHom.range ≤ A)
    (hAN : A ≤ normalizer (ρ.asGroupHom.range : Set (Module.End (ZMod 2) V)ˣ))
    (hfour : 4 ∣ Nat.card A) :
    Nonempty (A ≃* (S₃ × Multiplicative (ZMod 2))) ∨ Nonempty (A ≃* (S₃ × S₃)) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let : Finite ((Module.End (ZMod 2) V)ˣ) := Finite.of_injective Units.val Units.val_injective
  let H := ρ.asGroupHom.range.subgroupOf A
  let : H.Normal := (normal_subgroupOf_iff_le_normalizer hRA).mpr hAN
  let τ : Representation (ZMod 2) A V := (Units.coeHom _).comp A.subtype
  have hi : Function.Injective ρ.asGroupHom := fun a b he => hf (congrArg Units.val he)
  let j : H ≃* S₃ := ((subgroupOfEquivOfLe hRA).trans (MonoidHom.ofInjective hi).symm).trans e
  have hτ : Function.Injective τ := by
    intro a b he
    exact Subtype.ext (Units.ext he)
  let σ : Representation (ZMod 2) S₃ V := ρ.comp e.symm.toMonoidHom
  have hfull : subspaceCommutator σ ⊤ ⊤ = ⊤ := by
    rw [subspaceCommutator_comp_map,Subgroup.map_top_of_surjective _ e.symm.surjective]
    exact hm
  apply normal_symmetricThree_cases τ hτ h4 H j _ hfour
  exact fixedFree_of_full σ hfull

end Representation.BinarySymmetricThreeNormalizer
