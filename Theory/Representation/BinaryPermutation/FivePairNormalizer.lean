module
public import Theory.Representation.BinaryPermutation.FiveCoreNormalizer
public import Theory.Representation.BinaryPermutation.FivePairExtension
import Mathlib.Tactic

/-!
# Normalizers of the paired five-letter action

The fixed space of either whole symmetric factor is the opposite natural
summand. A normalizer preserving the actor factors preserves these summands;
its two restrictions are the actual permutation actions by Aut(A₅)=S₅ and
the binary scalar-commutant calculation. A factor-exchanging normalizer
cannot fix a nonzero vector on either axis. Thus the genuine source
preserve-or-exchange dichotomy yields a product actor whenever one such
fixed vector exists.

Source: Aschbacher–Smith C.1.24 and E.2.3(3), pp.130–131 and216–217.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation.FivePair
open FiveCentralExtension

private theorem fixed_all_eq_zero (v : Core) (hv : ∀ g : Sym, coreRepresentation (Fin 5) g v = v) : v = 0 := by
  have hh := core_sum v
  rw [Finset.sum_congr rfl (fun g _ => hv g),Finset.sum_const,cubes_card] at hh
  have hz : 20 • v = 0 := by
    rw [←Nat.cast_smul_eq_nsmul (R := ZMod 2)]
    change (20 : ZMod 2) • v = 0
    rw [show (20 : ZMod 2) = 0 from rfl,zero_smul]
  exact hh.symm.trans hz

private theorem axis_left_mem (φ : MulAut (Sym × Sym))
    (hφ : ((⊤ : Subgroup Sym).prod ⊥).map φ.toMonoidHom = (⊤ : Subgroup Sym).prod ⊥)
    (g : Sym) : (φ (g,1)).2 = 1 := by
  have hh : φ (g,1) ∈ (⊤ : Subgroup Sym).prod ⊥ := hφ ▸ mem_map_of_mem φ.toMonoidHom ⟨mem_top _,one_mem _⟩
  exact hh.2

private theorem axis_right_mem (φ : MulAut (Sym × Sym))
    (hφ : ((⊥ : Subgroup Sym).prod ⊤).map φ.toMonoidHom = (⊥ : Subgroup Sym).prod ⊤)
    (g : Sym) : (φ (1,g)).1 = 1 := by
  have hh : φ (1,g) ∈ (⊥ : Subgroup Sym).prod ⊤ := hφ ▸ mem_map_of_mem φ.toMonoidHom ⟨one_mem _,mem_top _⟩
  exact hh.1

private theorem map_symm_self (φ : MulAut (Sym × Sym)) (A : Subgroup (Sym × Sym))
    (hφ : A.map φ.toMonoidHom = A) : A.map φ.symm.toMonoidHom = A := by
  conv_lhs => rw [←hφ,map_map]
  have hc : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id (Sym × Sym) := by
    apply MonoidHom.ext
    intro x
    exact φ.symm_apply_apply x
  rw [hc,Subgroup.map_id]

/-- Preserving the marked actor factors preserves their actual natural summands. -/
theorem normalizer_preserves_axes
    (f : (Core × Core) ≃ₗ[ZMod 2] (Core × Core)) (φ : MulAut (Sym × Sym))
    (hf : ∀ g v, f (action g v) = action (φ g) (f v))
    (h₁ : ((⊤ : Subgroup Sym).prod ⊥).map φ.toMonoidHom = (⊤ : Subgroup Sym).prod ⊥)
    (h₂ : ((⊥ : Subgroup Sym).prod ⊤).map φ.toMonoidHom = (⊥ : Subgroup Sym).prod ⊤) :
    (∀ v : Core, (f (v,0)).2 = 0) ∧ (∀ v : Core, (f (0,v)).1 = 0) := by
  constructor
  · intro v
    apply fixed_all_eq_zero
    intro g
    let a := φ.symm (1,g)
    have ha : a.1 = 1 := axis_right_mem φ.symm (map_symm_self φ _ h₂) g
    have hh := hf a (v,0)
    have hid : action a (v,0) = (v,0) := by rw [action_apply,ha]; simp
    rw [hid,show φ a = (1,g) from φ.apply_symm_apply _] at hh
    exact (congrArg Prod.snd hh).symm
  · intro v
    apply fixed_all_eq_zero
    intro g
    let a := φ.symm (g,1)
    have ha : a.2 = 1 := axis_left_mem φ.symm (map_symm_self φ _ h₁) g
    have hh := hf a (0,v)
    have hid : action a (0,v) = (0,v) := by rw [action_apply,ha]; simp
    rw [hid,show φ a = (g,1) from φ.apply_symm_apply _] at hh
    exact (congrArg Prod.fst hh).symm

private theorem first_automorphism
    (φ : MulAut (Sym × Sym))
    (hφ : ((⊤ : Subgroup Sym).prod ⊥).map φ.toMonoidHom = (⊤ : Subgroup Sym).prod ⊥) :
    ∃ ψ : MulAut Sym, ∀ g, φ (g,1) = (ψ g,1) := by
  let q := (MonoidHom.fst Sym Sym).comp (φ.toMonoidHom.comp (MonoidHom.inl Sym Sym))
  have hinj : Function.Injective q := by
    intro a b hab
    have hh : φ (a,1) = φ (b,1) := Prod.ext hab ((axis_left_mem φ hφ a).trans (axis_left_mem φ hφ b).symm)
    exact congrArg Prod.fst (φ.injective hh)
  have hsurj : Function.Surjective q := by
    intro g
    refine ⟨(φ.symm (g,1)).1,?_⟩
    have hz := axis_left_mem φ.symm (map_symm_self φ _ hφ) g
    have he : ((φ.symm (g,1)).1,1) = φ.symm (g,1) := Prod.ext rfl hz.symm
    change (φ ((φ.symm (g,1)).1,1)).1 = g
    rw [he,φ.apply_symm_apply]
  refine ⟨MulEquiv.ofBijective q ⟨hinj,hsurj⟩,fun g => ?_⟩
  exact Prod.ext rfl (axis_left_mem φ hφ g)

private theorem second_automorphism
    (φ : MulAut (Sym × Sym))
    (hφ : ((⊥ : Subgroup Sym).prod ⊤).map φ.toMonoidHom = (⊥ : Subgroup Sym).prod ⊤) :
    ∃ ψ : MulAut Sym, ∀ g, φ (1,g) = (1,ψ g) := by
  let q := (MonoidHom.snd Sym Sym).comp (φ.toMonoidHom.comp (MonoidHom.inr Sym Sym))
  have hinj : Function.Injective q := by
    intro a b hab
    have hh : φ (1,a) = φ (1,b) := Prod.ext ((axis_right_mem φ hφ a).trans (axis_right_mem φ hφ b).symm) hab
    exact congrArg Prod.snd (φ.injective hh)
  have hsurj : Function.Surjective q := by
    intro g
    refine ⟨(φ.symm (1,g)).2,?_⟩
    have hz := axis_right_mem φ.symm (map_symm_self φ _ hφ) g
    have he : (1,(φ.symm (1,g)).2) = φ.symm (1,g) := Prod.ext hz.symm rfl
    change (φ (1,(φ.symm (1,g)).2)).2 = g
    rw [he,φ.apply_symm_apply]
  refine ⟨MulEquiv.ofBijective q ⟨hinj,hsurj⟩,fun g => ?_⟩
  exact Prod.ext (axis_right_mem φ hφ g) rfl

private theorem split_linear_equiv
    (f : (Core × Core) ≃ₗ[ZMod 2] (Core × Core))
    (h₁ : ∀ v : Core, (f (v,0)).2 = 0) (h₂ : ∀ v : Core, (f (0,v)).1 = 0)
    (h₁' : ∀ v : Core, (f.symm (v,0)).2 = 0) (h₂' : ∀ v : Core, (f.symm (0,v)).1 = 0) :
    ∃ f₁ f₂ : Core ≃ₗ[ZMod 2] Core, ∀ v, f v = (f₁ v.1,f₂ v.2) := by
  let a : Core →ₗ[ZMod 2] Core := (LinearMap.fst _ _ _).comp
    (f.toLinearMap.comp (LinearMap.inl _ _ _))
  let b : Core →ₗ[ZMod 2] Core := (LinearMap.snd _ _ _).comp
    (f.toLinearMap.comp (LinearMap.inr _ _ _))
  have ha : Function.Bijective a := by
    constructor
    · intro v w hvw
      exact congrArg Prod.fst (f.injective (Prod.ext hvw ((h₁ v).trans (h₁ w).symm)))
    · intro v
      refine ⟨(f.symm (v,0)).1,?_⟩
      have he : ((f.symm (v,0)).1,0) = f.symm (v,0) := Prod.ext rfl (h₁' v).symm
      change (f ((f.symm (v,0)).1,0)).1 = v
      rw [he,f.apply_symm_apply]
  have hb : Function.Bijective b := by
    constructor
    · intro v w hvw
      exact congrArg Prod.snd (f.injective (Prod.ext ((h₂ v).trans (h₂ w).symm) hvw))
    · intro v
      refine ⟨(f.symm (0,v)).2,?_⟩
      have he : (0,(f.symm (0,v)).2) = f.symm (0,v) := Prod.ext (h₂' v).symm rfl
      change (f (0,(f.symm (0,v)).2)).2 = v
      rw [he,f.apply_symm_apply]
  refine ⟨LinearEquiv.ofBijective a ha,LinearEquiv.ofBijective b hb,fun v => ?_⟩
  have hh : v = (v.1,0) + (0,v.2) := by ext <;> simp
  conv_lhs => rw [hh,map_add]
  apply Prod.ext
  · change (f (v.1,0)).1 + (f (0,v.2)).1 = a v.1
    rw [h₂,add_zero]
    rfl
  · change (f (v.1,0)).2 + (f (0,v.2)).2 = b v.2
    rw [h₁,zero_add]
    rfl

/-- A linear normalizer preserving both original actor factors is exactly the
pair of their marked permutation actions. -/
theorem normalizer_of_preserves
    (f : (Core × Core) ≃ₗ[ZMod 2] (Core × Core)) (φ : MulAut (Sym × Sym))
    (hf : ∀ g v, f (action g v) = action (φ g) (f v))
    (h₁ : ((⊤ : Subgroup Sym).prod ⊥).map φ.toMonoidHom = (⊤ : Subgroup Sym).prod ⊥)
    (h₂ : ((⊥ : Subgroup Sym).prod ⊤).map φ.toMonoidHom = (⊥ : Subgroup Sym).prod ⊤) :
    ∃ a : Sym × Sym, ∀ v, f v = action a v := by
  obtain ⟨ha₁,ha₂⟩ := normalizer_preserves_axes f φ hf h₁ h₂
  have hf' (g : Sym × Sym) (v : Core × Core) : f.symm (action g v) = action (φ.symm g) (f.symm v) := by
    apply f.injective
    rw [f.apply_symm_apply,hf,φ.apply_symm_apply,f.apply_symm_apply]
  obtain ⟨hi₁,hi₂⟩ := normalizer_preserves_axes f.symm φ.symm hf'
    (map_symm_self φ _ h₁) (map_symm_self φ _ h₂)
  obtain ⟨f₁,f₂,hsplit⟩ := split_linear_equiv f ha₁ ha₂ hi₁ hi₂
  obtain ⟨φ₁,hφ₁⟩ := first_automorphism φ h₁
  obtain ⟨φ₂,hφ₂⟩ := second_automorphism φ h₂
  obtain ⟨a,ha⟩ := FiveCoreNormalizer.normalizer f₁ φ₁ (by
    intro g v
    have hh := congrArg Prod.fst (hf (g,1) (v,0))
    rw [hφ₁,action_apply,hsplit,hsplit,action_apply] at hh
    exact hh)
  obtain ⟨b,hb⟩ := FiveCoreNormalizer.normalizer f₂ φ₂ (by
    intro g v
    have hh := congrArg Prod.snd (hf (1,g) (0,v))
    rw [hφ₂,action_apply,hsplit,hsplit,action_apply] at hh
    exact hh)
  exact ⟨(a,b),fun v => by rw [hsplit,ha,hb]; rfl⟩

/-- A factor-exchanging normalizer cannot fix a nonzero vector on one axis. -/
theorem not_exchange_of_fixed_axis
    (f : (Core × Core) ≃ₗ[ZMod 2] (Core × Core)) (φ : MulAut (Sym × Sym))
    (hf : ∀ g v, f (action g v) = action (φ g) (f v))
    (h₂ : ((⊥ : Subgroup Sym).prod ⊤).map φ.toMonoidHom = (⊤ : Subgroup Sym).prod ⊥)
    (v : Core) (hv : v ≠ 0) (hfv : f (v,0) = (v,0)) : False := by
  apply hv
  apply fixed_all_eq_zero
  intro g
  have hg : (g,1) ∈ ((⊥ : Subgroup Sym).prod ⊤).map φ.toMonoidHom := by
    rw [h₂]
    exact ⟨mem_top _,one_mem _⟩
  obtain ⟨a,ha,he⟩ := hg
  change φ a = (g,1) at he
  have hh := hf a (v,0)
  have hid : action a (v,0) = (v,0) := by
    rw [action_apply,show a.1 = 1 from ha.1]
    simp
  rw [hid,hfv,he,action_apply] at hh
  exact (congrArg Prod.fst hh).symm

/-- The source preserve-or-exchange dichotomy and a single nonzero fixed
axis vector already force a pair of genuine five-letter permutation actions. -/
theorem normalizer_of_fixed_axis
    (f : (Core × Core) ≃ₗ[ZMod 2] (Core × Core)) (φ : MulAut (Sym × Sym))
    (hf : ∀ g v, f (action g v) = action (φ g) (f v))
    (hperm :
      (((⊤ : Subgroup Sym).prod ⊥).map φ.toMonoidHom = (⊤ : Subgroup Sym).prod ⊥ ∧
       ((⊥ : Subgroup Sym).prod ⊤).map φ.toMonoidHom = (⊥ : Subgroup Sym).prod ⊤) ∨
      (((⊤ : Subgroup Sym).prod ⊥).map φ.toMonoidHom = (⊥ : Subgroup Sym).prod ⊤ ∧
       ((⊥ : Subgroup Sym).prod ⊤).map φ.toMonoidHom = (⊤ : Subgroup Sym).prod ⊥))
    (v : Core) (hv : v ≠ 0) (hfv : f (v,0) = (v,0)) :
    ∃ a : Sym × Sym, ∀ v, f v = action a v := by
  rcases hperm with h | h
  · exact normalizer_of_preserves f φ hf h.1 h.2
  · exact (not_exchange_of_fixed_axis f φ hf h.2 v hv hfv).elim

end BinaryPermutation.FivePair
