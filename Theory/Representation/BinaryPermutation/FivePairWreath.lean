module
public import Theory.Representation.BinaryPermutation.FivePairNormalizer
public import Theory.Representation.BinaryPermutation.FivePairFaithful
public import Mathlib.GroupTheory.RegularWreathProduct
/-!
# The concrete wreath action on two five-letter cores

The base acts separately on the two natural cores and the nonidentity element
of C₂ swaps the input coordinates. The action is faithful. The five-letter
normalizer theorem identifies each factor-preserving or factor-exchanging
normalizer with a unique actor in this literal regular wreath product.

Source: Aschbacher–Smith B.6.9 and E.2.3(3), pp.115–116 and216–217.
-/
@[expose] public section
open Subgroup Representation
namespace BinaryPermutation.FivePair
open FiveCentralExtension
abbrev C2 := Multiplicative (ZMod 2)
abbrev Wreath := RegularWreathProduct Sym C2
abbrev LinearWreath := RegularWreathProduct (Core ≃ₗ[ZMod 2] Core) C2
def swapIndex : C2 := Multiplicative.ofAdd 1
private theorem index_cases : ∀ i : C2, i = 1 ∨ i = swapIndex := by decide
@[simp] theorem swapIndex_ne_one : swapIndex ≠ 1 := by decide
@[simp] theorem swapIndex_inv : swapIndex⁻¹ = swapIndex := by decide
@[simp] theorem swapIndex_mul_self : swapIndex * swapIndex = 1 := by decide

def linearWreathMap (w : LinearWreath) : (Core × Core) ≃ₗ[ZMod 2] (Core × Core) :=
  if w.right = 1 then (w.left 1).prodCongr (w.left swapIndex)
  else (LinearEquiv.prodComm (ZMod 2) Core Core).trans
    ((w.left 1).prodCongr (w.left swapIndex))

def linearWreathHom : LinearWreath →* ((Core × Core) ≃ₗ[ZMod 2] (Core × Core)) where
  toFun := linearWreathMap
  map_one' := by
    apply LinearEquiv.ext
    intro v
    simp [linearWreathMap]
  map_mul' a b := by
    apply LinearEquiv.ext
    intro v
    rcases index_cases a.right with ha | ha <;>
      rcases index_cases b.right with hb | hb <;>
      simp [linearWreathMap, RegularWreathProduct.mul_left,
        RegularWreathProduct.mul_right, ha, hb, LinearEquiv.mul_apply]

private theorem linearWreathHom_injective : Function.Injective linearWreathHom := by
  apply (injective_iff_map_eq_one linearWreathHom).mpr
  intro w hw
  have hf : linearWreathMap w = 1 := hw
  rcases index_cases w.right with h | h
  · apply RegularWreathProduct.ext
    · funext i
      rcases index_cases i with rfl | rfl
      · apply LinearEquiv.ext
        intro v
        have hh := congrArg (fun f : (Core × Core) ≃ₗ[ZMod 2] (Core × Core) => f (v,0)) hf
        simpa [linearWreathMap, h] using congrArg Prod.fst hh
      · apply LinearEquiv.ext
        intro v
        have hh := congrArg (fun f : (Core × Core) ≃ₗ[ZMod 2] (Core × Core) => f (0,v)) hf
        simpa [linearWreathMap, h] using congrArg Prod.snd hh
    · exact h
  · let v : Core := ⟨![1,1,0,0,0], by simp [BinaryPermutation.mem_core]; decide +kernel⟩
    have hv : v ≠ 0 := by
      intro hv
      have hval := congrArg Subtype.val hv
      norm_num [v] at hval
    exfalso
    have hh := congrArg (fun f : (Core × Core) ≃ₗ[ZMod 2] (Core × Core) => f (v,0)) hf
    have hz := congrArg Prod.fst hh
    have hz' : v = 0 := by simpa [linearWreathMap, h] using hz.symm
    exact hv hz'

noncomputable def coreActionEquiv : Sym →* (Core ≃ₗ[ZMod 2] Core) where
  toFun g := LinearEquiv.ofBijective (coreRepresentation (Fin 5) g)
    ((coreRepresentation (Fin 5)).apply_bijective g)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    change coreRepresentation (Fin 5) (g*h) v = _
    change coreRepresentation (Fin 5) (g*h) v =
      coreRepresentation (Fin 5) g (coreRepresentation (Fin 5) h v)
    rw [← Module.End.mul_apply, ← map_mul]
noncomputable def wreathLift : Wreath →* LinearWreath where
  toFun w := ⟨fun i => coreActionEquiv (w.left i), w.right⟩
  map_one' := by
    apply RegularWreathProduct.ext
    · funext i
      simp
    · simp
  map_mul' a b := by
    apply RegularWreathProduct.ext
    · funext i
      simp [RegularWreathProduct.mul_left]
    · simp [RegularWreathProduct.mul_right]
noncomputable def wreathToLinear : Wreath →* ((Core × Core) ≃ₗ[ZMod 2] (Core × Core)) :=
  linearWreathHom.comp wreathLift

@[simp] theorem wreathToLinear_apply (w : Wreath) :
    wreathToLinear w = linearWreathMap (wreathLift w) := rfl

theorem coreActionEquiv_injective : Function.Injective coreActionEquiv := by
  intro a b hab
  apply BinaryPermutation.FivePair.core_injective
  apply LinearMap.ext
  intro v
  exact congrArg (fun e : Core ≃ₗ[ZMod 2] Core => e v) hab

theorem wreathToLinear_injective : Function.Injective wreathToLinear := by
  intro a b hab
  have hh : wreathLift a = wreathLift b := linearWreathHom_injective hab
  apply RegularWreathProduct.ext
  · funext i
    apply coreActionEquiv_injective
    exact congrArg (fun w : LinearWreath => w.left i) hh
  · exact congrArg (fun w : LinearWreath => w.right) hh

/-- Every normalizer preserving or exchanging the two factors is the concrete wreath action. -/
theorem normalizer_wreath
    (f : (Core × Core) ≃ₗ[ZMod 2] (Core × Core)) (φ : MulAut (Sym × Sym))
    (hf : ∀ g v, f (action g v) = action (φ g) (f v))
    (hperm :
      (((⊤ : Subgroup Sym).prod ⊥).map φ.toMonoidHom = (⊤ : Subgroup Sym).prod ⊥ ∧
       ((⊥ : Subgroup Sym).prod ⊤).map φ.toMonoidHom = (⊥ : Subgroup Sym).prod ⊤) ∨
      (((⊤ : Subgroup Sym).prod ⊥).map φ.toMonoidHom = (⊥ : Subgroup Sym).prod ⊤ ∧
       ((⊥ : Subgroup Sym).prod ⊤).map φ.toMonoidHom = (⊤ : Subgroup Sym).prod ⊥)) :
    ∃ w : Wreath, wreathToLinear w = f := by
  rcases hperm with hp | hp
  · obtain ⟨a,ha⟩ := normalizer_of_preserves f φ hf hp.1 hp.2
    refine ⟨⟨(fun i => if i = 1 then a.1 else a.2),1⟩,?_⟩
    apply LinearEquiv.ext
    intro v
    simpa [wreathToLinear,MonoidHom.comp_apply,linearWreathHom,wreathLift,
      linearWreathMap,if_pos rfl,LinearEquiv.prodCongr_apply,coreActionEquiv,
      LinearEquiv.ofBijective_apply,swapIndex_ne_one,if_false,action_apply] using (ha v).symm
  · let s : MulAut (Sym × Sym) := MulEquiv.prodComm
    let τ := s.trans φ
    have hs₁ : ((⊤ : Subgroup Sym).prod ⊥).map s.toMonoidHom = (⊥ : Subgroup Sym).prod ⊤ := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact ⟨hy.2,hy.1⟩
      · intro hx
        exact ⟨(x.2,x.1),⟨hx.2,hx.1⟩,rfl⟩
    have hs₂ : ((⊥ : Subgroup Sym).prod ⊤).map s.toMonoidHom = (⊤ : Subgroup Sym).prod ⊥ := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact ⟨hy.2,hy.1⟩
      · intro hx
        exact ⟨(x.2,x.1),⟨hx.2,hx.1⟩,rfl⟩
    have hτ₁ : ((⊤ : Subgroup Sym).prod ⊥).map τ.toMonoidHom = (⊤ : Subgroup Sym).prod ⊥ := by
      rw [show τ.toMonoidHom = φ.toMonoidHom.comp s.toMonoidHom from rfl,←map_map,hs₁,hp.2]
    have hτ₂ : ((⊥ : Subgroup Sym).prod ⊤).map τ.toMonoidHom = (⊥ : Subgroup Sym).prod ⊤ := by
      rw [show τ.toMonoidHom = φ.toMonoidHom.comp s.toMonoidHom from rfl,←map_map,hs₂,hp.1]
    let F := (LinearEquiv.prodComm (ZMod 2) Core Core).trans f
    have hF (g : Sym × Sym) (v : Core × Core) : F (action g v) = action (τ g) (F v) := by
      exact hf (g.2,g.1) (v.2,v.1)
    obtain ⟨a,ha⟩ := normalizer_of_preserves F τ hF hτ₁ hτ₂
    refine ⟨⟨(fun i => if i = 1 then a.1 else a.2),swapIndex⟩,?_⟩
    apply LinearEquiv.ext
    intro v
    simpa [wreathToLinear,MonoidHom.comp_apply,linearWreathHom,wreathLift,
      linearWreathMap,swapIndex_ne_one,if_false,LinearEquiv.trans_apply,
      LinearEquiv.prodComm_apply,LinearEquiv.prodCongr_apply,if_pos rfl,coreActionEquiv,
      LinearEquiv.ofBijective_apply,action_apply,F,Prod.swap] using (ha (v.2,v.1)).symm

/-- The coordinatewise copy of the paired symmetric group in the regular wreath product. -/
def base (a : Sym × Sym) : Wreath :=
  ⟨(fun i => if i = 1 then a.1 else a.2),1⟩

theorem wreathToLinear_base (a : Sym × Sym) (v : Core × Core) :
    wreathToLinear (base a) v = action a v := by
  simp [wreathToLinear,linearWreathHom,wreathLift,linearWreathMap,coreActionEquiv,base]

theorem base_coordinates (w : Wreath) (h : w.right = 1) :
    base (w.left 1,w.left swapIndex) = w := by
  apply RegularWreathProduct.ext
  · funext i
    rcases index_cases i with rfl | rfl <;> simp [base]
  · exact h.symm

/-- The binary eight-dimensional wreath module in the literal two-coordinate convention. -/
noncomputable def wreathRepresentation : Representation (ZMod 2) Wreath (Core × Core) where
  toFun w := (wreathToLinear w).toLinearMap
  map_one' := by
    change (wreathToLinear 1).toLinearMap = 1
    rw [map_one]
    rfl
  map_mul' a b := by
    change (wreathToLinear (a*b)).toLinearMap = _
    rw [map_mul]
    rfl

/-- The base permutation is indexed by the output coordinate; the shift exchanges inputs. -/
theorem wreathRepresentation_apply (w : Wreath) (v : Core × Core) :
    wreathRepresentation w v =
      if w.right = 1 then
        (coreRepresentation (Fin 5) (w.left 1) v.1,
          coreRepresentation (Fin 5) (w.left swapIndex) v.2)
      else
        (coreRepresentation (Fin 5) (w.left 1) v.2,
          coreRepresentation (Fin 5) (w.left swapIndex) v.1) := by
  by_cases h : w.right = 1 <;>
    simp [wreathRepresentation,wreathToLinear,linearWreathHom,wreathLift,
      linearWreathMap,coreActionEquiv,h]

theorem wreathRepresentation_injective : Function.Injective wreathRepresentation := by
  intro a b hab
  apply wreathToLinear_injective
  apply LinearEquiv.ext
  intro v
  exact LinearMap.congr_fun hab v

/-- Its base is precisely the kernel of the coordinate interchange. -/
abbrev baseSubgroup : Subgroup Wreath := RegularWreathProduct.rightHom.ker

theorem mem_base_iff (w : Wreath) : w ∈ baseSubgroup ↔ w.right = 1 := Iff.rfl

/-- A subgroup containing every base actor and one interchanging actor is the whole wreath group. -/
theorem range_eq_top_of_base_and_exchange {G : Type*} [Group G]
    (q : G →* Wreath)
    (hbase : ∀ a : Sym × Sym, ∃ g : G, q g = base a)
    (hex : ∃ t : G, (q t).right ≠ 1) : Function.Surjective q := by
  obtain ⟨t,ht⟩ := hex
  have ht' : (q t).right = swapIndex := (index_cases _).resolve_left ht
  intro w
  rcases index_cases w.right with hw | hw
  · obtain ⟨g,hg⟩ := hbase (w.left 1,w.left swapIndex)
    exact ⟨g,hg.trans (base_coordinates w hw)⟩
  · let u := w * (q t)⁻¹
    have hu : u.right = 1 := by
      simp only [u,RegularWreathProduct.mul_right,RegularWreathProduct.inv_right,
        hw,ht',swapIndex_inv,swapIndex_mul_self]
    obtain ⟨g,hg⟩ := hbase (u.left 1,u.left swapIndex)
    refine ⟨g*t,?_⟩
    rw [map_mul,hg,base_coordinates u hu]
    exact inv_mul_cancel_right w (q t)

end BinaryPermutation.FivePair
