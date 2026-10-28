module
public import Theory.GroupTheory.AutomorphismSquareRank
public import Theory.GroupTheory.WreathTwoElementaryRank

/-!
# Automorphisms of a centerless quasisimple square

The factor automorphisms and interchange identify Aut(S × S) with the literal
regular wreath product Aut(S) wr C₂. The normal form for automorphisms of a
simple square proves surjectivity; the two coordinates prove injectivity.
The inner-conjugation formula records each original factor separately.

Source application: Aschbacher--Smith 14.6.14, printed p.1033. The exchanged
closure action uses these coordinates before determining its outer image.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.AutomorphismSquare
open WreathTwoElementaryRank
variable {S : Type*} [Group S]

@[expose] def wreathMap (w : W (MulAut S)) : MulAut (S × S) :=
  if w.right = 1 then (w.left 1).prodCongr (w.left turn)
  else (w.left 1).prodCongr (w.left turn) * MulEquiv.prodComm

theorem wreathMap_apply (w : W (MulAut S)) (x : (S × S)) :
    wreathMap w x = if w.right=1 then (w.left 1 x.1, w.left turn x.2)
      else (w.left 1 x.2, w.left turn x.1) := by
  by_cases h : w.right=1 <;> simp only [wreathMap,h,ite_true,ite_false] <;> rfl

@[expose] def wreathHom : W (MulAut S) →* MulAut (S × S) where
  toFun := wreathMap
  map_one' := by ext x <;> simp [wreathMap_apply]
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    change wreathMap (a*b) x = wreathMap a (wreathMap b x)
    rcases index_cases a.right with ha | ha <;>
      rcases index_cases b.right with hb | hb <;>
      simp [wreathMap_apply,ha,hb,turn_ne_one]

theorem wreathHom_injective [Nontrivial S] : Function.Injective (wreathHom (S := S)) := by
  apply (injective_iff_map_eq_one wreathHom).mpr
  intro w hw
  have hh (x : (S × S)) : wreathMap w x = x := MulEquiv.congr_fun hw x
  rcases index_cases w.right with hr | hr
  · have ha : w.left 1 = 1 := by
      apply MulEquiv.ext
      intro x
      simpa [wreathMap_apply,hr] using congrArg Prod.fst (hh (x,1))
    have hb : w.left turn = 1 := by
      apply MulEquiv.ext
      intro x
      simpa [wreathMap_apply,hr] using congrArg Prod.snd (hh (1,x))
    have h1 : w.left 1 = 1 := ha
    have h2 : w.left turn = 1 := hb
    apply RegularWreathProduct.ext
    · funext i
      rcases index_cases i with rfl | rfl
      · exact h1
      · exact h2
    · exact hr
  · obtain ⟨x,hx⟩ := exists_ne (1 : S)
    have hf := congrArg Prod.fst (hh (x,1))
    have he : x = 1 := by simpa [wreathMap_apply,hr,turn_ne_one] using hf.symm
    exact (hx he).elim

theorem wreathHom_surjective [Finite S] [IsQuasisimple S] (hz : center S = ⊥) : Function.Surjective (wreathHom (S := S)) := by
  intro f
  rcases AutomorphismSquare.normal_form hz f with
    ⟨a,b,h⟩ | ⟨a,b,h⟩
  · refine ⟨baseHom (a,b),?_⟩
    apply MulEquiv.ext
    intro x
    simp [wreathHom,wreathMap,baseHom,h,turn_ne_one]
  · let w : W (MulAut S) := ⟨fun i => if i=1 then a else b,turn⟩
    refine ⟨w,?_⟩
    apply MulEquiv.ext
    intro x
    simp [wreathHom,wreathMap,w,h,turn_ne_one]

@[expose] def wreathEquiv [Finite S] [IsQuasisimple S] (hz : center S = ⊥) : W (MulAut S) ≃* MulAut (S × S) := by
  let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
  let : Nontrivial S := (QuotientGroup.mk'_surjective (center S)).nontrivial
  exact MulEquiv.ofBijective wreathHom ⟨wreathHom_injective,wreathHom_surjective hz⟩


theorem wreathHom_inner (a b : S) :
    wreathHom (baseHom (MulAut.conj a, MulAut.conj b)) = MulAut.conj (a,b) := by
  apply MulEquiv.ext
  intro x
  change wreathMap (baseHom (MulAut.conj a, MulAut.conj b)) x = _
  rw [wreathMap_apply]
  simp [baseHom,turn_ne_one]
  rfl

theorem wreathEquiv_apply [Finite S] [IsQuasisimple S] (hz : center S = ⊥)
    (w : W (MulAut S)) : wreathEquiv hz w = wreathHom w := rfl

end Theory.GroupTheory.AutomorphismSquare
