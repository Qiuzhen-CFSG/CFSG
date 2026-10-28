module
public import Theory.Representation.BinaryTensorThree.ConstituentStability
public import Theory.Representation.BinaryTensorThree.FactorInertia

/-!
# Restriction of a marked tensor to its actual components

A component of GL₃(2) × GL₃(2) is one of the coordinate factors. If it differs
from the first factor, component commutation and centerlessness place it in
the second; containment between components gives equality. Consequently an
arbitrary marked tensor restricts on any actual component to three natural
copies. Transposition treats the first coordinate using the same right-factor
convention as FactorInertia.

The equivalence produced here marks the actual component, so no compatibility
between an independently chosen pair marking and component marking is assumed.
This supplies the diagram-automorphism contradiction after whole-group
constituent invariance in the terminal14.6.22 application.
Source: Aschbacher--Smith D.3.7 and F.9.18(5ii), pp.197--199,325--326.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace BinaryTensorThree
private def naturalFactorEquiv : Matrix.PSL3Two.SL ≃* Factor :=
  Matrix.PSL3Two.equivGL.trans
    ((Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := ZMod 2)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Natural))

private theorem factor_center : center Factor = ⊥ := by
  apply bot_unique
  intro g hg
  apply mem_bot.mpr
  have hz : naturalFactorEquiv.symm g ∈ center Matrix.PSL3Two.SL := by
    rw [mem_center_iff] at hg ⊢
    intro x
    apply naturalFactorEquiv.injective
    simpa using hg (naturalFactorEquiv x)
  rw [Matrix.PSL3Two.center_eq_bot,mem_bot] at hz
  exact naturalFactorEquiv.symm.injective (hz.trans naturalFactorEquiv.symm.map_one.symm)

/-- Every component of the tensor base is one of its actual coordinate factors. -/
theorem component_eq_coordinate (C : Subgroup (Factor × Factor))
    (hC : IsComponent (Factor × Factor) C) :
    C = (MonoidHom.inl Factor Factor).range ∨ C = (MonoidHom.inr Factor Factor).range := by
  let L := (MonoidHom.inl Factor Factor).range
  let R := (MonoidHom.inr Factor Factor).range
  have hiL : Function.Injective (MonoidHom.inl Factor Factor) := fun _ _ h => congrArg Prod.fst h
  have hiR : Function.Injective (MonoidHom.inr Factor Factor) := fun _ _ h => congrArg Prod.snd h
  let : IsQuasisimple Factor := IsQuasisimple.of_mulEquiv naturalFactorEquiv
  let : L.Normal := ⟨by
    rintro x ⟨a,rfl⟩ g
    exact ⟨g.1*a*g.1⁻¹,by ext <;> simp⟩⟩
  let : R.Normal := ⟨by
    rintro x ⟨a,rfl⟩ g
    exact ⟨g.2*a*g.2⁻¹,by ext <;> simp⟩⟩
  have hL : IsComponent (Factor × Factor) L :=
    ⟨(inferInstance : L.Normal).isSubnormal,IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hiL)⟩
  have hR : IsComponent (Factor × Factor) R :=
    ⟨(inferInstance : R.Normal).isSubnormal,IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hiR)⟩
  by_cases he : C = L
  · exact Or.inl he
  right
  apply hC.eq_of_le hR
  intro x hx
  have hc := commutator_eq_bot_iff_le_centralizer.mp (hC.commutator_eq_bot_of_ne hL he) hx
  have hz : x.1 ∈ center Factor := by
    rw [mem_center_iff]
    intro a
    exact congrArg Prod.fst (hc (a,1) ⟨a,rfl⟩)
  rw [factor_center,mem_bot] at hz
  exact ⟨x.2,Prod.ext hz.symm rfl⟩

variable {D V : Type*} [_root_.Group D] [AddCommGroup V] [Module (ZMod 2) V]

/-- A marked tensor for a normal pair restricts to three natural copies on
each actual component, with a marking of that component itself. -/
theorem exists_component_right_tensor_marking
    (σ : Representation (ZMod 2) D V) (N K : Subgroup D)
    (hKN : K ≤ N) (hK : IsComponent N (K.subgroupOf N))
    (e : N ≃* Factor × Factor)
    (b : Representation.Equiv (σ.comp N.subtype) (baseRepresentation.comp e.toMonoidHom)) :
    ∃ eK : K ≃* Factor,
      Nonempty (Representation.Equiv (σ.comp K.subtype) (rightRepresentation.comp eK.toMonoidHom)) := by
  let C := (K.subgroupOf N).map e.toMonoidHom
  let c : K ≃* C := (subgroupOfEquivOfLe hKN).symm.trans (e.subgroupMap (K.subgroupOf N))
  have hc (k : K) : (c k).val = e ⟨k.val,hKN k.property⟩ := rfl
  have hiL : Function.Injective (MonoidHom.inl Factor Factor) := fun _ _ h => congrArg Prod.fst h
  have hiR : Function.Injective (MonoidHom.inr Factor Factor) := fun _ _ h => congrArg Prod.snd h
  have hm (k : K) (v : V) :
      b.toLinearEquiv (σ k.val v) = baseAction (c k).val (b.toLinearEquiv v) :=
    Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap ⟨k.val,hKN k.property⟩ v
  rcases component_eq_coordinate C (hK.map_equiv e) with hL | hR
  · let d := MulEquiv.subgroupCongr hL
    let r := MonoidHom.ofInjective hiL
    let eK := c.trans (d.trans r.symm)
    have hcoord (k : K) : (c k).val = (eK k,1) := by
      exact (MonoidHom.apply_ofInjective_symm hiL (d (c k))).symm
    refine ⟨eK,⟨.mk (b.toLinearEquiv.trans flip) ?_⟩⟩
    intro k
    apply LinearMap.ext
    intro v
    change flip (b.toLinearEquiv (σ k.val v)) = baseAction (1,eK k) (flip (b.toLinearEquiv v))
    rw [hm,hcoord,flip_baseAction]
  · let d := MulEquiv.subgroupCongr hR
    let r := MonoidHom.ofInjective hiR
    let eK := c.trans (d.trans r.symm)
    have hcoord (k : K) : (c k).val = (1,eK k) := by
      exact (MonoidHom.apply_ofInjective_symm hiR (d (c k))).symm
    refine ⟨eK,⟨.mk b.toLinearEquiv ?_⟩⟩
    intro k
    apply LinearMap.ext
    intro v
    change b.toLinearEquiv (σ k.val v) = baseAction (1,eK k) (b.toLinearEquiv v)
    rw [hm,hcoord]
end BinaryTensorThree
