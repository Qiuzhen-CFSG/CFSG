module

public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Factors.Action
/-!
# Centralizers of cubic quaternion automorphisms

A nontrivial cubic automorphism of Q₈ has cyclic centralizer of order three.
The proof uses existing cubic coordinates and checks the two generator images
in the eight-element group, then transports along a supplied quaternion model.
This supplies the independent-factor centralizer in Aschbacher (1994), §45.
-/

open QuaternionGroup GLS3.Chapter5.SchurPresentation
namespace QuaternionGroup
private abbrev Q := QuaternionGroup 2
private def generatorMap (a b : Q) : Q → Q
  | .a i => a^i.val
  | .xa i => b*a^i.val
private theorem commuting_pair_table : ∀ a b : Q,
    a^2≠1 → b^2≠1 → a*b≠b*a →
    generatorMap a b (q8Cycle (.a 1))=q8Cycle a →
    generatorMap a b (q8Cycle (.xa 0))=q8Cycle b →
    ∃ i : Fin 3, a=(q8Cycle^i.val) (.a 1) ∧ b=(q8Cycle^i.val) (.xa 0) := by
  decide
private theorem generatorMap_aut (f : MulAut Q) (x : Q) :
    generatorMap (f (.a 1)) (f (.xa 0)) x=f x := by
  cases x with
  | a i =>
    change (f (.a 1))^i.val=f (.a i)
    rw [←map_pow,a_one_pow,ZMod.natCast_zmod_val]
  | xa i =>
    change f (.xa 0)*(f (.a 1))^i.val=f (.xa i)
    rw [←map_pow,←map_mul,a_one_pow,ZMod.natCast_zmod_val,xa_mul_a,zero_add]

public theorem exists_pow_eq_of_commute_q8Cycle (f : MulAut (QuaternionGroup 2)) (hf : Commute f q8Cycle) :
    ∃ i : Fin 3, f=q8Cycle^i.val := by
  have ha : (f (.a 1))^2≠1 := by
    intro hh
    have he : (.a 1 : Q)^2=1 := f.injective (by simpa only [map_pow,map_one] using hh)
    exact (by decide : (.a 1 : Q)^2≠1) he
  have hb : (f (.xa 0))^2≠1 := by
    intro hh
    have he : (.xa 0 : Q)^2=1 := f.injective (by simpa only [map_pow,map_one] using hh)
    exact (by decide : (.xa 0 : Q)^2≠1) he
  have hab : f (.a 1)*f (.xa 0)≠f (.xa 0)*f (.a 1) := by
    intro hh
    have he : (.a 1 : Q)*(.xa 0)=(.xa 0)*(.a 1) :=
      f.injective (by simpa only [map_mul] using hh)
    exact (by decide : (.a 1 : Q)*(.xa 0)≠(.xa 0)*(.a 1)) he
  obtain ⟨i,hi,hj⟩ := commuting_pair_table _ _ ha hb hab
    (by rw [generatorMap_aut]; exact DFunLike.congr_fun hf.eq (.a 1))
    (by rw [generatorMap_aut]; exact DFunLike.congr_fun hf.eq (.xa 0))
  refine ⟨i,?_⟩
  ext x
  rw [←generatorMap_aut f x,hi,hj,generatorMap_aut]

public theorem exists_pow_eq_of_commute_cubic (a f : MulAut (QuaternionGroup 2))
    (ha : a^3=1) (hne : a≠1) (hf : Commute f a) :
    ∃ i : Fin 3, f=a^i.val := by
  obtain ⟨e,he⟩ := Subgroup.QuaternionCubicAction.exists_coordinates a ha hne
  let φ := MulAut.congr e
  obtain ⟨i,hi⟩ := exists_pow_eq_of_commute_q8Cycle (φ f)
    (by rw [←he]; exact hf.map φ.toMonoidHom)
  refine ⟨i,φ.injective ?_⟩
  rw [map_pow,he]
  exact hi

public theorem exists_pow_eq_of_commute_cubic_of_equiv {B : Type*} [Group B]
    (e : B≃*QuaternionGroup 2) (a f : MulAut B) (ha : a^3=1) (hne : a≠1)
    (hf : Commute f a) : ∃ i : Fin 3, f=a^i.val := by
  let φ := MulAut.congr e
  obtain ⟨i,hi⟩ := exists_pow_eq_of_commute_cubic (φ a) (φ f)
    (by rw [←map_pow,ha,map_one])
    (fun hh=>hne (φ.injective (hh.trans φ.map_one.symm))) (hf.map φ.toMonoidHom)
  exact ⟨i,φ.injective (by rwa [map_pow])⟩
end QuaternionGroup
