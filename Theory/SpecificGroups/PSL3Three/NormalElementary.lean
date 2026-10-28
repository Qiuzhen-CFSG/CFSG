module
public import Theory.SpecificGroups.PSL3Three.EvenLocals

/-!
# Normal elementary subgroups in a PSL₃(3) Sylow subgroup

Transport the proved semidihedral presentation of order sixteen along the
specified model equivalence. Its unique nontrivial normal elementary
subgroup is the central involution line. This supplies the model bound
for the odd-characteristic exclusion in Aschbacher--Smith 15.1.20(3),
printed p.1097.
-/

public section
open Subgroup Theory.GroupTheory
namespace Matrix.PSL3Three
variable {K : Type*} [Group K] [Finite K]

theorem normal_elementary_sylow_card_le_two
    (e : K ≃* SL) (P : Sylow 2 K) (E : Subgroup P)
    [E.Normal] [IsElementaryAbelian 2 E] : Nat.card E ≤ 2 := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let f : P ≃* Q := e.subgroupMap (P : Subgroup K)
  obtain ⟨a,b,ha,hb,hc,hg⟩ := sylowTwo_generators_SL Q
  let a' := f.symm a
  let b' := f.symm b
  have ha' : orderOf a' = 8 := (f.symm.orderOf_eq a).trans ha
  have hb' : orderOf b' = 2 := (f.symm.orderOf_eq b).trans hb
  have hc' : b'*a'*b'⁻¹=a'^3 := by
    dsimp only [a',b']
    rw [←map_inv,←map_mul,←map_mul,hc,map_pow]
  have hg' : closure ({a',b'} : Set P) = ⊤ := by
    have hh := congrArg (Subgroup.map f.symm.toMonoidHom) hg
    rw [MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton,
      map_top_of_surjective _ f.symm.surjective] at hh
    exact hh
  by_cases he : E = ⊥
  · rw [he,card_bot]; omega
  · rw [Semidihedral.normal_elementary_eq_of_order_sixteen a' b' ha' hb' hc' hg' E he,
      Nat.card_zpowers,orderOf_pow,ha']
    norm_num
end Matrix.PSL3Three
