module

public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients.Max6Action
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers.Centralizer
public import Theory.GroupTheory.PResidual.Quotient
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The two-core lies in the two-residual of Rudvalis max6

For the unchanged ATLAS generators x and y, three short relations force every
2-group image to kill x and give y order at most two. The relations are proved
by evaluating their words at the first three points and applying the existing
three-point rigidity theorem for the centralizer. Thus only nine small point
evaluations are needed, reusing the certified generator maps.

The 2-residual consequently has index at most two. The inverse image of A₅
under the existing surjective five-block action has index exactly two, so it
equals the 2-residual. In particular the action kernel, already identified with
the intrinsic 2-core, is contained in the 2-residual.

Source: the unchanged RuG1-max6W1 generators retained in SylowOvergroups and
GLS3 Table 5.3r, printed p.279. This supplies the residual containment used in
the Rudvalis local A₅ case of Aschbacher–Smith A.3.14(12).
-/

open Subgroup
namespace Rudvalis.CoreQuotients
namespace Max6Residual
open SylowOvergroups
open SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate
open CentralizerCertificate Rudvalis.OuterNormalizer

private theorem eq_one_of_odd_power {G : Type*} [Group G]
    (hG : IsPGroup 2 G) {n : ℕ} (hn : Nat.Coprime 2 n) (g : G) (h : g ^ n = 1) :
    g = 1 := by
  apply (hG.powEquiv hn).injective
  simpa only [IsPGroup.powEquiv_apply, one_pow] using h

private theorem images {G K : Type*} [Group G] [Group K]
    (f : G →* K) (hK : IsPGroup 2 K) (a b : G)
    (h20 : a ^ 20 = 1) (h5 : (a ^ 4 * b ^ 2) ^ 5 = 1)
    (h3 : (a ^ 4 * b ^ 3 * a * b) ^ 3 = 1) : f a = 1 ∧ f b ^ 2 = 1 := by
  have h4 : f a ^ 4 = 1 := by
    apply eq_one_of_odd_power hK (by decide : Nat.Coprime 2 5)
    simpa only [← pow_mul, ← map_pow, map_one] using congrArg f h20
  have hb : f b ^ 2 = 1 := by
    apply eq_one_of_odd_power hK (by decide : Nat.Coprime 2 5)
    simpa only [map_pow, map_mul, map_one, h4, one_mul] using congrArg f h5
  have hab : f b * f a * f b = 1 := by
    apply eq_one_of_odd_power hK (by decide : Nat.Coprime 2 3)
    simpa only [map_pow, map_mul, map_one, h4, one_mul, show 3 = 2 + 1 from rfl,
      pow_add, hb, pow_one] using congrArg f h3
  refine ⟨?_, hb⟩
  have hbb : f b * f b = 1 := by simpa only [pow_two] using hb
  have h := congrArg (fun z => f b * z * f b) hab
  simpa only [mul_assoc, ← mul_assoc (f b) (f b), hbb, one_mul, mul_one] using h

private theorem residual_index_le_two {G : Type*} [Group G] [Finite G]
    (a b : G) (hgen : closure ({a,b} : Set G) = ⊤)
    (h20 : a ^ 20 = 1) (h5 : (a ^ 4 * b ^ 2) ^ 5 = 1)
    (h3 : (a ^ 4 * b ^ 3 * a * b) ^ 3 = 1) : (pResidual 2 G).index ≤ 2 := by
  let q := QuotientGroup.mk' (pResidual 2 G)
  obtain ⟨ha, hb⟩ := images q (isPGroup_quotient_pResidual 2) a b h20 h5 h3
  have hz : zpowers (q b) = ⊤ := by
    have hm := congrArg (Subgroup.map q) hgen
    rw [MonoidHom.map_closure, map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at hm
    simpa only [Set.image_insert_eq, Set.image_singleton, ha, closure_insert_one,
      ← zpowers_eq_closure] using hm
  calc
    (pResidual 2 G).index = Nat.card (zpowers (q b)) := by rw [hz, card_top]; rfl
    _ = orderOf (q b) := Nat.card_zpowers _
    _ ≤ 2 := orderOf_le_of_pow_eq_one (by decide) hb

private theorem ker_le_residual {G : Type*} [Group G] [Finite G]
    (a b : G) (hgen : closure ({a,b} : Set G) = ⊤)
    (h20 : a ^ 20 = 1) (h5 : (a ^ 4 * b ^ 2) ^ 5 = 1)
    (h3 : (a ^ 4 * b ^ 3 * a * b) ^ 3 = 1)
    (f : G →* Equiv.Perm (Fin 5)) (hf : Function.Surjective f) :
    f.ker ≤ pResidual 2 G := by
  let K := (alternatingGroup (Fin 5)).comap f
  have hKi : K.index = 2 := by
    rw [Subgroup.index_comap_of_surjective _ hf, alternatingGroup.index_eq_two]
  have hRK : pResidual 2 G ≤ K := by
    apply (pResidual_le_iff_isPGroup_quotient 2 K).mpr
    apply IsPGroup.of_card (n := 1)
    exact hKi
  have hi := residual_index_le_two a b hgen h20 h5 h3
  have he : pResidual 2 G = K := by
    by_contra hne
    have hlt := Subgroup.index_strictAnti (lt_of_le_of_ne hRK hne)
    omega
  rw [he]
  intro g hg
  change f g ∈ alternatingGroup (Fin 5)
  rw [MonoidHom.mem_ker.mp hg]
  exact Subgroup.one_mem _
private def x : max6 := ⟨first, first_mem⟩
private def y : max6 := ⟨second, second_mem⟩
private def letter : Fin 2 → max6 := ![x,y]
private def letterMap : Fin 2 → Fin 4060 → Fin 4060 := ![firstMap,secondMap]
private def product (w : List (Fin 2)) : max6 := (w.map letter).prod
private def productMap (w : List (Fin 2)) (z : Fin 4060) : Fin 4060 :=
  w.foldr (fun i t => letterMap i t) z

private theorem productMap_eq (w : List (Fin 2)) (z : Fin 4060) :
    productMap w z = (product w).val.val z := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [productMap,List.foldr_cons,product,List.map_cons,List.prod_cons]
    change letterMap i (productMap w z) = (letter i).val.val ((product w).val.val z)
    rw [ih]
    fin_cases i <;> rfl

private theorem eval_commute {α : Type*} {H : Subgroup (Equiv.Perm α)}
    (g z : H) (h : g * z = z * g) (a : α) :
    g.val (z.val a) = z.val (g.val a) :=
  congrArg (fun t : H => t.val a) h

private theorem eq_one_of_three_fixed (g : max6)
    (hf : ∀ z : Fin 4060, z.val < 3 → g.val.val z = z) : g = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply fix_three_eq_one g.val.val
    (model_le_relationAut aPerm_mem_relationAut bPerm_mem_relationAut g.val.property)
  · intro z
    have h := eval_commute g.val centralInvolution
      (mem_centralizer_singleton_iff.mp (max6_le_centralizer g.property)) z
    simpa only [centralInvolution_val] using h
  · exact hf

private def relations : Fin 3 → List (Fin 2) :=
  ![List.replicate 20 0,
    List.flatten (List.replicate 5 [0,0,0,0,1,1]),
    List.flatten (List.replicate 3 [0,0,0,0,1,1,1,0,1])]

private theorem relations_fixed : ∀ i : Fin 3, ∀ z : Fin 3,
    productMap (relations i) ⟨z.val, by omega⟩ = ⟨z.val, by omega⟩ := by
  decide +kernel

private theorem relations_eq_one (i : Fin 3) : product (relations i) = 1 := by
  apply eq_one_of_three_fixed
  intro z hz
  rw [← productMap_eq]
  exact relations_fixed i ⟨z.val,hz⟩

private theorem rel_twenty : x ^ 20 = 1 := by
  simpa only [relations,Matrix.cons_val_zero,product,List.map_replicate,
    List.prod_replicate,letter,Matrix.cons_val_zero] using relations_eq_one 0

private theorem rel_five : (x ^ 4 * y ^ 2) ^ 5 = 1 := by
  have h := relations_eq_one 1
  simpa [relations,product,letter,List.prod_flatten,List.map_flatten,List.map_replicate,
    List.prod_replicate,pow_succ,mul_assoc] using h

private theorem rel_three : (x ^ 4 * y ^ 3 * x * y) ^ 3 = 1 := by
  have h := relations_eq_one 2
  simpa [relations,product,letter,List.prod_flatten,List.map_flatten,List.map_replicate,
    List.prod_replicate,pow_succ,mul_assoc] using h

private theorem generators_closure : closure ({x,y} : Set max6) = ⊤ := by
  apply Subgroup.map_injective max6.subtype_injective
  rw [MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]
  change closure ({first,second} : Set Model) = max6
  rw [first_model_eq, second_model_eq]
  rfl

end Max6Residual

/-- The intrinsic two-core of the original max6 subgroup lies in its two-residual. -/
public theorem max6_pCore_le_pResidual :
    pCore 2 SylowOvergroups.max6 ≤ pResidual 2 SylowOvergroups.max6 := by
  rw [← max6FiveAction_ker]
  exact Max6Residual.ker_le_residual Max6Residual.x Max6Residual.y
    Max6Residual.generators_closure Max6Residual.rel_twenty
    Max6Residual.rel_five Max6Residual.rel_three
    max6FiveAction max6FiveAction_surjective

end Rudvalis.CoreQuotients
