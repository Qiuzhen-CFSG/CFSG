module
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCubic
public import Theory.SpecificGroups.ReeTwo.SylowPackedArithmetic
public import Theory.GroupTheory.SubgroupClosureWords

/-!
# Generating coordinates for the actual native cubic action

A positive word in ten marked generators reconstructs every second-core
element, and transports its cubic action to collected arithmetic. The three
conjugates of the inverse cyclic-four generator cover the full Frattini
quotient of order eight, hence generate the core. An automorphism commuting
with the cubic is therefore determined by its value at that one generator.

This is the finite-coordinate reduction for the F.1.12/J.4.5 second-endpoint
extension problem, using the verified Shinoda/Parrott coordinates. It does
not yet assert the census of possible generator images or extensions.
-/

@[expose] public section
noncomputable section
namespace ReeTwo.SylowModel.CubicAction
open Tits.AmalgamRigidity.FullRee.SecondExtension
open Theory.GroupTheory

/-- A literal positive word for every element in the second core. -/
def normalWord (x:A) : List (Fin 10) :=
  List.replicate x.val.left.b1.val 1 ++ List.replicate x.val.left.b2.val 2 ++
  List.replicate x.val.left.b3.val 3 ++ List.replicate x.val.left.b4.val 4 ++
  List.replicate x.val.left.b5.val 5 ++ List.replicate x.val.left.b6.val 6 ++
  List.replicate x.val.left.b7.val 7 ++ List.replicate x.val.left.b8.val 8 ++
  List.replicate x.val.left.b9.val 9 ++ List.replicate x.val.right⁻¹.toAdd.val 0

private theorem evalWord_replicate {H:Type*} [Group H] {n:ℕ}
    (f:Fin n→H) (k:ℕ) (i:Fin n) : evalWord f (List.replicate k i)=f i^k := by
  induction k with
  | zero => simp only [List.replicate_zero,evalWord,pow_zero]
  | succ k ih => simp only [List.replicate_succ,evalWord,ih,pow_succ']

private theorem evalWord_append {H:Type*} [Group H] {n:ℕ}
    (f:Fin n→H) (u v:List (Fin n)) : evalWord f (u++v)=evalWord f u*evalWord f v := by
  induction u with
  | nil => simp [evalWord]
  | cons i u ih => simp only [List.cons_append,evalWord,ih,mul_assoc]

theorem normalWord_eval (x:A) : evalWord generator (normalWord x)=x := by
  apply A.subtype_injective
  change ((evalWord generator (normalWord x):A):SylowModel)=x.val
  simp only [normalWord,evalWord_append,evalWord_replicate,Subgroup.coe_mul,Subgroup.coe_pow]
  have hx0:x.val.left.b0=0:=(mem_firstParabolicCore_iff _).mp x.property
  have hn:=congrArg (SemidirectProduct.inl : Core→*SylowModel) (Core.normal_form x.val.left)
  simp only [map_mul,map_pow,hx0,ZMod.val_zero,pow_zero,one_mul] at hn
  have ht:SylowModel.rootOne^x.val.right⁻¹.toAdd.val=SemidirectProduct.inr x.val.right := by
    rw [SylowModel.rootOne,←map_pow,inv_pow,FiveFour.generator_pow_val,inv_inv]
  change (root 1^_ *root 2^_ *root 3^_ *root 4^_ *root 5^_ *root 6^_ *root 7^_ *root 8^_ *root 9^_) *rootOne^_=x.val
  rw [ht]
  exact (congrArg (·*SemidirectProduct.inr x.val.right) hn).trans
    (SemidirectProduct.inl_left_mul_inr_right x.val)

/-- Fast coordinate evaluator for the actual native cubic. -/
def cubicEval (x:A):SylowModel :=
  Collected.collectedEval (fun i=>(cubicImage i:SylowModel)) (normalWord x)

theorem cubicEval_eq (x:A) : cubicEval x=(cubic x:SylowModel) := by
  rw [cubicEval,Collected.collectedEval_eq]
  have hword (w:List (Fin 10)) :
      evalWord (fun i=>(cubicImage i:SylowModel)) w=(cubic (evalWord generator w):SylowModel) := by
    induction w with
    | nil => simp only [evalWord,map_one,Subgroup.coe_one]
    | cons i w ih =>
      simp only [evalWord,map_mul,Subgroup.coe_mul]
      rw [ih,cubic_generator]
  rw [hword,normalWord_eval]

/-- The orbit of the inverse cyclic-four generator under the native cubic. -/
def orbit (i:Fin 3):A := ![(generator 0)⁻¹,(generator 1)⁻¹,(cubicImage 1)⁻¹] i

theorem cubic_generator_zero : cubic (generator 0)=generator 1 := by
  rw [cubic_generator]
  exact (by decide +kernel : cubicImage 0=generator 1)

theorem orbit_actual (i:Fin 3) : orbit i=(cubic^i.val) ((generator 0)⁻¹) := by
  fin_cases i
  · rfl
  · simp [orbit,pow_one,map_inv,cubic_generator_zero]
  · change (cubicImage 1)⁻¹=(cubic*cubic) ((generator 0)⁻¹)
    rw [MulAut.mul_apply,map_inv,cubic_generator_zero,map_inv,cubic_generator]

theorem orbit_projection (i:Fin 3) :
    firstParabolicQuotient (orbit i)=Multiplicative.ofAdd (![![1,0,0],![0,1,0],![1,1,1]] i) := by
  exact (by decide +kernel : ∀i:Fin 3,
    firstParabolicQuotient (orbit i)=Multiplicative.ofAdd (![![1,0,0],![0,1,0],![1,1,1]] i)) i

/-- One cubic orbit generates the entire native second core. -/
theorem orbit_generated : Subgroup.closure (Set.range orbit)=⊤ := by
  let K:=Subgroup.closure (Set.range orbit)
  let sectionMap (v:Fin 3→ZMod 2):A :=
    orbit 0^(v 0+v 2).val*orbit 1^(v 1+v 2).val*orbit 2^(v 2).val
  have hm (v:Fin 3→ZMod 2):sectionMap v∈K := by
    exact K.mul_mem (K.mul_mem
      (K.pow_mem (Subgroup.subset_closure ⟨0,rfl⟩) _)
      (K.pow_mem (Subgroup.subset_closure ⟨1,rfl⟩) _))
      (K.pow_mem (Subgroup.subset_closure ⟨2,rfl⟩) _)
  have he (v:Fin 3→ZMod 2):firstParabolicQuotient (sectionMap v)=Multiplicative.ofAdd v := by
    simp only [sectionMap,map_mul,map_pow,orbit_projection]
    exact (by decide +kernel : ∀v:Fin 3→ZMod 2,
      (Multiplicative.ofAdd (![1,0,0]:Fin 3→ZMod 2))^(v 0+v 2).val *
        (Multiplicative.ofAdd (![0,1,0]:Fin 3→ZMod 2))^(v 1+v 2).val *
        (Multiplicative.ofAdd (![1,1,1]:Fin 3→ZMod 2))^(v 2).val=Multiplicative.ofAdd v) v
  have hmap:K.map firstParabolicQuotient=⊤ := by
    apply top_unique
    intro v _
    exact ⟨sectionMap v.toAdd,hm _,he _⟩
  have hsup:K⊔frattini A=⊤ := by
    have hh:=congrArg (Subgroup.comap firstParabolicQuotient) hmap
    rw [Subgroup.comap_map_eq,Subgroup.comap_top,firstParabolicQuotient_ker_eq_frattini] at hh
    exact hh
  exact frattini_nongenerating hsup

/-- A cubic-centralizing automorphism is determined by the first orbit value. -/
theorem commuting_aut_ext (α β:MulAut A) (hα:Commute α cubic) (hβ:Commute β cubic)
    (h:α (orbit 0)=β (orbit 0)) : α=β := by
  apply MulEquiv.toMonoidHom_injective
  apply MonoidHom.eq_of_eqOn_dense orbit_generated
  rintro _ ⟨i,rfl⟩
  change α (orbit i)=β (orbit i)
  rw [orbit_actual]
  have ha:=DFunLike.congr_fun (hα.pow_right i.val).eq ((generator 0)⁻¹)
  have hb:=DFunLike.congr_fun (hβ.pow_right i.val).eq ((generator 0)⁻¹)
  change α ((cubic^i.val) ((generator 0)⁻¹))=(cubic^i.val) (α ((generator 0)⁻¹)) at ha
  change β ((cubic^i.val) ((generator 0)⁻¹))=(cubic^i.val) (β ((generator 0)⁻¹)) at hb
  change α ((generator 0)⁻¹)=β ((generator 0)⁻¹) at h
  exact ha.trans ((congrArg (cubic^i.val) h).trans hb.symm)

end ReeTwo.SylowModel.CubicAction
