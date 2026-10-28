module
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCubicNormalizer

/-!
# Packed evaluation for source automorphism images

Bit-parallel collected multiplication evaluates a proposed map on all 2,048
core coordinates simultaneously. Reading one bit position recovers the actual
word evaluation. This is the finite evaluator used for the final reflected
extension obstruction.

Source: Shinoda's collected coordinates (1975), (2.3), and the binary Ree
extension calculation in Aschbacher–Smith F.1.12/J.4.5.
-/
@[expose] public section
namespace ReeTwo.SylowModel.CollectedBitVectors
open CubicAction
variable {n:ℕ}
private theorem eval_replicate {H:Type*} [Group H] {m:ℕ}
    (f:Fin m→H) (k:ℕ) (i:Fin m) : Theory.GroupTheory.evalWord f (List.replicate k i)=f i^k := by
  induction k with
  | zero => simp [Theory.GroupTheory.evalWord]
  | succ k ih => simp only [List.replicate_succ,Theory.GroupTheory.evalWord,ih,pow_succ']
private theorem eval_append {H:Type*} [Group H] {m:ℕ}
    (f:Fin m→H) (u v:List (Fin m)) :
    Theory.GroupTheory.evalWord f (u++v)=Theory.GroupTheory.evalWord f u*Theory.GroupTheory.evalWord f v := by
  induction u with
  | nil => simp [Theory.GroupTheory.evalWord]
  | cons i u ih => simp only [List.cons_append,Theory.GroupTheory.evalWord,ih,mul_assoc]

def chosenRoot (images:Fin 10→SylowModel) (b:BitVec n) (i:Fin 10):PackedElement n:=
  choose b (pack 1) (pack (images i))
def chosenRootInverse (images:Fin 10→SylowModel) (b:BitVec n) (k:ℕ):PackedElement n:=
  choose b (pack 1) (pack ((images 0)⁻¹^k))

def packedMap (images:Fin 10→SylowModel) (x:PackedElement n):PackedElement n :=
  product (product (product (product (product (product (product (product (product (product
    (chosenRoot images x.core.b1 1) (chosenRoot images x.core.b2 2))
    (chosenRoot images x.core.b3 3)) (chosenRoot images x.core.b4 4))
    (chosenRoot images x.core.b5 5)) (chosenRoot images x.core.b6 6))
    (chosenRoot images x.core.b7 7)) (chosenRoot images x.core.b8 8))
    (chosenRoot images x.core.b9 9)) (chosenRootInverse images x.t₀ 1)) (chosenRootInverse images x.t₁ 2)

private theorem read_chosenRoot (images:Fin 10→SylowModel) (b:BitVec n) (i:Fin 10) (k:Fin n) :
    read (chosenRoot images b i) k=images i^(zbit (b.getLsbD k.val)).val := by
  simp only [chosenRoot,read_choose,read_pack]
  cases b.getLsbD k.val <;> norm_num [zbit]
  change images i=images i^1
  rw [pow_one]

private theorem read_rootInverse (images:Fin 10→SylowModel) (hfour:images 0^4=1) (x:PackedElement n) (k:Fin n) :
    read (chosenRootInverse images x.t₀ 1) k * read (chosenRootInverse images x.t₁ 2) k=
      images 0^(read x k).right⁻¹.toAdd.val := by
  simp only [chosenRootInverse,read_choose,read_pack]
  change (if x.t₀.getLsbD k.val then (images 0)⁻¹^1 else 1)*
    (if x.t₁.getLsbD k.val then (images 0)⁻¹^2 else 1)=
    images 0^(Multiplicative.ofAdd ((x.t₀.getLsbD k.val).toNat+
      2*(x.t₁.getLsbD k.val).toNat:ZMod 4))⁻¹.toAdd.val
  have hinv:(images 0)⁻¹=images 0^3:=by
    apply inv_eq_of_mul_eq_one_left
    simpa only [←pow_succ] using hfour
  cases x.t₀.getLsbD k.val <;> cases x.t₁.getLsbD k.val
  all_goals simp only [Bool.false_eq_true,if_false,if_true,one_mul,mul_one,pow_one]
  · rfl
  · change (images 0)⁻¹^2=images 0^2
    rw [hinv,←pow_mul]
    calc
      _ = images 0^4*images 0^2 := by rw [←pow_add]
      _ = _ := by rw [hfour,one_mul]
  · exact hinv
  · change (images 0)⁻¹*(images 0)⁻¹^2=images 0^1
    rw [pow_one]
    rw [←pow_succ',hinv,←pow_mul]
    calc
      _ = (images 0^4)^2*images 0 := by rw [←pow_mul,←pow_succ]
      _ = _ := by rw [hfour,one_pow,one_mul]


theorem read_packedMap (images:Fin 10→SylowModel) (hfour:images 0^4=1)
    (x:PackedElement n) (k:Fin n) (a:A) (ha:read x k=(a:SylowModel)) :
    read (packedMap images x) k=Theory.GroupTheory.evalWord images (normalWord a) := by
  simp only [normalWord,eval_append,eval_replicate]
  simp only [packedMap,read_product,read_chosenRoot]
  rw [mul_assoc,read_rootInverse images hfour]
  have hc:=congrArg SemidirectProduct.left ha
  have ht:=congrArg SemidirectProduct.right ha
  change get x.core k=a.val.left at hc
  rw [←hc,←ht]
  rfl

theorem read_packedMap_hom (images:Fin 10→SylowModel) (ρ:A→*A)
    (himages:∀i,images i=(ρ (generator i):SylowModel))
    (x:PackedElement n) (k:Fin n) (a:A) (ha:read x k=(a:SylowModel)) :
    read (packedMap images x) k=(ρ a:SylowModel) := by
  have hfour:images 0^4=1 := by
    rw [himages,←Subgroup.coe_pow,←map_pow]
    have hg:(generator 0)^4=1 := by decide +kernel
    rw [hg,map_one,Subgroup.coe_one]
  have hw (w:List (Fin 10)) : Theory.GroupTheory.evalWord images w=
      (ρ (Theory.GroupTheory.evalWord generator w):SylowModel) := by
    induction w with
    | nil => simp only [Theory.GroupTheory.evalWord,map_one,Subgroup.coe_one]
    | cons i w ih =>
      simp only [Theory.GroupTheory.evalWord,map_mul,Subgroup.coe_mul,himages,ih]
  rw [read_packedMap images hfour x k a ha,hw,normalWord_eval]

end ReeTwo.SylowModel.CollectedBitVectors
