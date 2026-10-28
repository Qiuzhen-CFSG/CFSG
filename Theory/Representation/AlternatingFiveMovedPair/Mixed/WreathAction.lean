module
public import Theory.Representation.AlternatingFiveMovedPair.Mixed
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors
public import Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms

/-!
# The symmetric wreath action on the mixed A₅ tensor pair

The product S₅ × S₅ acts on N ⊗ D and D ⊗ N, while the nontrivial
wreath permutation exchanges the summands using tensor commutation. This
literal action realizes every marked automorphism of A₅ × A₅. Its
nonidentity involutions have displacement at least twelve: preserving
involutions use the two tensor formulas, and exchanging involutions move
exactly half the thirty-two dimensional space.

This supplies the involutive lifts used in the full-normalizer estimate for
Aschbacher–Smith D.3.5, printed pp.195–196.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace Representation.AlternatingFiveMovedPair.Mixed
open SL2FourNatural SL2FourNatural.SemilinearNormalizer
open Theory.GroupTheory.WreathTwoElementaryRank

abbrev Wreath := Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.Wreath
abbrev Alt := Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.Alt
abbrev Pair := Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.Pair

def exchange : Space ≃ₗ[ZMod 2] Space :=
  (LinearEquiv.prodComm (ZMod 2) ND DN).trans
    ((_root_.TensorProduct.comm (ZMod 2) Deleted Natural).prodCongr
      (_root_.TensorProduct.comm (ZMod 2) Natural Deleted))

lemma exchange_apply (v : ND) (w : DN) :
    exchange (v,w) = (_root_.TensorProduct.comm (ZMod 2) Deleted Natural w,
      _root_.TensorProduct.comm (ZMod 2) Natural Deleted v) := rfl

lemma exchange_square : exchange.toLinearMap * exchange.toLinearMap = 1 := by
  apply LinearMap.ext
  rintro ⟨v,w⟩
  change ((_root_.TensorProduct.comm (ZMod 2) Deleted Natural)
      (_root_.TensorProduct.comm (ZMod 2) Natural Deleted v),
    (_root_.TensorProduct.comm (ZMod 2) Natural Deleted)
      (_root_.TensorProduct.comm (ZMod 2) Deleted Natural w)) = (v,w)
  simp

lemma exchange_extended (p q : Sym) (x : Space) :
    exchange (extendedAction (p,q) x) = extendedAction (q,p) (exchange x) := by
  rcases x with ⟨v,w⟩
  apply Prod.ext
  · change (_root_.TensorProduct.comm (ZMod 2) Deleted Natural)
      (_root_.TensorProduct.map (deletedAction p) (naturalAction q) w) =
      _root_.TensorProduct.map (naturalAction q) (deletedAction p)
        (_root_.TensorProduct.comm (ZMod 2) Deleted Natural w)
    induction w using _root_.TensorProduct.induction_on with
    | zero => simp
    | tmul u v => rfl
    | add x y hx hy => simp only [map_add,hx,hy]
  · change (_root_.TensorProduct.comm (ZMod 2) Natural Deleted)
      (_root_.TensorProduct.map (naturalAction p) (deletedAction q) v) =
      _root_.TensorProduct.map (deletedAction q) (naturalAction p)
        (_root_.TensorProduct.comm (ZMod 2) Natural Deleted v)
    induction v using _root_.TensorProduct.induction_on with
    | zero => simp
    | tmul u v => rfl
    | add x y hx hy => simp only [map_add,hx,hy]

def wreathOperator (w : Wreath) : Module.End (ZMod 2) Space :=
  if w.right=1 then extendedAction (w.left 1,w.left turn)
  else extendedAction (w.left 1,w.left turn) * exchange.toLinearMap

lemma wreathOperator_apply (w : Wreath) (x : Space) :
    wreathOperator w x = if w.right=1 then extendedAction (w.left 1,w.left turn) x
      else extendedAction (w.left 1,w.left turn) (exchange x) := by
  by_cases h:w.right=1 <;> simp [wreathOperator,h]

lemma extended_mul (p q r s : Sym) (x : Space) :
    extendedAction (p*r,q*s) x = extendedAction (p,q) (extendedAction (r,s) x) :=
  LinearMap.congr_fun (map_mul extendedAction (p,q) (r,s)) x

def wreathRepresentation : Representation (ZMod 2) Wreath Space where
  toFun := wreathOperator
  map_one' := by
    change extendedAction 1=1
    exact map_one extendedAction
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    change wreathOperator (a*b) x = wreathOperator a (wreathOperator b x)
    have hs (x : Space) : exchange (exchange x) = x :=
      LinearMap.congr_fun exchange_square x
    rcases index_cases a.right with ha | ha <;>
      rcases index_cases b.right with hb | hb <;>
      simp [wreathOperator_apply,ha,hb,turn_ne_one,exchange_extended,hs,extended_mul]

lemma wreathRepresentation_apply (w : Wreath) (x : Space) :
    wreathRepresentation w x = if w.right=1 then extendedAction (w.left 1,w.left turn) x
      else extendedAction (w.left 1,w.left turn) (exchange x) :=
  wreathOperator_apply w x

def altAction : Representation (ZMod 2) Pair Space :=
  extendedAction.comp ((alternatingGroup (Fin 5)).subtype.prodMap
    (alternatingGroup (Fin 5)).subtype)

def pairEquiv : (SL × SL) ≃* Pair := alternatingFiveEquiv.prodCongr alternatingFiveEquiv

lemma action_pairEquiv (g : SL × SL) : action g = altAction (pairEquiv g) := rfl

lemma extended_intertwines (p q : Sym) (a : Pair) (x : Space) :
    extendedAction (p,q) (altAction a x) =
      altAction ((Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.factorEquiv p) a.1,
        (Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.factorEquiv q) a.2)
        (extendedAction (p,q) x) := by
  change extendedAction (p,q) (extendedAction (a.1.val,a.2.val) x) =
    extendedAction (p*a.1.val*p⁻¹,q*a.2.val*q⁻¹) (extendedAction (p,q) x)
  rw [←Module.End.mul_apply,←Module.End.mul_apply,←map_mul,←map_mul]
  congr 1
  ext <;> simp [mul_assoc]

lemma exchange_alt (a : Pair) (x : Space) :
    exchange (altAction a x) = altAction (a.2,a.1) (exchange x) :=
  exchange_extended _ _ _

lemma wreath_intertwines (w : Wreath) (a : Pair) (x : Space) :
    wreathRepresentation w (altAction a x) =
      altAction (Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.wreathHom w a)
        (wreathRepresentation w x) := by
  change wreathOperator w (altAction a x) =
    altAction (Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.wreathMap w a)
      (wreathOperator w x)
  rw [Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.wreathMap_apply]
  by_cases h : w.right=1
  · simpa only [wreathOperator_apply,h,ite_true] using
      extended_intertwines (w.left 1) (w.left turn) a x
  · simpa only [wreathOperator_apply,h,ite_false,exchange_alt] using
      extended_intertwines (w.left 1) (w.left turn) (a.2,a.1) (exchange x)

lemma wreath_displacement_ge_twelve (w : Wreath) (hw : w*w=1) (hne : w≠1) :
    12 ≤ BinaryOffender.NaturalTensor.operatorFixedCodim (wreathRepresentation w) := by
  by_cases h : w.right=1
  · have hsq : (w.left 1,w.left turn)*(w.left 1,w.left turn)=1 := by
      apply Prod.ext
      · simpa [h] using congrArg (fun z : Wreath => z.left 1) hw
      · simpa [h] using congrArg (fun z : Wreath => z.left turn) hw
    have hnon : (w.left 1,w.left turn) ≠ (1 : Sym×Sym) := by
      intro he
      apply hne
      apply RegularWreathProduct.ext
      · funext i
        rcases index_cases i with rfl | rfl
        · exact congrArg Prod.fst he
        · exact congrArg Prod.snd he
      · exact h
    change 12 ≤ BinaryOffender.NaturalTensor.operatorFixedCodim (wreathOperator w)
    simpa only [wreathOperator,h,ite_true] using extended_displacement_ge_twelve _ hsq hnon
  · have hs : wreathRepresentation w * wreathRepresentation w = 1 := by
      rw [←map_mul,hw,map_one]
    let a : ND →ₗ[ZMod 2] DN := (second (w.left 1,w.left turn)).comp
      (_root_.TensorProduct.comm (ZMod 2) Natural Deleted).toLinearMap
    let b : DN →ₗ[ZMod 2] ND := (first (w.left 1,w.left turn)).comp
      (_root_.TensorProduct.comm (ZMod 2) Deleted Natural).toLinearMap
    have he : ∀ v z, wreathRepresentation w (v,z) = (b z,a v) := by
      intro v z
      simp only [wreathRepresentation_apply,h,ite_false]
      rfl
    have hd := exchanging_displacement (wreathRepresentation w) a b he hs
    omega

end Representation.AlternatingFiveMovedPair.Mixed
