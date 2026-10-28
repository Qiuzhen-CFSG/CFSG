module
public import Theory.SpecificGroups.SymmetricFourWreath.Core.Factors
public import Theory.SpecificGroups.SymmetricFourWreath.LocalStructure.Coordinates

/-!
# The three index-two overgroups of the actual extraspecial core

Abelianizing the two dihedral coordinates gives a surjection P → C2×C2
whose kernel is Q. Its three lines pull back to distinct groups of order64.
The rotation line is the normalizer of the actual first quaternion factor;
the other two lines are AQ and BQ. Both A and B move that quaternion factor.

Source: Aschbacher–Smith 13.9.8(2), printed p.972 (PDF p.989).
-/

@[expose] public section
namespace SymmetricFourWreath
open Subgroup
private instance : DecidableEq P := (RegularWreathProduct.equivProd D8 C2).injective.decidableEq
private instance : Fintype P := Fintype.ofEquiv _ (RegularWreathProduct.equivProd D8 C2).symm

def dihedralFlags : D8→*C2×C2 where
  toFun x := match x with
    | .r i => (1,Multiplicative.ofAdd (i.val:ZMod 2))
    | .sr i => (turn,Multiplicative.ofAdd (i.val:ZMod 2))
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def sylowFlags : P→*C2×C2 where
  toFun x := dihedralFlags (x.left 1)*dihedralFlags (x.left turn)
  map_one' := by simp
  map_mul' x y := by
    change dihedralFlags (x.left 1*y.left (x.right⁻¹*1))*
      dihedralFlags (x.left turn*y.left (x.right⁻¹*turn)) = _
    rcases c2_eq_one_or_turn x.right with hx|hx
    · rw [hx]
      simp only [inv_one,one_mul,map_mul]
      ac_rfl
    · rw [hx]
      simp only [turn_inv,mul_one,turn_sq,map_mul]
      ac_rfl

theorem sylowFlags_ker : sylowFlags.ker=coreInP := by
  ext x
  rw [MonoidHom.mem_ker,mem_coreInP]
  exact (by decide +kernel : ∀a b:D8,dihedralFlags a*dihedralFlags b=1 ↔
    a*b⁻¹=1 ∨ a*b⁻¹=DihedralGroup.r 2) _ _

theorem sylowFlags_surjective : Function.Surjective sylowFlags := by
  intro a
  have h : ∀a:C2×C2,∃d:D8,dihedralFlags d=a := by decide +kernel
  obtain ⟨d,hd⟩ := h a
  exact ⟨pair (d,1),by simpa [sylowFlags,pair,turn_ne_one] using hd⟩

/-- The three lines of the actual quotient P/Q: rotations, even reflections,
and odd reflections in the difference of the dihedral coordinates. -/
def flagLine (i : Fin 3) : Subgroup (C2×C2) where
  carrier := {x | x=1 ∨ x=![ (1,turn),(turn,1),(turn,turn)] i}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have h : ∀i:Fin 3,∀a b:C2×C2,
      (a=1 ∨ a=![ (1,turn),(turn,1),(turn,turn)] i) →
      (b=1 ∨ b=![ (1,turn),(turn,1),(turn,turn)] i) →
      (a*b=1 ∨ a*b=![ (1,turn),(turn,1),(turn,turn)] i) := by decide +kernel
    intro a b ha hb
    exact h i a b ha hb
  inv_mem' := by revert i;decide +kernel

instance flagLine_decidable (i : Fin 3) : DecidablePred (·∈flagLine i) := fun x=>
  inferInstanceAs (Decidable (x=1 ∨ x=![ (1,turn),(turn,1),(turn,turn)] i))

def coreOvergroup (i : Fin 3) : Subgroup P := (flagLine i).comap sylowFlags

instance coreOvergroup_decidable (i : Fin 3) : DecidablePred (·∈coreOvergroup i) := fun x=>
  inferInstanceAs (Decidable (sylowFlags x∈flagLine i))

theorem card_coreOvergroup (i : Fin 3) : Nat.card (coreOvergroup i)=64 := by
  rw [Nat.card_eq_fintype_card]
  revert i
  decide +kernel

theorem core_le_coreOvergroup (i : Fin 3) : coreInP≤coreOvergroup i := by
  rw [←sylowFlags_ker]
  intro x hx
  change sylowFlags x∈flagLine i
  rw [show sylowFlags x=1 from hx]
  exact one_mem _

theorem coreOvergroup_distinct : Function.Injective coreOvergroup := by
  have hl : Function.Injective flagLine := by
    intro i j he
    have h : ∀i j:Fin 3,(∀x:C2×C2,x∈flagLine i ↔ x∈flagLine j)→i=j := by decide +kernel
    exact h i j (fun x=>he ▸ Iff.rfl)
  intro i j h
  apply hl
  exact comap_injective sylowFlags_surjective h

private theorem normalizerTest : ∀x:P,
    (∀a:QuaternionGroup 2,∃b:QuaternionGroup 2,
      x*quaternionEmbedding false a*x⁻¹=quaternionEmbedding false b) ↔
        sylowFlags x∈flagLine 0 := by
  decide +kernel

theorem normalizer_quaternion_left : normalizer ((quaternionEmbedding false).range:Set P)=coreOvergroup 0 := by
  ext x
  constructor
  · intro hx
    apply (normalizerTest x).mp
    intro a
    obtain ⟨b,hb⟩ := (mem_normalizer_iff.mp hx _).mp (show quaternionEmbedding false a∈(quaternionEmbedding false).range from ⟨a,rfl⟩)
    exact ⟨b,hb.symm⟩
  · intro hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨_,⟨a,rfl⟩,rfl⟩
      obtain ⟨b,hb⟩ := (normalizerTest x).mpr hx a
      exact ⟨b,hb.symm⟩
    · rw [card_map_of_injective (MulAut.conj x).injective]

private theorem map_elementary_flags (b : Bool) :
    (elementaryInP b b).map sylowFlags=flagLine (if b then 2 else 1) := by
  apply le_antisymm
  · rintro _ ⟨_,⟨⟨a,c⟩,⟨ha,hc⟩,rfl⟩,rfl⟩
    exact (by decide +kernel : ∀b:Bool,∀a c:D8,a∈plane b → c∈plane b →
      sylowFlags (pair (a,c))∈flagLine (if b then 2 else 1)) b a c ha hc
  · intro x hx
    change x=1 ∨ x=![ (1,turn),(turn,1),(turn,turn)] (if b then 2 else 1) at hx
    rcases hx with rfl|rfl
    · exact one_mem _
    · refine ⟨pair (DihedralGroup.sr (if b then 1 else 0),1),?_,?_⟩
      · refine ⟨(DihedralGroup.sr (if b then 1 else 0),1),?_,rfl⟩
        change DihedralGroup.sr (if b then 1 else 0)∈plane b ∧ (1:D8)∈plane b
        cases b <;> decide +kernel
      · cases b <;> decide +kernel

theorem elementary_sup_core (b : Bool) :
    elementaryInP b b⊔coreInP=coreOvergroup (if b then 2 else 1) := by
  rw [←sylowFlags_ker,←comap_map_eq,map_elementary_flags]
  rfl

theorem elementary_not_le_quaternion_normalizer (b : Bool) :
    ¬elementaryInP b b≤normalizer ((quaternionEmbedding false).range:Set P) := by
  intro h
  let a := pair (DihedralGroup.sr (if b then 1 else 0),1)
  have ha : a∈elementaryInP b b := by
    refine ⟨(DihedralGroup.sr (if b then 1 else 0),1),?_,rfl⟩
    change DihedralGroup.sr (if b then 1 else 0)∈plane b ∧ (1:D8)∈plane b
    cases b <;> decide +kernel
  have hx := h ha
  rw [normalizer_quaternion_left] at hx
  have hn : a∉coreOvergroup 0 := by cases b <;> decide +kernel
  exact hn hx
end SymmetricFourWreath
