module
public import Theory.SpecificGroups.PSL2.OddSylowFixers
public import Theory.GroupTheory.SpecificGroups.DihedralAut
public import Theory.FieldTheory.FiniteAutomorphismOrder
public import GorensteinWalter.PSL2Cardinality
/-!
# The actual PSL₂(25) Sylow stabilizer is a two-group

A full PSL₂(25) Sylow is D₈, whose automorphism group is a two-group. An
automorphism stabilizing it therefore has a two-power with pointwise-trivial
Sylow action. Semilinear coverage shows its square is projective linear;
the PGL₂ Sylow-fixer theorem makes that square inner by a Sylow element.
The coefficient field automorphism has order two. Thus the original
stabilizer is a two-group, on the literal automorphism carrier.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup GorensteinWalter
open scoped MatrixGroups Pointwise
namespace Theory.SpecificGroups.Classical.SylowMarkedSL2
variable {F : Type*} [Field F] [Finite F]
theorem psl25_sylow_stabilizer_isPGroup (hF : Nat.card F = 25)
    (S : Sylow 2 PSL(2,F)) :
    IsPGroup 2 (MulAction.stabilizer (MulAut PSL(2,F)) (S : Subgroup PSL(2,F))) := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ho : IsOddPrimePower (Nat.card F) := ⟨5,2,by decide,by decide,by decide,by simpa using hF⟩
  have hlarge : 3 < Nat.card F := by omega
  have hS : Nat.card S = 8 := by
    rw [Sylow.card_eq_multiplicity,psl2_card_formula F ho,hF]
    decide +kernel
  obtain ⟨m,hm,⟨eS⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F ho S
  have hm4 : 2 ^ m = 4 := by
    have he := Nat.card_congr eS.toEquiv
    rw [hS,DihedralGroup.nat_card] at he
    omega
  have hD := S.isPGroup'.of_surjective eS.toMonoidHom eS.surjective
  have hA : IsPGroup 2 (MulAut S) :=
    (DihedralGroup.isPGroup_mulAut_of_two_lt (by omega) hD).of_injective
      (MulAut.congr eS).toMonoidHom (MulAut.congr eS).injective
  let H := MulAction.stabilizer (MulAut PSL(2,F)) (S : Subgroup PSL(2,F))
  let r : H →* MulAut S :=
    { toFun := fun a => (a.val.subgroupMap (S : Subgroup PSL(2,F))).trans (MulEquiv.subgroupCongr a.property)
      map_one' := by ext x; rfl
      map_mul' := by intro a b; ext x; rfl }
  intro a
  obtain ⟨n,hn⟩ := hA (r a)
  let b := a.val ^ (2 ^ n)
  have hb (t : PSL(2,F)) (ht : t ∈ S) : b t = t := by
    have he : r (a ^ (2 ^ n)) = 1 := (map_pow r a (2^n)).trans hn
    exact congrArg (fun c : MulAut S => (c ⟨t,ht⟩).val) he
  obtain ⟨x,hx⟩ := pGammaL2ToMulAutPSL2_surjective F (p := 5) (f := 2)
    (by simpa using hF) ho hlarge b
  have hσ : x.right ^ 2 = 1 := FiniteField.ringAut_sq_of_card_prime_pow
    (by decide : Nat.Prime 5) (by decide : 2 ≤ 2) (by simpa using hF) x.right
  have hx2 : x ^ 2 = SemidirectProduct.inl ((x ^ 2).left) := by
    apply SemidirectProduct.ext
    · rfl
    · simpa [pow_two] using hσ
  have hpgl : pgl2InnerAutPSL2 F ho hlarge ((x^2).left) = b ^ 2 := by
    rw [← pGammaL2ToMulAutPSL2_inl,← hx2,map_pow,hx]
  have hb2 (t : PSL(2,F)) (ht : t ∈ S) : (b ^ 2) t = t := by
    change b (b t) = t
    rw [hb t ht,hb t ht]
  obtain ⟨s,hs,he⟩ := Theory.PSL2.odd_pgl_sylow_fixed_inner ho hlarge S (b^2) hb2 ((x^2).left) hpgl
  obtain ⟨k,hk⟩ := S.isPGroup' (⟨s,hs⟩ : S)
  have hsk : s ^ (2^k) = 1 := congrArg Subtype.val hk
  refine ⟨n + (k+1),?_⟩
  apply Subtype.ext
  change a.val ^ (2 ^ (n+(k+1))) = 1
  rw [Nat.pow_add,pow_mul]
  change b ^ (2 ^ (k+1)) = 1
  calc
    _ = (b ^ 2) ^ (2^k) := by
      calc
        b ^ (2 ^ (k+1)) = b ^ (2 * 2^k) := by rw [Nat.pow_succ, Nat.mul_comm (2^k) 2]
        _ = (b ^ 2) ^ (2^k) := pow_mul b 2 (2^k)
    _ = (MulAut.conj s) ^ (2^k) := by rw [he]
    _ = 1 := by rw [← map_pow,hsk,map_one]
end Theory.SpecificGroups.Classical.SylowMarkedSL2
