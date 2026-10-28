module
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.NormalForm
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Prime-power automorphisms of PSL₃ over a prime field

A p-element in three-dimensional matrices over characteristic p has pth power
one when p≥3: subtract the identity, use the dimension bound on nilpotence,
and apply the characteristic-p binomial identity. Sylow lifting gives the
same conclusion for PSL₃.

Over a prime field, the checked automorphism normal form has only linear
and graph factors. Odd order eliminates the graph factor, and p>5 eliminates
the diagonal factor of order dividing three. The automorphism is inner,
so the matrix bound applies. The source consumer uses this exponent bound
on a higher homocyclic primary subgroup, whose order-p plane consists of
pth powers.

Source: GLS3, Theorem2.5.12(a) and §2.7; the actual higher-primary
configuration in Aschbacher--Smith3.2.14, p.585, and13.1.4(5), p.867.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3.OddPrimeAutomorphisms
open Matrix.PSL3.OuterSolvable Matrix.PSL3.OddInvolutionFixed

private theorem matrix_prime_power_exponent {F : Type*} [Field F] {p : ℕ}
    [Fact p.Prime] [CharP F p] (hp : 3 ≤ p)
    (A : Matrix (Fin 3) (Fin 3) F) {m : ℕ} (ha : A^(p^m)=1) : A^p=1 := by
  let : CharP (Matrix (Fin 3) (Fin 3) F) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
      have h := congrArg (algebraMap F (Matrix (Fin 3) (Fin 3) F)) (CharP.cast_eq_zero F p)
      simpa only [map_natCast,map_zero] using h)
  have hn : (A-1)^(p^m)=0 := by
    rw [sub_pow_char_pow_of_commute p m (Commute.one_right A),ha,one_pow,sub_self]
  have hthree : (A-1)^3=0 := by
    apply Matrix.toLin'.injective
    rw [map_zero,Matrix.toLin'_pow]
    apply LinearMap.ext
    intro x
    have hh := Module.End.ker_pow_le_ker_pow_finrank (Matrix.toLin' (A-1)) (p^m)
    have hx : x ∈ LinearMap.ker ((Matrix.toLin' (A-1))^(p^m)) := by
      rw [← Matrix.toLin'_pow,hn,map_zero]
      simp
    simpa only [Module.finrank_fin_fun,LinearMap.mem_ker,LinearMap.zero_apply] using hh hx
  have hh := pow_eq_zero_of_le hp hthree
  rw [sub_pow_char_of_commute p (Commute.one_right A),one_pow] at hh
  exact sub_eq_zero.mp hh

private theorem psl_prime_power_exponent {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] [CharP F p] (hp : 3 ≤ p)
    (x : PSL(3,F)) {m : ℕ} (hx : x^(p^m)=1) : x^p=1 := by
  have hz : IsPGroup p (zpowers x) := IsPGroup.of_card_dvd_pow (n := m) (by
    simpa only [Nat.card_zpowers] using orderOf_dvd_of_pow_eq_one hx)
  obtain ⟨P,hP⟩ := hz.exists_le_sylow
  let q := QuotientGroup.mk' (center SL(3,F))
  obtain ⟨S,hS⟩ := Sylow.mapSurjective_surjective (QuotientGroup.mk'_surjective (center SL(3,F))) p P
  have hxP : x ∈ (S : Subgroup SL(3,F)).map q := by
    change x ∈ (S.mapSurjective (QuotientGroup.mk'_surjective (center SL(3,F))) : Subgroup PSL(3,F))
    rw [hS]
    exact hP (mem_zpowers x)
  obtain ⟨y,hy,he⟩ := hxP
  obtain ⟨k,hk⟩ := S.isPGroup' (⟨y,hy⟩ : S)
  have hym : (y : Matrix (Fin 3) (Fin 3) F)^(p^k)=1 := by
    exact congrArg (fun z : S => ((z : SL(3,F)) : Matrix (Fin 3) (Fin 3) F)) hk
  have hyp : y^p=1 := by
    apply Subtype.ext
    exact matrix_prime_power_exponent hp (y : Matrix (Fin 3) (Fin 3) F) hym
  rw [← he,← map_pow,hyp,map_one]

/-- Over an odd prime field of order p>5, every p-element of the actual
automorphism group of PSL₃ has pth power one. -/
theorem prime_power_exponent {F : Type*} [Field F] [Finite F]
    [IsSimpleGroup PSL(3,F)] [Group.IsPerfect SL(3,F)]
    {p : ℕ} [Fact p.Prime] (hp : 5 < p) (hF : Nat.card F = p)
    (a : MulAut PSL(3,F)) {m : ℕ} (ha : a^(p^m)=1) : a^p=1 := by
  have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  let : Group.IsPerfect PSL(3,F) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center SL(3,F))) (QuotientGroup.mk'_surjective _)
  have hns := Group.IsPerfect.not_isSolvable PSL(3,F)
  have hsquare : a^2 ∈ (linearConj F).range := by
    obtain ⟨g,hg | hg⟩ := automorphism_normal_form hns Fact.out ho hF a
    · exact ⟨g^2,by rw [map_pow,hg]⟩
    · refine ⟨g * inverseTransposeGL g,?_⟩
      rw [map_mul,hg,pow_two]
      have hh := Matrix.PSL3.OddInvolutionFixed.graph_linearConj g
      calc
        linearConj F g * linearConj F (inverseTransposeGL g) =
            linearConj F g * linearConj F (inverseTransposeGL g) * (graph F)^2 := by rw [graph_sq,mul_one]
        _ = (linearConj F g * graph F) * (linearConj F g * graph F) := by
          rw [pow_two]
          calc
            _ = linearConj F g * (linearConj F (inverseTransposeGL g) * graph F) * graph F := by group
            _ = _ := by rw [← hh]; group
  have hlin : a ∈ (linearConj F).range := (zpowers_le.mpr hsquare)
    (mem_zpowers_pow_iff.mpr ((Nat.coprime_two_left.mpr ho.pow).of_dvd_right
      (orderOf_dvd_of_pow_eq_one ha)))
  obtain ⟨b,hb⟩ := hlin
  have hc : a^3 ∈ MulAut.innerSubgroup PSL(3,F) := hb ▸ linearConj_cube_inner b
  have hcop : Nat.Coprime 3 (p^m) :=
    (Nat.coprime_comm.mpr ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by
      intro hd
      have := Nat.le_of_dvd (by decide : 0 < 3) hd
      omega))).pow_right m
  have hi : a ∈ MulAut.innerSubgroup PSL(3,F) := (zpowers_le.mpr hc)
    (mem_zpowers_pow_iff.mpr (hcop.of_dvd_right (orderOf_dvd_of_pow_eq_one ha)))
  obtain ⟨x,hx⟩ := hi
  have hcenter : center PSL(3,F) = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)
  have hxpow : x^(p^m)=1 := by
    apply MulAut.conj_injective_of_center_eq_bot hcenter
    rw [map_pow,hx,ha,map_one]
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime (by simpa only [← Nat.card_eq_fintype_card] using hF)
  rw [← hx,← map_pow,psl_prime_power_exponent (by omega) x hxpow,map_one]


end Matrix.PSL3.OddPrimeAutomorphisms
