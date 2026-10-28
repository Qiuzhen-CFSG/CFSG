module
public import Theory.Representation.SpecialLinearNatural
public import Theory.GroupTheory.CoprimeSubgroupLift
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic.ReduceModChar

/-!
# A literal binary Singer projector

The polynomial 1+X³+X⁵+X⁶ vanishes on the fixed and natural Singer
factors and is idempotent on every operator of exponent seven. All actor
and coefficient conventions are explicit; no composition count is used.
-/
public noncomputable section
open Matrix Polynomial
open scoped MatrixGroups
namespace BinarySingerPrimary

/-- The synchronized natural Singer, with polynomial X³+X+1. -/
@[expose] def singer : SL(3,ZMod 2) := ⟨!![0,1,0;0,0,1;1,1,0],by decide⟩

/-- The literal complementary projector polynomial. -/
@[expose] def polynomial : Polynomial (ZMod 2) := 1+X^3+X^5+X^6

/-- The corresponding operator on an arbitrary binary vector space. -/
@[expose] def projector {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (a : Module.End (ZMod 2) M) : Module.End (ZMod 2) M := 1+a^3+a^5+a^6

theorem projector_aeval {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (a : Module.End (ZMod 2) M) : projector a=aeval a polynomial := by
  simp only [projector,polynomial,map_add,map_pow,map_one,aeval_X]

/-- Polynomial evaluation respects a specified intertwining map. -/
theorem projector_intertwine
    {M N : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [AddCommGroup N] [Module (ZMod 2) N]
    (f : M →ₗ[ZMod 2] N) (a : Module.End (ZMod 2) M) (b : Module.End (ZMod 2) N)
    (h : ∀ x, f (a x)=b (f x)) (x : M) :
    f (projector a x)=projector b (f x) := by
  have hp (n : ℕ) (x : M) : f ((a^n) x)=(b^n) (f x) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [pow_succ',Module.End.mul_apply]
      rw [h,ih]
  simp only [projector,LinearMap.add_apply,Module.End.one_apply,map_add,hp]

theorem projector_idempotent {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (a : Module.End (ZMod 2) M) (ha : a^7=1) : projector a*projector a=projector a := by
  have hp : polynomial^2-polynomial=(X^7-1)*(X^5+X^3) := by
    dsimp [polynomial]
    ring_nf
    reduce_mod_char
  have he := congrArg (aeval a) hp
  simp only [map_sub,map_pow,map_mul,map_add,map_one,aeval_X,ha,sub_self,zero_mul] at he
  rw [←projector_aeval,pow_two] at he
  exact sub_eq_zero.mp he

theorem singer_pow : singer^7=1 := by decide +kernel

theorem singer_ne_one : singer≠1 := by decide +kernel

theorem singer_projector_natural :
    projector (Representation.specialLinearNatural (k := ZMod 2) 3 singer)=0 := by
  apply LinearMap.ext
  exact (by decide +kernel : ∀ x : Fin 3 → ZMod 2,
    projector (Representation.specialLinearNatural (k := ZMod 2) 3 singer) x=0)

/-- A genuine order-seven lift with exactly the specified original image. -/
theorem exists_order_seven_lift {L : Type*} [Group L] [Finite L]
    (a : L →* SL(3,ZMod 2)) (ha : Function.Surjective a)
    (hk : IsPGroup 2 a.ker) :
    ∃ s : L, a s=singer ∧ s^7=1 ∧ orderOf s=7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let T := Subgroup.zpowers singer
  have hT : Nat.card T=7 := (Nat.card_zpowers singer).trans
    (orderOf_eq_prime singer_pow singer_ne_one)
  have hcop : Nat.Coprime (Nat.card a.ker) (Nat.card T) := by
    rw [hT]
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 7).pow_left n
  obtain ⟨f,hf⟩ := a.exists_subgroup_section_of_coprime_kernel ha T hcop
  let x : T := ⟨singer,Subgroup.mem_zpowers singer⟩
  have hx : a (f x)=singer := congrArg (fun b : T →* SL(3,ZMod 2) => b x) hf
  have hx7 : x^7=1 := Subtype.ext singer_pow
  have hs7 : (f x)^7=1 := by rw [←map_pow,hx7,map_one]
  exact ⟨f x,hx,hs7,orderOf_eq_prime hs7 (fun h => singer_ne_one (hx.symm.trans (h ▸ map_one a)))⟩

/-- Cardinality form of injection through a marked section: the projector
image lifts through f and its intersection with ker(q) is killed. -/
theorem card_range_le_of_section
    {M S Y : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [Group S] [Group Y] [Finite Y]
    (e : Module.End (ZMod 2) M) (he : e*e=e)
    (f : S →* Multiplicative M) (q : S →* Y)
    (hlift : ∀ x : e.range, ∃ s : S, (f s).toAdd=x.val)
    (hkill : ∀ s : S, q s=1 → e (f s).toAdd=0) :
    Nat.card e.range ≤ Nat.card Y := by
  classical
  choose lift hlift using hlift
  let j : e.range → Y := fun x => q (lift x)
  apply Nat.card_le_card_of_injective j
  intro x y hxy
  have hk : q (lift x*(lift y)⁻¹)=1 := by
    rw [map_mul,map_inv,show q (lift x)=q (lift y) from hxy,mul_inv_cancel]
  have hz := hkill _ hk
  have hx : e x.val=x.val := by
    obtain ⟨v,hv⟩ := x.property
    rw [←hv]
    exact LinearMap.congr_fun he v
  have hy : e y.val=y.val := by
    obtain ⟨v,hv⟩ := y.property
    rw [←hv]
    exact LinearMap.congr_fun he v
  change e (f (lift x*(lift y)⁻¹)).toAdd=0 at hz
  rw [map_mul,map_inv] at hz
  change e ((f (lift x)).toAdd+ -(f (lift y)).toAdd)=0 at hz
  rw [←sub_eq_add_neg] at hz
  rw [hlift,hlift,map_sub,hx,hy] at hz
  exact Subtype.ext (sub_eq_zero.mp hz)

/-- The same literal Singer on the endpoint hyperplane. -/
@[expose] def endpointSinger : SL(4,ZMod 2) :=
  ⟨!![1,0,0,0;0,0,1,0;0,0,0,1;0,1,1,0],by decide⟩

theorem endpointSinger_pow : endpointSinger^7=1 := by decide +kernel

theorem endpointSinger_ne_one : endpointSinger≠1 := by decide +kernel

theorem endpointSinger_projector_natural :
    projector (Representation.specialLinearNatural (k := ZMod 2) 4 endpointSinger)=0 := by
  apply LinearMap.ext
  exact (by decide +kernel : ∀ x : Fin 4 → ZMod 2,
    projector (Representation.specialLinearNatural (k := ZMod 2) 4 endpointSinger) x=0)

/-- Lift any specified seven-element through its original two-group kernel. -/
theorem exists_seven_lift {L B : Type*} [Group L] [Finite L] [Group B]
    (a : L →* B) (ha : Function.Surjective a) (hk : IsPGroup 2 a.ker)
    (y : B) (hy : y^7=1) (hy1 : y≠1) :
    ∃ s : L, a s=y ∧ s^7=1 ∧ orderOf s=7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let T := Subgroup.zpowers y
  have hT : Nat.card T=7 := (Nat.card_zpowers y).trans (orderOf_eq_prime hy hy1)
  have hcop : Nat.Coprime (Nat.card a.ker) (Nat.card T) := by
    rw [hT]
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 7).pow_left n
  obtain ⟨f,hf⟩ := a.exists_subgroup_section_of_coprime_kernel ha T hcop
  let x : T := ⟨y,Subgroup.mem_zpowers y⟩
  have hx : a (f x)=y := congrArg (fun b : T →* B => b x) hf
  have hx7 : x^7=1 := Subtype.ext hy
  have hs7 : (f x)^7=1 := by rw [←map_pow,hx7,map_one]
  exact ⟨f x,hx,hs7,orderOf_eq_prime hs7 (fun h => hy1 (hx.symm.trans (h ▸ map_one a)))⟩

/-- The literal cubic X³+X+1 evaluated on a binary endomorphism. -/
@[expose] def cubic {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (a : Module.End (ZMod 2) M) : Module.End (ZMod 2) M := a^3+a+1

theorem cubic_aeval {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (a : Module.End (ZMod 2) M) :
    cubic a=aeval a ((X^3+X+1 : Polynomial (ZMod 2))) := by
  simp only [cubic,map_add,map_pow,map_one,aeval_X]

/-- With the inverse-left convention, the kernel of X³+X+1 for the
right actor lies in the complementary projector image for the left actor.
The identity uses the specified actors, without a natural/dual label. -/
theorem inverse_cubic_kernel_le_projector_range
    {A M : Type*} [Group A] [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) A M) (s : A) :
    LinearMap.ker (cubic (ρ (s⁻¹))) ≤
      (projector (ρ s)).range := by
  have h3 : s^6*(s⁻¹)^3=s^3 := by group
  have h5 : s^6*s⁻¹=s^5 := by group
  have he : projector (ρ s)=1+ρ (s^6)*
      cubic (ρ (s⁻¹)) := by
    simp only [cubic,mul_add,mul_one]
    rw [←map_pow ρ (s⁻¹) 3,←map_mul ρ (s^6) ((s⁻¹)^3),h3,
      ←map_mul ρ (s^6) (s⁻¹),h5]
    simp only [map_pow,projector,add_assoc]
  intro x hx
  refine ⟨x,?_⟩
  rw [he,LinearMap.add_apply,Module.End.one_apply,Module.End.mul_apply,
    LinearMap.mem_ker.mp hx,map_zero,add_zero]

end BinarySingerPrimary
