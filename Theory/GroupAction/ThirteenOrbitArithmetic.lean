module
public import Theory.GroupAction.InvariantFiberCard

/-!
# The residual orbit arithmetic at thirteen

If each orbit has size divisible by thirteen or has size300,600,1200, an
invariant set has size13m+300k. Such a set cannot have353 points. Applied
after deleting the fixed point and two hypothetical975-point orbits from
2304 points, this proves the uniqueness required by source J.5.5(5).
-/

public noncomputable section
open scoped BigOperators
namespace MulAction
variable {K Ω:Type*} [Group K] [MulAction K Ω] [Finite Ω]

private theorem sum_decomposition {I:Type*} (T:Finset I) (d:I→ℕ)
    (hd:∀i∈T,13∣d i ∨ d i=300 ∨ d i=600 ∨ d i=1200) :
    ∃m k:ℕ,∑i∈T,d i=13*m+300*k := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0,0,by simp⟩
  | @insert i T hi ih =>
    obtain ⟨m,k,h⟩:=ih (fun j hj=>hd j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert hi,h]
    rcases hd i (Finset.mem_insert_self i T) with ⟨n,hn⟩|hn|hn|hn
    · exact ⟨m+n,k,by omega⟩
    · exact ⟨m,k+1,by omega⟩
    · exact ⟨m,k+2,by omega⟩
    · exact ⟨m,k+4,by omega⟩

/-- The corrected thirteen-overgroup alternatives forbid a residual353-point invariant set. -/
theorem invariant_card_ne_353 (S:Set Ω) (hS:∀k:K,∀x∈S,k•x∈S)
    (horbit:∀x∈S,13∣Nat.card (orbit K x) ∨ Nat.card (orbit K x)=300 ∨
      Nat.card (orbit K x)=600 ∨ Nat.card (orbit K x)=1200) : Nat.card S≠353 := by
  classical
  let I:=orbitRel.Quotient K Ω
  let : Fintype I:=Fintype.ofFinite I
  let f:Ω→I:=Quotient.mk''
  let d:I→ℕ:=fun i=>Nat.card i.orbit
  have ht:∀x y,f x=f y→∃k:K,k•x=y:=by
    intro x y he
    exact Quotient.exact he.symm
  have hc (i:I):Nat.card {x:Ω // f x=i}=d i:=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x=>orbitRel.Quotient.mem_orbit.symm))
  obtain ⟨T,hT,hcard⟩:=invariant_set_fiber_sum f ht S hS d hc
  have hd:∀i∈T,13∣d i ∨ d i=300 ∨ d i=600 ∨ d i=1200:=by
    intro i hi
    have he:f i.out=i:=Quotient.out_eq' i
    have hx:i.out∈S:=(hT i.out).mpr (he.symm ▸ hi)
    have ho:=horbit i.out hx
    have hio:i.orbit=orbit K i.out:=orbitRel.Quotient.orbit_eq_orbit_out i Quotient.out_eq'
    change 13∣Nat.card i.orbit ∨ Nat.card i.orbit=300 ∨ Nat.card i.orbit=600 ∨ Nat.card i.orbit=1200
    rwa [hio]
  obtain ⟨m,k,hm⟩:=sum_decomposition T d hd
  rw [hcard,hm]
  omega
end MulAction
