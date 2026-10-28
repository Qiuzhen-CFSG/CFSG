module
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows.Linear
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.PrimeRankHom
/-! # Odd-prime rank in binary SL₂ and its two-kernel extensions
Every odd Sylow subgroup of binary SL₂ is cyclic by the faithful eigenline
argument. A two-group kernel has vanishing odd-prime rank, so the same rank-one
bound holds for any group mapping to SL₂ with such a kernel.
Source application: Aschbacher--Smith 2.5.6, printed p.554, excluding an
embedded binary rank-two component from the Levi factor of a parabolic.
-/
public section
open Subgroup Theory.GroupTheory
namespace Matrix.SL2
variable {F:Type*} [Field F] [Finite F] [CharP F 2]
theorem binary_odd_primeRank_le_one {p:ℕ} [Fact p.Prime] (ho:Odd p) :
    primeRank p (Matrix.SpecialLinearGroup (Fin 2) F)≤1 := by
  let P:=Classical.choice (inferInstance:Nonempty (Sylow p (Matrix.SpecialLinearGroup (Fin 2) F)))
  have hp2:p≠2:=fun h=>ho.not_two_dvd_nat (by rw [h])
  let : IsCyclic P:=odd_pGroup_isCyclic_of_injective P.isPGroup' hp2
    (P:Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).subtype
    (P:Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).subtype_injective
  exact P.primeRank_le_one_of_isCyclic inferInstance
theorem primeRank_le_one_of_two_kernel {D:Type*} [Group D] [Finite D]
    {p:ℕ} [Fact p.Prime] (ho:Odd p)
    (f:D→*Matrix.SpecialLinearGroup (Fin 2) F) (hk:IsPGroup 2 f.ker) : primeRank p D≤1 := by
  have hz:primeRank p f.ker=0:=by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    obtain ⟨m,hm⟩:=IsPGroup.iff_card.mp hk
    rw [hm]
    intro hd
    have hp2:p=2:=(Nat.prime_dvd_prime_iff_eq (Fact.out:p.Prime) Nat.prime_two).mp
      ((Fact.out:p.Prime).dvd_of_dvd_pow hd)
    exact ho.not_two_dvd_nat (by rw [hp2])
  have hr:=primeRank_le_ker_add (p:=p) f
  have hs:=Matrix.SL2.binary_odd_primeRank_le_one (F:=F) ho
  omega


end Matrix.SL2
