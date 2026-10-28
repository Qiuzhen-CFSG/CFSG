module

public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.FinCases

/-!
# Odd torsion in a split involution centralizer of PSL₄

The determinant-one diagonal torus centralizes diag(-1,-1,1,1). Its
p-torsion has three independent parameters whenever p divides |F|-1.
For odd p it embeds in the projective quotient: a scalar in the kernel
has order dividing both p and four, hence is trivial. The torus itself
is not claimed to embed after quotienting by scalars.

The displayed involution is nonidentity when -1 ≠ 1 in F. Together
these calculations supply the linear torus obstruction in Aschbacher–Smith,
*The Classification of Quasithin Groups*, A.2.17, printed p.39.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups
namespace Matrix.PSL4.OddSplitTorus
variable (F : Type*) [Field F]

def torusFour (a : Fin 3 → Fˣ) : SL(4,F) :=
  ⟨diagonal ![(a 0 : F), (a 1 : F), (a 2 : F), ↑(a 0 * a 1 * a 2)⁻¹], by
    simp [det_diagonal, Fin.prod_univ_succ, ← Units.val_mul, ← mul_assoc]⟩

def torusFourHom : (Fin 3 → Fˣ) →* SL(4,F) where
  toFun := torusFour F
  map_one' := by apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;>
    simp [torusFour]
  map_mul' a b := by
    apply Subtype.ext
    change diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]

def splitInvolution : PSL(4,F) :=
  QuotientGroup.mk' _ (torusFour F ![-1,-1,1])

theorem splitInvolution_ne_one (hodd : (-1 : F) ≠ 1) : splitInvolution F ≠ 1 := by
  intro h
  have hc := (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  have h0 := congrArg (fun m : Matrix (Fin 4) (Fin 4) F => m 0 0) hr
  have h2 := congrArg (fun m : Matrix (Fin 4) (Fin 4) F => m 2 2) hr
  apply hodd
  exact h0.symm.trans h2

theorem splitInvolution_sq : splitInvolution F ^ 2 = 1 := by
  have hs : (torusFour F ![-1,-1,1]) ^ 2 = 1 := by
    change (torusFourHom F ![-1,-1,1]) ^ 2 = 1
    rw [← map_pow]
    have hp : (![-1,-1,1] : Fin 3 → Fˣ) ^ 2 = 1 := by
      ext i
      fin_cases i <;> simp
    rw [hp, map_one]
  rw [splitInvolution, ← map_pow, hs, map_one]

def torusFourCentralizer : (Fin 3 → Fˣ) →* Subgroup.centralizer ({splitInvolution F} : Set PSL(4,F)) :=
  ((QuotientGroup.mk' _).comp (torusFourHom F)).codRestrict _ fun a => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    change QuotientGroup.mk' _ (torusFourHom F a) * QuotientGroup.mk' _ (torusFourHom F ![-1,-1,1]) =
      QuotientGroup.mk' _ (torusFourHom F ![-1,-1,1]) * QuotientGroup.mk' _ (torusFourHom F a)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm a]

def torsionFour (p : ℕ) : (Fin 3 → rootsOfUnity p F) →*
    Subgroup.centralizer ({splitInvolution F} : Set PSL(4,F)) :=
  (torusFourCentralizer F).comp
    { toFun := fun a i => (a i).val, map_one' := rfl, map_mul' := fun _ _ => rfl }

theorem torsionFour_injective {p : ℕ} (hp : p.Prime) (ho : p ≠ 2) :
    Function.Injective (torsionFour F p) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  have hh : QuotientGroup.mk' _ (torusFour F (fun i => (a i).val)) = 1 := congrArg Subtype.val ha
  have hc := (QuotientGroup.eq_one_iff _).mp hh
  obtain ⟨r, hr, he⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  have hcoord (i : Fin 3) : r = ((a i).val : F) := by
    have h := congrArg (fun m : Matrix (Fin 4) (Fin 4) F => m i.castSucc i.castSucc) he
    fin_cases i <;> exact h
  have hfour : (a 0).val ^ 4 = 1 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, Fintype.card_fin, hcoord 0] using hr
  have hpw : (a 0).val ^ p = 1 := (mem_rootsOfUnity p _).mp (a 0).property
  have hone : (a 0).val = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpw) (orderOf_dvd_of_pow_eq_one hfour)
    have hg : Nat.Coprime p 4 := by
      have h2 : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr
        (fun h => ho ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
      exact h2.pow_right 2
    simpa only [hg.gcd_eq_one] using hd
  have hrone : r = 1 := (hcoord 0).trans (congrArg Units.val hone)
  funext i
  apply Subtype.ext
  apply Units.ext
  exact (hcoord i).symm.trans hrone

theorem three_le_primeRank_torus [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : p ≠ 2) (hd : p ∣ Nat.card F - 1) :
    3 ≤ primeRank p (Subgroup.centralizer ({splitInvolution F} : Set PSL(4,F))) := by
  have hp : p.Prime := Fact.out
  let : NeZero p := ⟨hp.ne_zero⟩
  have hdu : p ∣ Nat.card Fˣ := by simpa only [Nat.card_units] using hd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hdu
  have hroot : IsPrimitiveRoot u p := hu ▸ IsPrimitiveRoot.orderOf u
  have hc : Nat.card (rootsOfUnity p F) = p := hroot.card_rootsOfUnity'
  refine primeRank_ge_of_elementary_embedding (A := Fin 3 → rootsOfUnity p F)
    ?_ ?_ (torsionFour F p) (torsionFour_injective F hp ho)
  · intro a
    funext i
    exact Subtype.ext ((mem_rootsOfUnity p _).mp (a i).property)
  · rw [Nat.card_fun, hc, Nat.card_fin]
end Matrix.PSL4.OddSplitTorus
