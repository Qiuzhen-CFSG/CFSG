module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularLastSuzukiLinearBraid
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.TorusActions

/-!
# Torus extension of the last pure Suzuki-linear seed

The two independent simple-root characters move the parameter-one commutator
to every nonzero pair of field parameters. Their checked native weights give
all six factors, including the Suzuki inverse correction and the middle
central coefficient. Zero parameters follow from the local root laws.

Source: Fong--Seitz II, Section 10, (10.27)--(10.41); GLS3 Table 2.4.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition
open ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)
local notation "L" i:max a:max => synchronizedPositivePoint Q split c (Sum.inl i) a
local notation "S" i:max a:max b:max => synchronizedPositivePoint Q split c (Sum.inr i) (a,b)

private theorem power_tits (x : CoefficientField m) : x^(2*2^m) = titsEnd m x := by
  rw [titsEnd_apply,pow_succ]
  congr 1
  exact Nat.mul_comm _ _

private theorem power_twice_tits (x : CoefficientField m) :
    x^(4*2^m) = (titsEnd m x)^2 := by
  rw [←power_tits,←pow_mul]
  congr 1
  omega

/-- Independent simple-root characters extend the one checked seed. -/
theorem synchronized_last_main_commutator_of_seed
    (hseed : (L 0 1)⁻¹ * (S 0 1 0)⁻¹ * L 0 1 * S 0 1 0 =
      S 2 1 1 * L 2 1 * S 1 0 1 * L 3 1 * S 3 1 0 * L 1 1)
    (a x : CoefficientField m) :
    (L 0 x)⁻¹ * (S 0 a 0)⁻¹ * L 0 x * S 0 a 0 =
      S 2 (a*x) (titsEnd m (a*x)*(a*x)) *
        L 2 ((a^2*titsEnd m a)*(x*titsEnd m x)) *
        S 1 0 ((a^3*(titsEnd m a)^2)*(x^2*titsEnd m x)) *
        L 3 ((a^2*(titsEnd m a)^2)*(x*titsEnd m x)) *
        S 3 ((a*titsEnd m a)*x) 0 * L 1 ((a^2*titsEnd m a)*x) := by
  by_cases ha : a = 0
  · subst a
    simp
  by_cases hx : x = 0
  · subst x
    simp
  let t : TorusParameter m := (Units.mk0 x hx,Units.mk0 a ha)
  let H := normalizedSynchronizedTorus Q split c t
  have hp (i : Fin 4) (z : CoefficientField m) :
      MulAut.conj H (L i z) =
        L i ((TorusCharts.character t (.inl i) : CoefficientField m)*z) :=
    normalizedSynchronizedTorus_pair Q split c t i z
  have hq (i : Fin 4) (z v : CoefficientField m) :
      MulAut.conj H (S i z v) =
        S i ((TorusCharts.character t (.inr i) : CoefficientField m)*z)
          ((TorusCharts.character t (.inr i) : CoefficientField m)*
            titsEnd m (TorusCharts.character t (.inr i))*v) :=
    normalizedSynchronizedTorus_quartet Q split c t i z v
  have wp (i : Fin 4) : (TorusCharts.character t (.inl i) : CoefficientField m) =
      ![x,(a^2*titsEnd m a)*x,(a^2*titsEnd m a)*(x*titsEnd m x),
        (a^2*(titsEnd m a)^2)*(x*titsEnd m x)] i := by
    rw [TorusCharts.character_pair]
    fin_cases i <;> simp [t,pow_add,power_tits,power_twice_tits]
    all_goals ring
  have wq (i : Fin 4) : (TorusCharts.character t (.inr i) : CoefficientField m) =
      ![a,titsEnd m x*(a*titsEnd m a),a*x,(a*titsEnd m a)*x] i := by
    rw [TorusCharts.character_quartet]
    fin_cases i <;> simp [t,pow_add,power_tits]
    all_goals ring
  have hp0 : MulAut.conj H (L 0 1) = L 0 x := by
    rw [hp,wp]; simp only [Matrix.cons_val_zero,mul_one]
  have hp1 : MulAut.conj H (L 1 1) = L 1 ((a^2*titsEnd m a)*x) := by
    rw [hp,wp]; simp only [Matrix.cons_val,mul_one]
  have hp2 : MulAut.conj H (L 2 1) = L 2 ((a^2*titsEnd m a)*(x*titsEnd m x)) := by
    rw [hp,wp]; simp only [Matrix.cons_val,mul_one]
  have hp3 : MulAut.conj H (L 3 1) = L 3 ((a^2*(titsEnd m a)^2)*(x*titsEnd m x)) := by
    rw [hp,wp]; simp only [Matrix.cons_val,mul_one]
  have hq0 : MulAut.conj H (S 0 1 0) = S 0 a 0 := by
    rw [hq,wq]; simp only [Matrix.cons_val,mul_one,mul_zero]
  have hq2 : MulAut.conj H (S 2 1 1) = S 2 (a*x) (titsEnd m (a*x)*(a*x)) := by
    rw [hq,wq]; simp only [Matrix.cons_val,mul_one]
    rw [mul_comm (a*x)]
  have hq3 : MulAut.conj H (S 3 1 0) = S 3 ((a*titsEnd m a)*x) 0 := by
    rw [hq,wq]; simp only [Matrix.cons_val,mul_one,mul_zero]
  have hq1 : MulAut.conj H (S 1 0 1) =
      S 1 0 ((a^3*(titsEnd m a)^2)*(x^2*titsEnd m x)) := by
    rw [hq,wq]; simp only [Matrix.cons_val,mul_one,mul_zero,map_mul,titsEnd_twice]
    congr 1
    ring
  have h := congrArg (MulAut.conj H) hseed
  simpa only [map_mul,map_inv,hp0,hp1,hp2,hp3,hq0,hq1,hq2,hq3] using h

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
