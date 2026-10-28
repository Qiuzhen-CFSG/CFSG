module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.QuotientShape
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupAction.CoprimeCharacteristicRestriction
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Mathlib.Algebra.Ring.GeomSum

/-!
# The natural-extension row of the Cartan component sieve

In A.3.6(3), the characteristic generalized Fitting subgroup is an
actual elementary abelian plane of order p² and the quotient is SL₂(p).
Every prime dividing GL₂(p) divides SL₂(p), so a coprime automorphism
fixes the plane. Self-centralization and the prime-group restriction
kernel then make it trivial on the whole group.

The application to the original component image is in `Sieve.Noncentral`.
Only the nilpotent-Fitting A.3.6 row remains there; its discharge and the
source 11.5.6 assembly stay with qt-d-1222-natural-closure-cartan.
Source: Aschbacher--Smith A.3.6(3), pp.43--45, and 11.5.6(3), pp.780--781.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02



namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear
/-- A natural A.3.6 group has no nontrivial coprime automorphism. -/
theorem natural_coprime_actor_eq_one {Q : Type*} [Group Q] [Finite Q]
    (hn : A36Natural Q) (a : MulAut Q)
    (hc : Nat.Coprime (orderOf a) (Nat.card Q)) : a = 1 := by
  obtain ⟨p,hp,hp3,hact⟩ := hn.2
  let : Fact p.Prime := ⟨hp⟩
  let N := generalizedFitting Q
  let : N.Characteristic := by
    change (generalizedFitting Q).Characteristic
    rw [hn.1]
    infer_instance
  obtain ⟨hel,hcard⟩ := CFSG.Quasithin.Chapter1.RadicalStructure.natural_elementary hact
  let : IsElementaryAbelian p N := hel
  have hpN : IsPGroup p N := IsPGroup.of_card hcard
  obtain ⟨F,_,_,hF,v,ρ,_⟩ := hact
  have hsl : Nat.card (Q ⧸ N) = p * (p ^ 2 - 1) := by
    rw [Nat.card_congr ρ.toEquiv, Atlas.card_sl_two, hF]
  have hcop : Nat.Coprime (orderOf a) (p * (p ^ 2 - 1)) := by
    rw [← hsl]
    exact hc.of_dvd_right N.card_quotient_dvd_card
  have hpredDvd : p - 1 ∣ p ^ 2 - 1 := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow p 1 2
  have hpred : Nat.Coprime (orderOf a) (p - 1) :=
    hcop.of_dvd_right (hpredDvd.trans (dvd_mul_left (p ^ 2 - 1) p))
  have hgl : Nat.Coprime (orderOf a)
      (Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) := by
    rw [Matrix.card_GL_field]
    simp only [ZMod.card, Fin.prod_univ_two, Fin.val_zero, Fin.val_one,
      pow_zero, pow_one]
    have hsub : p ^ 2 - p = p * (p - 1) := by
      rw [pow_two, Nat.mul_sub_left_distrib, mul_one]
    rw [hsub]
    exact (hcop.of_dvd_right (dvd_mul_left _ _)).mul_right
      ((hcop.of_dvd_right (dvd_mul_right _ _)).mul_right hpred)
  obtain ⟨f,hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := p) (n := 2) N hcard.le
  apply MulAut.eq_one_of_coprime_characteristic_restriction N hpN
    (centralizer_generalizedFitting_le Q) a
    (hcop.of_dvd_right (dvd_mul_right _ _))
  exact hgl.of_dvd_right (Subgroup.card_dvd_of_injective f hf)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear
