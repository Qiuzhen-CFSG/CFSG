module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.FittingActions
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupAction.CoprimePrimaryDetection

/-!
# Detecting the surviving action on a nilpotent primary plane

A coprime automorphism of the nilpotent-Fitting A.3.6 group is detected on
an actual O_p/Frattini quotient. The full-core/omega comparison identifies
this quotient as an elementary plane without restricting the homocyclic
exponent or excluding extraspecial cores. The prime five cannot detect
such an actor: GL₂(5) has no prime divisor outside the SL₂(5) quotient.
Thus a moved plane has prime greater than five.

The automorphism and the component conjugation action use the literal
prime-core inclusion and Frattini quotient. Their conjugation identity
prepares the scalar-action reduction. This does not exclude the remaining
ambient action or assert source 11.5.6(3).
Source: Aschbacher--Smith A.3.6(4), pp.43--45, and 11.5.6(3), pp.780--781.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.RadicalActions

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear

/-- The canonical automorphism action on the full prime-core Frattini quotient. -/
def primaryFrattiniAut (p : ℕ) (Q : Type*) [Group Q] :
    MulAut Q →* MulAut (pCore p Q ⧸ frattini (pCore p Q)) :=
  (quotientAut (frattini (pCore p Q))).comp (MulAut.characteristic (pCore p Q))

/-- The two actual actions satisfy the original conjugation identity. -/
theorem primaryFrattiniAut_conjugation {Q : Type*} [Group Q]
    (p : ℕ) (a : MulAut Q) (g : Q) :
    primaryFrattiniAut p Q a * FittingActions.coreFrattiniAction p Q g *
      (primaryFrattiniAut p Q a)⁻¹ = FittingActions.coreFrattiniAction p Q (a g) := by
  change primaryFrattiniAut p Q a * primaryFrattiniAut p Q (MulAut.conj g) *
      (primaryFrattiniAut p Q a)⁻¹ = primaryFrattiniAut p Q (MulAut.conj (a g))
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  rw [MulAut.apply_inv_self]

/-- Both permitted primary shapes have an elementary Frattini plane. -/
theorem nilpotent_primary_frattini_shape {Q : Type*} [Group Q] [Finite Q]
    (hn : A36Nilpotent Q) {p : ℕ} [Fact p.Prime]
    (hd : p ∣ Nat.card (fittingSubgroup Q)) :
    IsElementaryAbelian p (pCore p Q ⧸ frattini (pCore p Q)) ∧
      Nat.card (pCore p Q ⧸ frattini (pCore p Q)) = p ^ 2 := by
  let e := FittingActions.coreOmegaEquiv (Or.inr hn) hd
  obtain ⟨hel,hcard⟩ := Nilpotent.frattini_shape hn hd
  let := hel
  exact ⟨IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective,
    (Nat.card_congr e.toEquiv).trans hcard⟩

/-- Nontrivial coprime movement is detected at a genuine primary plane of prime greater than five. -/
theorem exists_moved_nilpotent_primary_plane {Q : Type*} [Group Q] [Finite Q]
    (hn : A36Nilpotent Q) (a : MulAut Q)
    (hcop : Nat.Coprime (orderOf a) (Nat.card Q)) (hne : a ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ 5 < p ∧ p ∣ Nat.card (fittingSubgroup Q) ∧
      (LocalModels.OddExtraspecialThree p (pCore p Q) ∨
        LocalModels.HomocyclicTwo p (pCore p Q)) ∧
      IsElementaryAbelian p (pCore p Q ⧸ frattini (pCore p Q)) ∧
      Nat.card (pCore p Q ⧸ frattini (pCore p Q)) = p ^ 2 ∧
      primaryFrattiniAut p Q a ≠ 1 := by
  have hself : centralizer (fittingSubgroup Q : Set Q) ≤ fittingSubgroup Q := by
    rw [← hn.1]
    exact centralizer_generalizedFitting_le Q
  obtain ⟨p,hp,hd,hm⟩ := MulAut.exists_moved_primary_frattini_of_coprime hself a hcop hne
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hel,hcard⟩ := nilpotent_primary_frattini_shape hn hd
  have hp3 := (CFSG.Quasithin.Chapter1.RadicalStructure.radical_core (Or.inr hn) hd).2.1
  have hp5 : p ≠ 5 := by
    intro he
    subst p
    let := hel
    obtain ⟨f,hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
      (p := 5) (n := 2) (pCore 5 Q ⧸ frattini (pCore 5 Q)) hcard.le
    let b := primaryFrattiniAut 5 Q a
    have h120 : 120 ∣ Nat.card Q := by
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hn.2.2.1
      have hq : Nat.card (Q ⧸ generalizedFitting Q) = 120 := by
        rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two, hF]
        norm_num
      exact hq ▸ (generalizedFitting Q).card_quotient_dvd_card
    have hgl : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)) = 480 := by
      rw [Matrix.card_GL_field]
      norm_num [Fin.prod_univ_two]
    have hb480 : orderOf b ∣ 480 := by
      rw [← hgl, ← orderOf_injective f hf b]
      exact orderOf_dvd_natCard _
    have hb120 : Nat.Coprime (orderOf b) 120 :=
      hcop.of_dvd (orderOf_map_dvd (primaryFrattiniAut 5 Q) a) h120
    have hb480cop : Nat.Coprime (orderOf b) 480 := by
      exact (hb120.pow_right 2).of_dvd_right (by norm_num : 480 ∣ 120 ^ 2)
    exact hm (orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hb480cop dvd_rfl hb480))
  refine ⟨p,hp,?_,hd,?_,hel,hcard,hm⟩
  · have hp4 : p ≠ 4 := by intro he; subst p; norm_num at hp
    omega
  · exact (hn.2.2.2 p hp (by simpa only [hn.1] using hd)).2

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear
