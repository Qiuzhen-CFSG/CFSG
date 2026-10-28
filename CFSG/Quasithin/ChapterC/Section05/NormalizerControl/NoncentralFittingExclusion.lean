module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting
public import Theory.Representation.BinaryEightPrimeObstruction
public import Theory.Representation.CentralizerQuotientAction
/-!
# The small-dimensional noncentral Fitting obstruction

The noncentral A.3.6 structure forces every prime in F(L) to have a
primary core of order at least p². The source constructs L/F(L)≃SL₂(r), r>3. Unless r=5, primary
support forces r³ to divide the group order, impossible in GL₈(2).
For r=5 every primary prime is 5 or congruent to ±1 modulo five. The order of GL₈(2) then forces
p = 5, but the quotient contributes another factor five, impossible
in GL₈(2). This uses the genuine SQTK odd-rank hypotheses through the
proved A.3.6 primary-shape theorem.

The centralizer-quotient application retains the actual two-core kernel;
it does not assume a faithful representation of the two-core quotient.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter1.Section02 LocalModels
open CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
open CFSG.Quasithin

namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
private theorem square_dvd_of_shape {A : Type*} [Group A] {p : ℕ}
    (h : OddExtraspecialThree p A ∨ HomocyclicTwo p A) : p^2 ∣ Nat.card A := by
  rcases h with h | ⟨a, ha, ⟨e⟩⟩
  · rw [h.1.2]
    exact pow_dvd_pow _ (by decide)
  · rw [Nat.card_congr e.toEquiv]
    rw [Nat.card_congr Multiplicative.toAdd]
    simp only [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    rw [← pow_mul]
    exact pow_dvd_pow _ (by omega)

private theorem prime_eq_five {p : ℕ} (hp : p.Prime)
    (hs : p = 5 ∨ p % 5 = 1 ∨ p % 5 = 4)
    (hd : p^2 ∣ Nat.card (GL (Fin 8) (ZMod 2))) : p = 5 := by
  have hd1 : p ∣ Nat.card (GL (Fin 8) (ZMod 2)) :=
    (dvd_pow_self p (by decide : 2 ≠ 0)).trans hd
  have h := Representation.BinaryEight.prime_divisors_binary_GL_eight hp hd1
  rcases h with h | h | h | h | h | h | h <;> subst p
  all_goals try omega
  rw [Matrix.card_GL_field] at hd
  norm_num [Fin.prod_univ_succ] at hd

/-- An actual SQTK C-component with SL₂(5) Fitting quotient has central
Fitting subgroup whenever its order divides the binary degree-eight order. -/
theorem fitting_central_of_card_dvd_binary_eight {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    {κ : GroupClass} (hG : IsSQTK κ G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent)
    (e : (L ⧸ fittingSubgroup L) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))
    (hd : Nat.card L ∣ Nat.card (GL (Fin 8) (ZMod 2))) :
    fittingSubgroup L ≤ center L := by
  by_contra hn
  have hnon : Nat.card (fittingSubgroup L) ≠ 1 := by
    intro hc
    apply hn
    rw [card_eq_one.mp hc]
    exact bot_le
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hnon
  let : Fact p.Prime := ⟨hp⟩
  have hq : PrimeSL2FittingQuotient L := ⟨5, by decide, by decide, ⟨e⟩⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hs := CoreShapes.PrimeSupport.prime_support
    CFSG.Quasithin.ChapterA.RankActions.primeSL2CoverRigidity
    hG hO hL (by decide : 3 < 5) e hp hpd
  have hshape := CoreShapes.PrimaryShapes.primary_shapes
    CFSG.Quasithin.ChapterA.RankActions.primeSL2CoverRigidity
    hG hO hL hq p hpd
  have hdF : p^2 ∣ Nat.card (fittingSubgroup L) :=
    (square_dvd_of_shape hshape).trans (card_dvd_of_le (pCore_le_fitting L p))
  have hp5 : p = 5 := prime_eq_five hp (hs.elim Or.inl (fun h => Or.inr h.2))
    (hdF.trans ((fittingSubgroup L).card_subgroup_dvd_card.trans hd))
  subst p
  have hc : Nat.card (L ⧸ fittingSubgroup L) = 120 := by
    rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two, Nat.card_zmod]
    norm_num
  have hd125 : 125 ∣ Nat.card L := by
    rw [card_eq_card_quotient_mul_card_subgroup (fittingSubgroup L), hc]
    exact Nat.mul_dvd_mul (by decide : 5 ∣ 120) hdF
  have hb := hd125.trans hd
  rw [Matrix.card_GL_field] at hb
  norm_num [Fin.prod_univ_succ] at hb


/-- The actual small module excludes a noncentral SL₂(5) Fitting section
modulo the two-core. The centralizer may be nontrivial: its containment in
the two-core gives order divisibility between the two different quotients. -/
theorem fitting_central_of_small_centralizer_quotient
    {D : Type*} [Group D] [Finite D] {κ : GroupClass} (hD : IsSQTK κ D)
    (V : Subgroup D) [V.Normal] [IsElementaryAbelian 2 V]
    (hr : Module.finrank (ZMod 2) (Additive V) ≤ 8)
    (hk : centralizer (V : Set D) ≤ pCore 2 D)
    (L : Subgroup (D ⧸ pCore 2 D)) (hL : L.IsCComponent)
    (e : (L ⧸ fittingSubgroup L) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :
    fittingSubgroup L ≤ center L := by
  have hQ : IsSQTK κ (D ⧸ pCore 2 D) := by
    refine ⟨?_, hD.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hD.stronglyQuasithin p hp ho)
  have hd : Nat.card (D ⧸ pCore 2 D) ∣ Nat.card (D ⧸ centralizer (V : Set D)) := by
    rw [← index_eq_card, ← index_eq_card]
    exact index_dvd_of_le hk
  let ρ := Representation.centralizerQuotient V
  have hi : Function.Injective ρ := by
    intro a b hab
    apply Representation.centralizerQuotient_faithful V
    exact Units.ext hab
  have hgl := Representation.card_dvd_card_GL_of_injective ρ hi
  have hbound := Representation.BinaryEight.card_binary_GL_dvd_eight hr
  exact fitting_central_of_card_dvd_binary_eight hQ (pCore_quotient_pCore_eq_bot 2)
    hL e (L.card_subgroup_dvd_card.trans (hd.trans (hgl.trans hbound)))

/-- The genuine A.3.6 producer removes the prime-field model premise:
every such small SQTK C-component has central Fitting subgroup. -/
theorem fitting_central_of_small_order {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    {κ : GroupClass} (hG : IsSQTK κ G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) (hd : Nat.card L ∣ Nat.card (GL (Fin 8) (ZMod 2))) :
    fittingSubgroup L ≤ center L := by
  by_contra hn
  obtain ⟨r,hr,hr3,⟨e⟩⟩ := primeSL2FittingQuotient_of_noncentral
    CFSG.Quasithin.ChapterA.RankActions.primeSL2CoverRigidity hG hO hL hn
  let : Fact r.Prime := ⟨hr⟩
  by_cases hr5 : r=5
  · subst r
    exact hn (fitting_central_of_card_dvd_binary_eight hG hO hL e hd)
  have hnon : Nat.card (fittingSubgroup L) ≠ 1 := by
    intro hc
    apply hn
    rw [card_eq_one.mp hc]
    exact bot_le
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd hnon
  let : Fact p.Prime := ⟨hp⟩
  have hs := CoreShapes.PrimeSupport.prime_support
    CFSG.Quasithin.ChapterA.RankActions.primeSL2CoverRigidity hG hO hL hr3 e hp hpd
  have hpr : p=r := hs.resolve_right (fun h => hr5 h.1)
  subst p
  have hshape := CoreShapes.PrimaryShapes.primary_shapes
    CFSG.Quasithin.ChapterA.RankActions.primeSL2CoverRigidity
    hG hO hL ⟨r,hr,hr3,⟨e⟩⟩ r hpd
  have hsq : r^2 ∣ Nat.card (fittingSubgroup L) :=
    (square_dvd_of_shape hshape).trans (card_dvd_of_le (pCore_le_fitting L r))
  have hq : r ∣ Nat.card (L ⧸ fittingSubgroup L) := by
    rw [Nat.card_congr e.toEquiv,Atlas.card_sl_two,Nat.card_zmod]
    exact dvd_mul_right _ _
  have hc : r^3 ∣ Nat.card L := by
    rw [show r^3=r*r^2 by ring,card_eq_card_quotient_mul_card_subgroup (fittingSubgroup L)]
    exact Nat.mul_dvd_mul hq hsq
  have hcGL := hc.trans hd
  have hlist := Representation.BinaryEight.prime_divisors_binary_GL_eight hr
    ((dvd_pow_self r (by decide : 3≠0)).trans hcGL)
  rcases hlist with h | h | h | h | h | h | h <;> subst r
  all_goals try omega
  all_goals rw [Matrix.card_GL_field] at hcGL
  all_goals norm_num [Fin.prod_univ_succ] at hcGL

/-- Every actual C-component of D/O₂(D) is quasisimple on a small binary
module with C_D(V)≤O₂(D). The earlier source classification supplies all
Fitting-quotient alternatives internally. -/
theorem quasisimple_of_small_centralizer_quotient
    {D : Type*} [Group D] [Finite D] {κ : GroupClass} (hD : IsSQTK κ D)
    (V : Subgroup D) [V.Normal] [IsElementaryAbelian 2 V]
    (hr : Module.finrank (ZMod 2) (Additive V) ≤ 8)
    (hk : centralizer (V : Set D) ≤ pCore 2 D)
    (L : Subgroup (D ⧸ pCore 2 D)) (hL : L.IsCComponent) :
    IsQuasisimple L := by
  have hQ : IsSQTK κ (D ⧸ pCore 2 D) := by
    refine ⟨?_, hD.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hD.stronglyQuasithin p hp ho)
  have hd : Nat.card (D ⧸ pCore 2 D) ∣ Nat.card (D ⧸ centralizer (V : Set D)) := by
    rw [← index_eq_card, ← index_eq_card]
    exact index_dvd_of_le hk
  let ρ := Representation.centralizerQuotient V
  have hi : Function.Injective ρ := by
    intro a b hab
    apply Representation.centralizerQuotient_faithful V
    exact Units.ext hab
  have hgl := Representation.card_dvd_card_GL_of_injective ρ hi
  have hbound := Representation.BinaryEight.card_binary_GL_dvd_eight hr
  have hf := fitting_central_of_small_order hQ (pCore_quotient_pCore_eq_bot 2)
    hL (L.card_subgroup_dvd_card.trans (hd.trans (hgl.trans hbound)))
  have hr : solvableRadical L = center L := by
    apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hf)
    exact le_solvableRadical (center L) inferInstance
      (Group.isSolvable_of_comm (fun a b => Subtype.ext
        (mem_center_iff.mp a.property b).symm))
  let := hL.perfect
  let := hL.isSimpleGroup_quotient_solvableRadical
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
