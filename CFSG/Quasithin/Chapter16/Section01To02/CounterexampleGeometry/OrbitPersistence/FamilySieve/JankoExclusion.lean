module
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.FamilySieve.SourceLists
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
public import Theory.SpecificGroups.Tits.FiniteImageOrder
public import BenderSuzuki.SE.Section11Lemma115Endpoint
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.AtlasPort.LinearGroups.G2.Order
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FormTransport
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices
public import Theory.SpecificGroups.Triality.LeviArmCommutation
public import Theory.SpecificGroups.Triality.LeviIdentification
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.SporadicFour.JankoTwo
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
public import Theory.SpecificGroups.Rudvalis.Model.ElementaryFive
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.SuzukiCoordinates
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.Actions
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock

/-!
# Excluding J₁ from the even-type component list

We exhaust the actual (E2) alternatives after identifying the trivial-two-core
quotient with the given group. The certified J₁ order is 175560, whose two-part
is eight. In the PSL₂ order identity the only possible parameter is 56;
its two distinct prime divisors exclude it as a finite-field order.

The split, unitary and Suzuki cases are separated by their orders or two-parts.
The genuine triality arm Levi is PSL₂ over the cubic extension: the two-part
forces the base field to have order two, and the resulting subgroup of order
504 still cannot divide 175560. The genuine Ree Suzuki root block has order
q², already with too large a two-part. The Tits presentation has a certified
finite quotient larger than J₁; no faithfulness or simplicity is needed here.

For the sporadics, the existing Mathieu and HS orders and the explicit
three-subgroups in J₂ and J₄ and five-subgroup in Ru suffice. These comparisons
use actual carriers and maps. The imported matrix and permutation certificates
retain their ATLAS source attribution and licenses. The private PSL₂ identity
is the calculation of `RankOneModels.Orders`, under narrow order imports.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, (E2) on
printed p.1170 and the list intersection for Lemma 16.2.5 on p.1174;
the other list is A.3.8(3), printed pp.45–46 (`refs/quasithin.pdf`).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.FamilySieve
open ClassificationModels ChapterA.Section02
open Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
open scoped MatrixGroups

variable {S : Type*} [Group S]

private theorem psl_two_card_mul {L : Type*} [Group L] {q : ℕ}
    (h : ClassicalGroup.IsPSL L 2 q) :
    Nat.card L * Nat.gcd 2 (q - 1) = q * (q ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  have hq : 1 < q := hF ▸ (Finite.one_lt_card (α := F))
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 2
  rw [← Nat.card_congr e.toEquiv, hF] at hc
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at hc
  have hsub : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one, pow_two]
  rw [hsub] at hc
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q - 1 by omega)
  calc
    _ = (q ^ 2 - 1) * (q * (q - 1)) := hc
    _ = _ := by ring

private theorem two_power_bound {n : ℕ} (hd : 2 ^ n ∣ 175560) : n ≤ 3 := by
  by_contra hn
  have hh : 16 ∣ 175560 := (show 2^4 ∣ 2^n from pow_dvd_pow 2 (by omega)).trans hd
  norm_num at hh

private theorem not_psl_two (hc : Nat.card S = 175560) {q : ℕ}
    (h : ClassicalGroup.IsPSL S 2 q) : False := by
  have ho := psl_two_card_mul h
  rw [hc] at ho
  have hq : q < 71 := by
    by_contra hn
    have hm := Nat.mul_le_mul (show 71 ≤ q by omega)
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left (show 71 ≤ q by omega) 2) 1)
    have hg := Nat.gcd_le_left (q-1) (by decide : 0 < 2)
    have hh := Nat.mul_le_mul_left 175560 hg
    norm_num at hm
    omega
  have h56 : q = 56 := by
    interval_cases q <;> norm_num at *
  obtain ⟨F, _, _, hF, _⟩ := h
  let := Fintype.ofFinite F
  have hf := FiniteField.isPrimePow_card F
  have hcard : Fintype.card F = 56 := by simpa only [Nat.card_eq_fintype_card] using hF.trans h56
  rw [hcard, isPrimePow_iff_unique_prime_dvd] at hf
  obtain ⟨r, _, hr⟩ := hf
  have h2 := hr 2 (by norm_num)
  have h7 := hr 7 (by norm_num)
  omega

private theorem not_psl_three_three (hc : Nat.card S = 175560)
    (h : ClassicalGroup.IsPSL S 3 3) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  have ho := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [← Nat.card_congr e.toEquiv, hc, hF] at ho
  norm_num [Fin.prod_univ_succ] at ho

private theorem not_binary_linear (hc : Nat.card S = 175560) {n : ℕ}
    (hn : n = 4 ∨ n = 5) (h : ClassicalGroup.IsPSL S n 2) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let : NeZero n := ⟨by omega⟩
  have ho := Atlas.ExceptionalSupport.card_psl_mul (F := F) n
  rw [← Nat.card_congr e.toEquiv, hc, hF] at ho
  rcases hn with rfl | rfl <;> norm_num [Fin.prod_univ_succ] at ho

private theorem not_suzuki (hc : Nat.card S = 175560) {m : ℕ} (hm : 1 ≤ m)
    (h : Nonempty (S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) : False := by
  obtain ⟨e⟩ := h
  have ho := Nat.card_congr e.toEquiv
  rw [hc, BenderSuzuki.lemma115_suzukiMatrixGroup_card_formula m (by omega)] at ho
  have hd : 2 ^ ((2*m+1)*2) ∣ 175560 := by
    rw [ho, pow_mul]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have := two_power_bound hd
  omega

private theorem not_linear_three (hc : Nat.card S = 175560) {f : ℕ} (hf : 1 ≤ f)
    (h : ClassicalGroup.IsPSL S 3 (2^f)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let q := 2^f
  have hq : 2 ≤ q := Nat.le_pow (by omega)
  have ho := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [← Nat.card_congr e.toEquiv, hF] at ho
  change Nat.card S * Nat.gcd 3 (q-1) * (q-1) = _ at ho
  simp only [Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero,
    pow_one, Nat.zero_add, Nat.reduceAdd, Fin.prod_univ_zero, mul_one] at ho
  change Nat.card S * Nat.gcd 3 (q-1) * (q-1) =
    (q^3-1)*((q^3-q)*(q^3-q^2)) at ho
  have hfact1 : q^3-q = q*(q^2-1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]; congr 1; ring
  have hfact2 : q^3-q^2 = q^2*(q-1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]; congr 1
  have ho' : Nat.card S * Nat.gcd 3 (q-1) = q^3*(q^3-1)*(q^2-1) := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < q-1 by omega)
    calc
      _ = (q^3-1)*((q^3-q)*(q^3-q^2)) := ho
      _ = _ := by rw [hfact1, hfact2]; ring
  have hd : q^3 ∣ Nat.card S := by
    have hcop : Nat.Coprime (q^3) (Nat.gcd 3 (q-1)) := by
      apply Nat.Coprime.pow_left
      apply Nat.Coprime.pow_left
      exact (show Nat.Coprime 2 3 by decide).of_dvd_right (Nat.gcd_dvd_left 3 (q-1))
    apply hcop.dvd_mul_right.mp
    rw [ho']
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  rw [hc] at hd ho'
  have hb := two_power_bound (by simpa only [q, ← pow_mul] using hd)
  have hfone : f = 1 := by omega
  norm_num [q, hfone] at ho'

private theorem not_symplectic (hc : Nat.card S = 175560) {f : ℕ} (hf : 2 ≤ f)
    (h : ClassicalGroup.IsPSp S 2 (2^f)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have ho := (Nat.card_congr e.toEquiv).trans
    (Nat.card_congr (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm.toEquiv)
  rw [Theory.SpecificGroups.SymplecticFour.card_sp, hF] at ho
  have hd : 2^(f*4) ∣ 175560 := by
    rw [← hc, ho, pow_mul]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have := two_power_bound hd
  omega

private theorem not_g2 (hc : Nat.card S = 175560) {f : ℕ} (hf : 2 ≤ f)
    (h : IsG2At S (2^f)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  have ho := Nat.card_congr e.toEquiv
  rw [Atlas.G2.card_Model, hF] at ho
  have hd : 2^(f*6) ∣ 175560 := by
    rw [← hc, ho, pow_mul]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have := two_power_bound hd
  omega

private theorem not_unitary (hc : Nat.card S = 175560) {f : ℕ} (hf : 2 ≤ f)
    (h : ClassicalGroup.IsPSU S 3 (2^f)) : False := by
  rcases h with ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩
  obtain ⟨C, hC⟩ := ChapterF.Source.Unitary.FormTransport.exists_standard_basis J f (by omega) hcard hconj
  let K := ChapterF.Source.Unitary.FormTransport.standardForm J
  let e' := e.trans (ChapterF.Source.Unitary.FormTransport.projectiveEquiv J C hC)
  have hfixed : Nat.card {x : F // K.conj x = x} = 2^f :=
    ChapterF.Source.Unitary.fixed_card J f (by omega) hcard hconj
  rcases BenderSuzuki.External.huppert_II_10_12 K (2^f) hcard hfixed rfl with
    ⟨_, _, _, _, _, _, hroot, _, _, _⟩
  rcases hroot with ⟨R, H, _, _, _, _, _, _, hRcard, _⟩
  have hd : 2^(f*3) ∣ 175560 := by
    rw [← hc, Nat.card_congr e'.toEquiv, pow_mul, ← hRcard]
    exact R.card_subgroup_dvd_card
  have := two_power_bound hd
  omega

private theorem not_symplectic_derived (hc : Nat.card S = 175560)
    (h : Nonempty (S ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) : False := by
  obtain ⟨e⟩ := h
  have ho := Nat.card_congr (e.trans
    Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toEquiv
  rw [hc, nat_card_alternatingGroup] at ho
  norm_num at ho

private theorem not_g2_derived (hc : Nat.card S = 175560)
    (h : Nonempty (S ≃* commutator (Atlas.G2.Model (ZMod 2)))) : False := by
  obtain ⟨e⟩ := h
  have ho := Nat.card_congr e.toEquiv
  rw [hc, Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
    Atlas.G2.BinaryException.card_H] at ho
  norm_num at ho

private theorem not_tits (hc : Nat.card S = 175560)
    (h : Nonempty (S ≃* Tits.ParrottGroup)) : False := by
  obtain ⟨e⟩ := h
  let : Finite S := Nat.finite_of_card_ne_zero (by omega)
  have ho := Nat.card_le_card_of_surjective (Tits.parrottFiniteImageMap ∘ e)
    (Tits.parrottFiniteImageMap_surjective.comp e.surjective)
  rw [hc, Tits.atlas1600Group_card] at ho
  omega

private theorem odd_subgroup_cyclic {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hc : Nat.card G = 175560) (hp : ¬ p^2 ∣ 175560)
    (P : Subgroup G) (hP : IsPGroup p P) : IsCyclic P := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hd := P.card_subgroup_dvd_card
  rw [hc, hn] at hd
  have hb : n ≤ 1 := by
    by_contra hh
    exact hp ((pow_dvd_pow p (by omega : 2 ≤ n)).trans hd)
  exact isCyclic_of_card_dvd_prime (p := p) (by rw [hn]; simpa only [pow_one] using pow_dvd_pow p hb)

private theorem not_sporadic (hc : Nat.card S = 175560)
    (h : IsEvenTypeSporadicQuotient S) : False := by
  obtain ⟨name, hj3, hhe, ⟨e⟩⟩ := h
  have ho : Nat.card name.Carrier = 175560 := (Nat.card_congr e.toEquiv).symm.trans hc
  cases name with
  | m11 => have := Sporadic.Mathieu.m11_order; change Nat.card Sporadic.Mathieu.M11 = _ at ho; omega
  | m12 => have := Sporadic.Mathieu.m12_order; change Nat.card Sporadic.Mathieu.M12 = _ at ho; omega
  | m22 => have := Sporadic.Mathieu.m22_order; change Nat.card Sporadic.Mathieu.M22 = _ at ho; omega
  | m23 => have := Sporadic.Mathieu.m23_order; change Nat.card Sporadic.Mathieu.M23 = _ at ho; omega
  | m24 => have := Sporadic.Mathieu.m24_order; change Nat.card Sporadic.Mathieu.M24 = _ at ho; omega
  | j3 => exact hj3 rfl
  | he => exact hhe rfl
  | hs =>
    have := Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier
    change Nat.card Sporadic.LeechRelated.HS.Carrier = _ at ho
    omega
  | j2 =>
    change Nat.card Sporadic.LeechRelated.J2.Carrier = 175560 at ho
    obtain ⟨P, hP, hn⟩ := j2_noncyclic_three_subgroup
    exact hn (odd_subgroup_cyclic ho (by norm_num : ¬ 3^2 ∣ 175560) P hP)
  | j4 =>
    change Nat.card Janko4.Model = 175560 at ho
    have hd := (Janko4.Simplicity.threeLocalSubgroup
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four).card_subgroup_dvd_card
    rw [Janko4.Simplicity.threeLocal_card, ho] at hd
    norm_num at hd
  | ru =>
    change Nat.card Rudvalis.Model = 175560 at ho
    have hd := Rudvalis.ElementaryFive.subgroup.card_subgroup_dvd_card
    rw [Rudvalis.ElementaryFive.subgroup_elementary_and_card.2, ho] at hd
    norm_num at hd

private theorem not_triality (hc : Nat.card S = 175560) {f : ℕ} (hf : 1 ≤ f)
    (h : Triality.Standard.IsTrialityGroupAt (2^f) S) : False := by
  obtain ⟨P, hq, ⟨e⟩⟩ := h
  have hp2 : P.prime = 2 := by
    apply (Nat.prime_dvd_prime_iff_eq P.prime_prime Nat.prime_two).mp
    apply P.prime_prime.dvd_of_dvd_pow (n := f)
    rw [← hq]
    exact dvd_pow_self P.prime (Nat.ne_of_gt P.exponent_pos)
  let := Triality.Standard.Parabolics.rankOneExtensionCharTwo P hp2
  let eLevi := Triality.Standard.Parabolics.leviArmsEquivPSL2OfPinnedMaps P hp2
    (Triality.Standard.Parabolics.pinnedRankOneMaps P hp2)
    (Triality.Standard.Parabolics.armRootCommutation P hp2)
  let E := Triality.Standard.ExtensionField P
  let j : Multiplicative E →* S := e.symm.toMonoidHom.comp
    ((Triality.Standard.Parabolics.levi P .arms).subtype.comp
      (eLevi.symm.toMonoidHom.comp
        ((Theory.PSL2.sl2QuotientEquiv E).toMonoidHom.comp
          (Matrix.SpecialLinearGroup.upperUnipotentHom E))))
  have hj : Function.Injective j := e.symm.injective.comp
    ((Subgroup.subtype_injective _).comp (eLevi.symm.injective.comp
      ((Theory.PSL2.sl2QuotientEquiv E).injective.comp
        (Matrix.SpecialLinearGroup.upperUnipotentHom_injective E))))
  have hd := Subgroup.card_dvd_of_injective j hj
  change Nat.card E ∣ Nat.card S at hd
  rw [hc, Triality.Standard.card_extensionField, hq, ← pow_mul] at hd
  have hb := two_power_bound hd
  have hfone : f = 1 := by omega
  have hE : Nat.card E = 8 := by
    rw [Triality.Standard.card_extensionField, hq, hfone]
    norm_num
  have hmodel : ClassicalGroup.IsPSL
      (Triality.Standard.Parabolics.levi P .arms) 2 8 :=
    ⟨E, inferInstance, inferInstance, hE, ⟨eLevi⟩⟩
  have horder := psl_two_card_mul hmodel
  norm_num at horder
  have hd' := (Triality.Standard.Parabolics.levi P .arms).card_subgroup_dvd_card
  rw [← Nat.card_congr e.toEquiv, hc, horder] at hd'
  norm_num at hd'

private theorem not_ree (hc : Nat.card S = 175560) {m : ℕ} (hm : 1 ≤ m)
    (h : Nonempty (S ≃* ReeF4.Model m)) : False := by
  obtain ⟨e⟩ := h
  let d := ReeF4.canonicalLocalBlockInput m
  let eS := d.modelEquiv.trans e.symm
  let C := ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery.suzukiCoordinates d
  have horder := Nat.card_congr (C.blockEquiv true)
  rw [Nat.card_prod, ReeF4.field_card] at horder
  have hd := (ReeF4.LocalBlockInput.PairRigidity.simpleBlock d .suzuki true).card_subgroup_dvd_card
  rw [← horder, Nat.card_congr eS.toEquiv, hc] at hd
  have hb := two_power_bound (by simpa only [← pow_two, ← pow_mul] using hd)
  omega

/-- No carrier in the complete characteristic-two (E2) quotient list has the
order of the concrete J₁ model. -/
private theorem janko_order_excludes_lie (hc : Nat.card S = 175560)
    (h : IsEvenTypeLieQuotient S) : False := by
  rcases h with h | ⟨f, h⟩ | ⟨n, hn, h⟩
  · cases h with
    | linear f hf h => exact not_psl_two hc h
    | unitary f hf h => exact not_unitary hc hf h
    | suzuki m hm h => exact not_suzuki hc hm h
  · cases h with
    | linear hf h => exact not_linear_three hc hf h
    | symplectic hf h => exact not_symplectic hc hf h
    | g2 hf h => exact not_g2 hc hf h
    | triality hf h => exact not_triality hc hf h
    | ree_f4 m hm hf h => exact not_ree hc hm h
    | symplectic_derived hf h => exact not_symplectic_derived hc h
    | g2_derived hf h => exact not_g2_derived hc h
    | tits hf h => exact not_tits hc h
  · exact not_binary_linear hc hn h

/-- J₁ cannot satisfy (E2) when its two-core is trivial. The characteristic-two
and sporadic alternatives are compared through the actual two-core quotient. -/
theorem janko_one_exclusion (S : Type*) [Group S] [Finite S]
    (hcore : pCore 2 S = ⊥) (heven : IsEvenTypeComponent S)
    (hj : Nonempty (S ≃* Janko1.Model)) : False := by
  obtain ⟨e⟩ := hj
  have hc := (Nat.card_congr e.toEquiv).trans Janko1.card_model
  let eq : (S ⧸ pCore 2 S) ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  have hquot := (Nat.card_congr eq.toEquiv).trans hc
  rcases heven with h | h | ⟨p, _, h⟩ | h
  · exact janko_order_excludes_lie hquot h.1
  · exact not_psl_three_three hc h
  · exact not_psl_two hc h
  · exact not_sporadic hquot h

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.FamilySieve
