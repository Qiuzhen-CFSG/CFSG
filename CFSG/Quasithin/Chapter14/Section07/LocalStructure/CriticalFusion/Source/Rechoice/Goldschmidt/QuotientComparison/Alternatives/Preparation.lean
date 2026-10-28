module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.LocalResiduals
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
public import Theory.GroupTheory.PResidual.PrimeToSubnormal

/-!
# Excluding the collapsed and first-row alternatives in 14.7.70

A subnormal S₃ has odd index when the ambient Sylow two-group has order
 two. It is therefore the ambient prime-to-two residual and is normal.
 The source small subnormal witness now excludes a Sylow plus image of
 order two: its two simple alternatives have order divisible by four,
 and the S₃ alternative contradicts the local residual centralization
 obstruction.

F.6.11's compatible local equivalence transfers this order obstruction
 to the bang quotient. Consequently the collapsed S₃ case is impossible,
 the bang images form a genuine Goldschmidt triple, and the full F.6.18
 implication applies with the original I as its SQTK cover. The common
 Sylow in that classification has order different from two, excluding row (1).

`RowTwoModel` spells out exactly the weaker shape extracted in row (2)
 of FSource, not the native marked F.6.16 classification. Its elimination
 must retain the native actions from Noncyclic.SourceImplication when used.
 The row-(2) elimination and the comparison of rows (3)–(13) remain separate
 prerequisites; no bang recognition or equality of the ambient quotients
 is asserted here. The universal F.6.18 input is owned by qt-f-06.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
 Lemma 14.7.70, printed pp.1074–1075 (PDF pp.1091–1092),
 F.6.11(2), printed pp.306–307, and F.6.18, printed pp.309–310.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives

private theorem symmetricThree_two_factors : ∀ x : Equiv.Perm (Fin 3),
    ∃ a b : Equiv.Perm (Fin 3), a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ x = a * b := by
  decide +kernel

private theorem symmetricThree_primeToResidual {D : Type*} [Group D]
    (e : D ≃* Equiv.Perm (Fin 3)) : primeToResidual 2 D = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, b, ha, hb, he⟩ := symmetricThree_two_factors (e x)
  have hpow (a : Equiv.Perm (Fin 3)) (ha : a ^ 2 = 1) :
      e.symm a ∈ primeToResidual 2 D := by
    apply mem_primeToResidual_of_pow (n := 1)
    simpa only [pow_one, map_pow, map_one] using congrArg e.symm ha
  have hx := (primeToResidual 2 D).mul_mem (hpow a ha) (hpow b hb)
  simpa only [← map_mul, ← he, e.symm_apply_apply] using hx

private theorem no_four_divisor {D : Type*} [Group D] [Finite D]
    (S : Sylow 2 D) (hS : Nat.card S = 2) : ¬ 4 ∣ Nat.card D := by
  intro hd
  have he : Nat.card D = 2 * (S : Subgroup D).index := by
    rw [← (S : Subgroup D).index_mul_card, hS, mul_comm]
  rw [he] at hd
  change 2 * 2 ∣ 2 * (S : Subgroup D).index at hd
  exact S.not_dvd_index ((Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp hd)

/-- With an ambient Sylow of order two, a subnormal S₃ is normal. Its
odd index identifies it with the actual prime-to-two residual. -/
private theorem normal_symmetricThree_of_sylow_two
    {D : Type*} [Group D] [Finite D] (S : Sylow 2 D) (hS : Nat.card S = 2)
    (K : Subgroup D) (hK : K.IsSubnormal) (e : K ≃* Equiv.Perm (Fin 3)) : K.Normal := by
  have hk : Nat.card K = 6 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hi : K.index * 3 = (S : Subgroup D).index := by
    have h₁ := K.index_mul_card
    have h₂ := (S : Subgroup D).index_mul_card
    rw [hk] at h₁
    rw [hS] at h₂
    omega
  have hodd : Nat.Coprime 2 K.index := Nat.prime_two.coprime_iff_not_dvd.mpr (by
    intro hd
    apply S.not_dvd_index
    rw [← hi]
    exact dvd_mul_of_dvd_left hd 3)
  rw [← primeToResidual_eq_of_subnormal_coprime_index 2 K hK
    (symmetricThree_primeToResidual e) hodd]
  infer_instance

open Representation Chapter12.Section08
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
/-- The exact two shapes in FSource row (2). The extraspecial clause
retains a literal normal subgroup and quotient; it does not specify an action. -/
def RowTwoModel (D : Type*) [Group D] : Prop :=
  Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
    ∃ N : Subgroup D, ∃ _ : N.Normal,
      IsExtraspecial 3 N ∧ Nat.card N = 27 ∧ Monoid.exponent N = 3 ∧
      Nonempty ((D ⧸ N) ≃* FSource.E4)

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)

/-- The prescribed Sylow image in the literal plus quotient. -/
def plusSylow : Sylow 2 ((I c) ⧸ pCore 2 (I c)) :=
  (sylow c).mapSurjective (QuotientGroup.mk'_surjective _)

/-- The prescribed Sylow image in the literal bang quotient. -/
def bangSylow : Sylow 2 ((I c) ⧸ pPrimeCore 3 (I c)) :=
  (sylow c).mapSurjective (QuotientGroup.mk'_surjective _)

@[simp] theorem plusSylow_coe : (plusSylow c : Subgroup _) = plus c (T : Subgroup G) := rfl
@[simp] theorem bangSylow_coe : (bangSylow c : Subgroup _) = bang c (T : Subgroup G) := rfl

/-- The small subnormal witness excludes a Sylow image of order two:
the simple cases have order divisible by four, and the S₃ case would be normal. -/
theorem plus_sylow_card_ne_two (h : Geometry d c) (k : CoreFacts c)
    (small : SmallSubnormal c) : Nat.card (plus c (T : Subgroup G)) ≠ 2 := by
  intro hS
  have htwo : Nat.card (plusSylow c) = 2 := hS
  have hfour := no_four_divisor (plusSylow c) htwo
  obtain ⟨K, hK, he | he | he⟩ := small
  · obtain ⟨e⟩ := he
    let : K.Normal := normal_symmetricThree_of_sylow_two (plusSylow c) htwo K hK e
    exact no_normal_symmetricThree d c h k K e
  · obtain ⟨e⟩ := he
    apply hfour
    apply dvd_trans (show 4 ∣ Nat.card K from ?_) K.card_subgroup_dvd_card
    rw [Nat.card_congr e.toEquiv, Matrix.PSL3Two.card_SL]
    decide
  · obtain ⟨e⟩ := he
    apply hfour
    apply dvd_trans (show 4 ∣ Nat.card K from ?_) K.card_subgroup_dvd_card
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]

/-- F.6.11 transports this obstruction through the compatible local
equivalence, without identifying the ambient quotients. -/
theorem bang_sylow_card_ne_two (h : Geometry d c) (k : CoreFacts c)
    (small : SmallSubnormal c) : Nat.card (bang c (T : Subgroup G)) ≠ 2 := by
  rw [← sylow_plus_card_eq_bang c k]
  exact plus_sylow_card_ne_two d c h k small

/-- The collapsed symmetric-three quotient in F.6.11(2) is impossible. -/
theorem bang_not_symmetricThree (h : Geometry d c) (k : CoreFacts c)
    (small : SmallSubnormal c) :
    ¬ Nonempty (((I c) ⧸ pPrimeCore 3 (I c)) ≃* Equiv.Perm (Fin 3)) := by
  rintro ⟨e⟩
  let S := (bangSylow c).mapSurjective (f := e.toMonoidHom) e.surjective
  have hc : Nat.card S = 2 := by
    rw [S.card_eq_multiplicity,
      show Nat.card (Equiv.Perm (Fin 3)) = 6 by
        simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]]
    decide +kernel
  have he : Nat.card (bangSylow c) = Nat.card S :=
    Nat.card_congr (e.subgroupMap (bangSylow c : Subgroup _)).toEquiv
  exact bang_sylow_card_ne_two d c h k small (he.trans hc)

/-- The first branch of the full F.6.11 dichotomy gives the actual bang
Goldschmidt triple; the collapsed branch has been eliminated. -/
theorem bang_triple (h : Geometry d c) (k : CoreFacts c) (small : SmallSubnormal c) :
    ChapterF.IsGoldschmidtTriple (bang c (group F L)) (bang c (YT c)) := by
  rcases k.triple.primeToThreeCore_dichotomy with hfull | hcollapsed
  · exact hfull.2.1
  · exact (bang_not_symmetricThree d c h k small hcollapsed.2.2.1).elim

/-- The complete F.6.18 application, with the original I as its SQTK
cover and an arbitrary common Sylow retained. Row (1) is excluded by its order. -/
theorem classified_bang (sourceF : FSource.ClassificationInput KnownSimple.IsKnownSimple.{u})
    (h : Geometry d c) (k : CoreFacts c) (small : SmallSubnormal c) :
    ∃ S : Sylow 2 ((I c) ⧸ pPrimeCore 3 (I c)),
      bang c (group F L) ⊓ bang c (YT c) = (S : Subgroup _) ∧
      Nat.card S ≠ 2 ∧
      (FSource.Alternative (bang c (group F L)) (bang c (YT c)) S ∨
        FSource.Alternative (bang c (YT c)) (bang c (group F L)) S) := by
  let cover : ThreePrimeSQTKQuotient KnownSimple.IsKnownSimple
      ((I c) ⧸ pPrimeCore 3 (I c)) := {
    Cover := I c
    sqtk := (Geometry.local_and_sqtk (d := d) (c := c) k.nontrivial).2
    equiv := MulEquiv.refl _ }
  obtain ⟨S, hS, hs⟩ := sourceF _ _ _ (bang_triple d c h k small) cover
  refine ⟨S, hS, ?_, hs⟩
  intro hcard
  exact bang_sylow_card_ne_two d c h k small
    ((Nat.card_congr ((bangSylow c).equiv S).toEquiv).trans hcard)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives
