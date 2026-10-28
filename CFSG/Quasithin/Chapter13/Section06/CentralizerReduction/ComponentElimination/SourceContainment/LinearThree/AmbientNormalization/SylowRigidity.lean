module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.AmbientNormalization.NormalCover
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.AmbientNormalization.SylowRigidity.FixedPoints
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.QuotientShape
public import Theory.GroupTheory.CComponent.SeedAction
public import Theory.GroupTheory.Hall.SylowSupplementRigidity
public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# Sylow rigidity of A.3.6 radical supplements

A radical supplement covers every quasisimple quotient, hence supplements
F(C) in A.3.6. In the exceptional alternatives all primes in F(C) exceed
three, making F(C) coprime to the given {2,3}-subgroup. Burnside's two-prime
theorem supplies solvability of that subgroup. The simple and quasisimple
alternatives already force the supplement to be the whole component.

In the exceptional cases, `FixedPoints` proves that Sylow fixed points in
F(C) are central, using the actual omega–Frattini actions. The general Hall
conjugacy theorem then controls the supplement. Combining these results
proves intrinsic rigidity with no additional fixed-point or Hall premise.

The normal-cover application constructs the actual Sylow in the image of D
modulo the ambient two-core, transports the perfect supplement K, and proves
the {2,3}-order condition for the image of Lᵥ(Tᵥ ∩ D). The intrinsic two-core
quotient equivalence retains the literal quotient map, so the already proved
kernel-normalization lift applies. No plus-kernel bound or Lᵥ ≤ K is used.
Only the exact A.3.6 conclusion on the quotient image remains explicit;
the ambient-normalization assembly owns its discharge from universal A.3.6
together with construction of the normal cover.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.6,
printed pp.43–45, and the noncentral branch of 13.6.20, printed p.931.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.AmbientNormalization.SylowRigidity
open ComponentSelection Chapter1.Section02
universe u

/-- A radical supplement also supplements the literal A.3.6 Fitting subgroup. -/
theorem fitting_supplement {H : Type*} [Group H] [Finite H]
    (hc : A36Common H) (B : Subgroup H)
    (hB : solvableRadical H ⊔ B = ⊤) : fittingSubgroup H ⊔ B = ⊤ := by
  let : IsQuasisimple (H ⧸ fittingSubgroup H) := hc.2.1
  have he := map_radical_supplement_eq_top_of_quasisimple
    (QuotientGroup.mk' (fittingSubgroup H)) (QuotientGroup.mk'_surjective _) B hB
  have hh := congrArg (comap (QuotientGroup.mk' (fittingSubgroup H))) he
  simpa only [comap_map_eq, QuotientGroup.ker_mk', comap_top, sup_comm] using hh

/-- All exceptional Fitting primes exceed three, with every homocyclic exponent retained. -/
theorem fitting_coprime {H : Type*} [Group H] [Finite H]
    (ha : A36Natural H ∨ A36Nilpotent H) (E : Subgroup H)
    (hE : ∀ p : ℕ, p.Prime → p ∣ Nat.card E → p = 2 ∨ p = 3) :
    Nat.Coprime (Nat.card (fittingSubgroup H)) (Nat.card E) := by
  apply Nat.coprime_of_dvd
  intro p hp hd he
  let : Fact p.Prime := ⟨hp⟩
  have hlarge := (Chapter1.RadicalStructure.radical_core ha hd).2.1
  rcases hE p hp he with rfl | rfl <;> omega

private theorem quasisimple_supplement {H : Type*} [Group H] [Finite H]
    [IsQuasisimple H] (B : Subgroup H)
    (hB : solvableRadical H ⊔ B = ⊤) : B = ⊤ := by
  have h := map_radical_supplement_eq_top_of_quasisimple
    (MonoidHom.id H) Function.surjective_id B hB
  simpa only [map_id] using h

/-- Structural reduction with explicit fixed-point and Hall-conjugacy inputs.
Both inputs are discharged in `normalizes_radical_supplement`. -/
theorem normalizes_of_fixed_points_and_hall
    {X : Type*} [Group X] [Finite X] {C : Subgroup X}
    (ha : A36Conclusion C) (S : Sylow 2 C) (B E : Subgroup C)
    (hB : solvableRadical C ⊔ B = ⊤)
    (hSB : (S : Subgroup C) ≤ normalizer (B : Set C))
    (hSE : (S : Subgroup C) ≤ E)
    (hE : ∀ p : ℕ, p.Prime → p ∣ Nat.card E → p = 2 ∨ p = 3)
    (hfixed : fittingSubgroup C ⊓ centralizer (S : Set C) ≤ center C)
    (hHall : ∀ (N B E : Subgroup C) (S : Sylow 2 C),
      N.Normal → Group.IsNilpotent N → Nat.Coprime 2 (Nat.card N) → N ⊔ B = ⊤ →
      (S : Subgroup C) ≤ normalizer (B : Set C) → (S : Subgroup C) ≤ E →
      Nat.Coprime (Nat.card N) (Nat.card E) → Group.IsSolvable E →
      N ⊓ centralizer (S : Set C) ≤ normalizer (B : Set C) →
      E ≤ normalizer (B : Set C)) : E ≤ normalizer (B : Set C) := by
  classical
  by_cases hq : IsQuasisimple C
  · let := hq
    rw [quasisimple_supplement B hB, normalizer_eq_top]
    exact le_top
  · have hexc := Chapter1.RadicalStructure.nonsimple_radical ha hq
    have hodd : Nat.Coprime 2 (Nat.card (fittingSubgroup C)) := by
      rw [ha.2.1]
      exact pPrimeCore_coprime_card
    exact hHall (fittingSubgroup C) B E S inferInstance inferInstance hodd
      (fitting_supplement ha.2 B hB) hSB hSE (fitting_coprime hexc E hE)
      (isSolvable_of_prime_dvd_card_eq_two_or_three E hE)
      (hfixed.trans (center_le_normalizer (B : Set C)))

/-- In an A.3.6 C-component, every {2,3}-subgroup containing a Sylow
two-subgroup that normalizes a perfect radical supplement normalizes that
supplement. Perfectness of the supplement is retained in the contract, although
the fixed-point and Hall argument works for any radical supplement. -/
theorem normalizes_radical_supplement
    {X : Type*} [Group X] [Finite X] (hX : pCore 2 X = ⊥)
    {C : Subgroup X} (hC : C.IsCComponent) (ha : A36Conclusion C)
    (S : Sylow 2 C) (B E : Subgroup C) (_hperfect : Group.IsPerfect B)
    (hB : solvableRadical C ⊔ B = ⊤)
    (hSB : (S : Subgroup C) ≤ normalizer (B : Set C))
    (hSE : (S : Subgroup C) ≤ E)
    (hE : ∀ p : ℕ, p.Prime → p ∣ Nat.card E → p = 2 ∨ p = 3) :
    E ≤ normalizer (B : Set C) := by
  exact normalizes_of_fixed_points_and_hall ha S B E hB hSB hSE hE
    (FixedPoints.fitting_fixed_central hX hC ha S)
    normalizes_of_nilpotent_supplement_of_sylow_fixed_points

private theorem prime_support_of_cubic_quotient {H : Type*} [Group H] [Finite H]
    (hc : Nat.card (H ⧸ pCore 2 H) = 3) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3 := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  intro p hp hd
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 H), hc, hn] at hd
  rcases hp.dvd_mul.mp hd with h3 | h2
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow h2))

private theorem prime_support_sup {H : Type*} [Group H] [Finite H]
    (R P : Subgroup H) (hn : P ≤ normalizer (R : Set H)) (hP : IsPGroup 2 P)
    (hR : ∀ p : ℕ, p.Prime → p ∣ Nat.card R → p = 2 ∨ p = 3) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card (R ⊔ P : Subgroup H) → p = 2 ∨ p = 3 := by
  intro p hp hd
  have hm : p ∣ Nat.card R * Nat.card P := by
    rw [card_mul_eq_card_inf_mul_card_sup_of_normalizes R P hn]
    exact dvd_mul_of_dvd_right hd _
  rcases hp.dvd_mul.mp hm with h | h
  · exact hR p hp h
  · obtain ⟨n, he⟩ := hP.exists_card_eq
    rw [he] at h
    exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow h))

variable {G : Type u} [Group G] [Finite G]

/-- Instantiate an intrinsic rigidity theorem on the actual normal cover.
Every Sylow, perfectness, normalization and prime-support transport is proved. -/
theorem normalizes_of_intrinsic_rigidity
    (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (D : Subgroup (plusActor K L T v)) (hD : D.IsCComponent)
    (hKD : K.subgroupOf (plusActor K L T v) ≤ D)
    (hLD : Lv L v ≤ D.map (plusActor K L T v).subtype)
    (hgen : solvableRadical D ⊔
      (K.subgroupOf (plusActor K L T v)).subgroupOf D = ⊤)
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hrigid : let C := D.map (QuotientGroup.mk' (pCore 2 (plusActor K L T v)))
      ∀ (S : Sylow 2 C) (B E : Subgroup C), Group.IsPerfect B →
        solvableRadical C ⊔ B = ⊤ →
        (S : Subgroup C) ≤ normalizer (B : Set C) → (S : Subgroup C) ≤ E →
        (∀ p : ℕ, p.Prime → p ∣ Nat.card E → p = 2 ∨ p = 3) →
        E ≤ normalizer (B : Set C)) :
    Lv L v ≤ normalizer (K : Set G) := by
  let A := plusActor K L T v
  let B := (K.subgroupOf A).subgroupOf D
  let R := ((Lv L v).subgroupOf A).subgroupOf D
  let q := QuotientGroup.mk' (pCore 2 A)
  let C := D.map q
  let f : D →* C := q.subgroupMap D
  have hf : Function.Surjective f := q.subgroupMap_surjective D
  have hKA : K ≤ A := K_le_plusActor K L T v
  have hTA : Tv T v ≤ A := le_sup_right
  have hLA : Lv L v ≤ A := le_sup_right.trans le_sup_left
  have hRD : (Lv L v).subgroupOf A ≤ D := by
    intro a ha
    obtain ⟨d, hd, he⟩ := hLD ha
    exact (Subtype.ext he : d = a) ▸ hd
  obtain ⟨SA, hSA⟩ := hSyl.restrict hTA (plusActor_le_Gv K L T v hK.1.1)
  have hSA' : (SA : Subgroup A) = (Tv T v).subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [hSA, map_subgroupOf_eq_of_le hTA]
  obtain ⟨SD, hSD⟩ := SA.exists_subgroupOf_eq_of_subnormal D hD.subnormal
  have hSDB : (SD : Subgroup D) ≤ normalizer (B : Set D) := by
    rw [hSD, hSA', ← subgroupOf_normalizer_eq hKD, ← subgroupOf_normalizer_eq hKA]
    exact comap_mono (comap_mono hn)
  have hSDR : (SD : Subgroup D) ≤ normalizer (R : Set D) := by
    rw [hSD, hSA', ← subgroupOf_normalizer_eq hRD, ← subgroupOf_normalizer_eq hLA]
    exact comap_mono (comap_mono hL)
  let S : Sylow 2 C := SD.mapSurjective hf
  let E : Subgroup D := R ⊔ (SD : Subgroup D)
  let eB : B ≃* K := (subgroupOfEquivOfLe hKD).trans (subgroupOfEquivOfLe hKA)
  let := Chapter1.mem_L_isPerfect hK.1.2
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := eB.symm.toMonoidHom) eB.symm.surjective
  let : Group.IsPerfect (B.map f) := Group.IsPerfect.ofSurjective
    (f := f.subgroupMap B) (f.subgroupMap_surjective B)
  have hgenC : solvableRadical C ⊔ B.map f = ⊤ := by
    apply top_unique
    have he := congrArg (map f) hgen
    rw [Subgroup.map_sup, map_top_of_surjective f hf] at he
    rw [← he]
    exact sup_le_sup (map_solvableRadical_le_of_surjective f hf) le_rfl
  have hSN : (S : Subgroup C) ≤ normalizer (B.map f : Set C) :=
    (map_mono hSDB).trans (B.le_normalizer_map f)
  have hSE : (S : Subgroup C) ≤ E.map f := map_mono le_sup_right
  have hRc : Nat.card R = Nat.card (Lv L v) :=
    Nat.card_congr ((subgroupOfEquivOfLe hRD).trans (subgroupOfEquivOfLe hLA)).toEquiv
  have hRpr : ∀ p : ℕ, p.Prime → p ∣ Nat.card R → p = 2 ∨ p = 3 := by
    rw [hRc]
    exact prime_support_of_cubic_quotient hc
  have hEpr := prime_support_sup R (SD : Subgroup D) hSDR SD.isPGroup' hRpr
  have hnE : E.map f ≤ normalizer (B.map f : Set C) :=
    hrigid S (B.map f) (E.map f) inferInstance hgenC hSN hSE
      (fun p hp hd => hEpr p hp (hd.trans (card_map_dvd E f)))
  have hnR : R.map f ≤ normalizer (B.map f : Set C) := (map_mono le_sup_left).trans hnE
  let e := cComponentTwoCoreQuotientEquiv hD
  have he : f = e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D)) := rfl
  have hnRq : R.map (QuotientGroup.mk' (pCore 2 D)) ≤
      normalizer (B.map (QuotientGroup.mk' (pCore 2 D)) : Set (D ⧸ pCore 2 D)) := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [map_normalizer_eq_of_bijective _ (f := e.toMonoidHom) e.bijective]
    simpa only [map_map, ← he] using hnR
  exact normalizes_of_twoCore_image K L T z v hK hSyl hn D hD hKD hLD
    (map_le_iff_le_comap.mp hnRq)

/-- Apply the structural reduction to the cover supplied by `exists_normal_cover`,
retaining explicit fixed-point and Hall inputs for independent use. The final
application `normalizes_of_A36` discharges both inputs. -/
theorem normalizes_of_A36_fixed_points_and_hall
    (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (D : Subgroup (plusActor K L T v)) (hD : D.IsCComponent)
    (hKD : K.subgroupOf (plusActor K L T v) ≤ D)
    (hLD : Lv L v ≤ D.map (plusActor K L T v).subtype)
    (hgen : solvableRadical D ⊔
      (K.subgroupOf (plusActor K L T v)).subgroupOf D = ⊤)
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (ha : A36Conclusion
      (D.map (QuotientGroup.mk' (pCore 2 (plusActor K L T v)))))
    (hfixed : let C := D.map (QuotientGroup.mk' (pCore 2 (plusActor K L T v)))
      ∀ S : Sylow 2 C, fittingSubgroup C ⊓ centralizer (S : Set C) ≤ center C)
    (hHall : let C := D.map (QuotientGroup.mk' (pCore 2 (plusActor K L T v)))
      ∀ (N B E : Subgroup C) (S : Sylow 2 C),
        N.Normal → Group.IsNilpotent N → Nat.Coprime 2 (Nat.card N) → N ⊔ B = ⊤ →
        (S : Subgroup C) ≤ normalizer (B : Set C) → (S : Subgroup C) ≤ E →
        Nat.Coprime (Nat.card N) (Nat.card E) → Group.IsSolvable E →
        N ⊓ centralizer (S : Set C) ≤ normalizer (B : Set C) →
        E ≤ normalizer (B : Set C)) : Lv L v ≤ normalizer (K : Set G) := by
  apply normalizes_of_intrinsic_rigidity K L T z v hK hSyl hn hL D hD hKD hLD hgen hc
  dsimp only
  intro S B E _ hB hSB hSE hE
  exact normalizes_of_fixed_points_and_hall ha S B E hB hSB hSE hE (hfixed S) hHall

/-- The normal-cover application with both rigidity inputs discharged. The
literal A.3.6 conclusion on D's image in A/O₂(A) is the only earlier
classification input retained here. The parent constructs D using
`exists_normal_cover` and supplies that conclusion from universal A.3.6. -/
theorem normalizes_of_A36
    (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (D : Subgroup (plusActor K L T v)) (hD : D.IsCComponent)
    (hKD : K.subgroupOf (plusActor K L T v) ≤ D)
    (hLD : Lv L v ≤ D.map (plusActor K L T v).subtype)
    (hgen : solvableRadical D ⊔
      (K.subgroupOf (plusActor K L T v)).subgroupOf D = ⊤)
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (ha : A36Conclusion
      (D.map (QuotientGroup.mk' (pCore 2 (plusActor K L T v))))) :
    Lv L v ≤ normalizer (K : Set G) := by
  apply normalizes_of_intrinsic_rigidity K L T z v hK hSyl hn hL D hD hKD hLD hgen hc
  dsimp only
  intro S B E hperfect hB hSB hSE hE
  let := pCore_isNilpotent (p := 2) (G := plusActor K L T v)
  exact normalizes_radical_supplement (pCore_quotient_pCore_eq_bot 2)
    (hD.map_quotient _) ha S B E hperfect hB hSB hSE hE

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.AmbientNormalization.SylowRigidity
