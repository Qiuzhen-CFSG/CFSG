module
public import Glauberman.PushingUpOriginalMainQuotient
public import Glauberman.PushingUpExactBounds
public import Glauberman.PushingUpInvolutionGeneration
public import Glauberman.PushingUpNaturalChief
public import Theory.GroupTheory.RankOneCentralChiefPassage

/-!
# Niles Theorem B reduced to Main Hypothesis structure

The original source hypotheses construct the actual central-chief quotient
of Theorem 7.2. Applying the Main Hypothesis structure theorem there and
lifting through the kernel gives exact Sylow class two, exponent four and one
noncentral chief factor. The separately proved original omega action identifies
that factor equivariantly with the natural module, and equal quotient orders
make its action factor through the literal original H/O2(H).

The Main Hypothesis structure theorem remains an explicit premise here. This
module proves the complete final implication; it does not assert that the
separate Sections 4–6 structure proof has been completed.

Source: Niles, *Pushing-up in finite groups* (1979), Theorem B, pp.28, 62.
-/

public section
open Subgroup NilesRankOneKernel Theory.GroupTheory NoncentralChiefRefinement
namespace Glauberman
universe u v
variable {H : Type u} {F : Type v} [Group H] [Finite H] [Field F] [Finite F]

/-- Applying a Main Hypothesis structure theorem to the quotient constructed
from the original hypotheses discharges every reduction input. -/
theorem original_psl2_four_structure_of_main_hypothesis
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoCharacteristicNormal (S : Subgroup H))
    (hmain : ∀ (X : Type u) [Group X] [Finite X] (P : Sylow 2 X)
      (L : Subgroup X) [L.Normal],
      ((X ⧸ L) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) →
      generalizedFitting X = pCore 2 X →
      Order.HasUniqueMaximalOver (P : Subgroup X) ⊤ →
      (∃ β : MulAut P, NoInvariantNormal (P : Subgroup X) β) →
      Group.nilpotencyClass P = 2 ∧ Monoid.exponent P = 4 ∧
        Nonempty ((X ⧸ pCore 2 X) ≃* Representation.SL2FourNatural.SL) ∧
        ∃ t : SeriesOn (pCore 2 X), t.noncentralCount = 1) :
    Group.nilpotencyClass S = 2 ∧ Monoid.exponent S = 4 ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* Representation.SL2FourNatural.SL) ∧
      ∀ t : SeriesOn (pCore 2 H), t.noncentralCount = 1 := by
  obtain ⟨α,s,hc,hN,hNK,⟨eN⟩,hfN,huN,β,hβ⟩ :=
    original_psl2_four_exists_main_quotient hF S hu K e hf hno
  let N := (invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype
  let π := QuotientGroup.mk' N
  let P := S.mapSurjective (QuotientGroup.mk'_surjective N)
  let _ : (K.map π).Normal := Subgroup.Normal.map (inferInstance : K.Normal) π
    (QuotientGroup.mk'_surjective N)
  obtain ⟨hcl,hex,he,ht⟩ := hmain (H ⧸ N) P (K.map π) (eN.trans e) hfN huN ⟨β,hβ⟩
  exact structure_of_central_chief_quotient S hno N hN s hc hcl hex he ht

/-- The original natural chief factor is marked by the actual two-core
quotient once the Main Hypothesis structure clauses have been supplied. -/
theorem original_psl2_four_natural_factors_of_structure
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoCharacteristicNormal (S : Subgroup H))
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Representation.SL2FourNatural.SL))
    (hcount : ∀ t : SeriesOn (pCore 2 H), t.noncentralCount = 1) :
    ∃ eQ : (H ⧸ pCore 2 H) ≃* Representation.SL2FourNatural.SL,
      K = pCore 2 H ∧
      ∀ s : SeriesOn (pCore 2 H), s.noncentralCount = 1 ∧
        ∀ i : Fin s.series.length, ¬ s.Central i →
          Nat.card (s.Factor i) = 16 ∧
          ∃ f : s.Factor i ≃* Multiplicative Representation.SL2FourNatural.V,
            ∀ h x, (f (s.action i h x)).toAdd =
              Representation.specialLinearNatural 2
                (eQ (QuotientGroup.mk' (pCore 2 H) h)) (f x).toAdd := by
  obtain ⟨q,hq,hk,_,_,hc,_,hfactor⟩ :=
    original_psl2_four_natural_chief_data hF S hu K e hf hno
  obtain ⟨e0⟩ := he
  have hQ : pCore 2 H ≤ q.ker := by
    rw [hk,← omegaAction_kernel]
    exact twoCore_le_omegaAction_kernel
  have hqker := ker_eq_pCore_of_quotient_equiv q hq hQ e0
  have hK : K = pCore 2 H := by
    have hh := (original_psl2_four_omegaAction_kernel_eq hF S hu K e hf hno).1
    rw [omegaAction_kernel] at hh
    exact hh.symm.trans (hk.symm.trans hqker)
  let eQ : (H ⧸ pCore 2 H) ≃* Representation.SL2FourNatural.SL :=
    QuotientGroup.liftEquiv (pCore 2 H) hq hqker.symm
  refine ⟨eQ,hK,?_⟩
  intro s
  refine ⟨hcount s,?_⟩
  intro i hi
  obtain ⟨⟨a⟩,_,f,hf⟩ := hfactor s (hcount s) i hi
  refine ⟨(Nat.card_congr a.equiv.toEquiv).trans hc,f,?_⟩
  intro h x
  rw [show eQ (QuotientGroup.mk' (pCore 2 H) h) = q h from
    QuotientGroup.liftEquiv_mk (pCore 2 H) hq hqker.symm h]
  exact hf h x

/-- The complete p=2, q=4 conclusion of Niles Theorem B, conditional only on
its separately proved Main Hypothesis structure theorem. The unique factor
is marked for the literal original H/O2(H), not merely by its order. -/
theorem niles_theoremB_four_of_main_hypothesis
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoCharacteristicNormal (S : Subgroup H))
    (hmain : ∀ (X : Type u) [Group X] [Finite X] (P : Sylow 2 X)
      (L : Subgroup X) [L.Normal],
      ((X ⧸ L) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) →
      generalizedFitting X = pCore 2 X →
      Order.HasUniqueMaximalOver (P : Subgroup X) ⊤ →
      (∃ β : MulAut P, NoInvariantNormal (P : Subgroup X) β) →
      Group.nilpotencyClass P = 2 ∧ Monoid.exponent P = 4 ∧
        Nonempty ((X ⧸ pCore 2 X) ≃* Representation.SL2FourNatural.SL) ∧
        ∃ t : SeriesOn (pCore 2 X), t.noncentralCount = 1) :
    Group.nilpotencyClass S = 2 ∧ Monoid.exponent S = 4 ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∧
      ∃ eQ : (H ⧸ pCore 2 H) ≃* Representation.SL2FourNatural.SL,
        K = pCore 2 H ∧
        ∀ s : SeriesOn (pCore 2 H), s.noncentralCount = 1 ∧
          ∀ i : Fin s.series.length, ¬ s.Central i →
            Nat.card (s.Factor i) = 16 ∧
            ∃ f : s.Factor i ≃* Multiplicative Representation.SL2FourNatural.V,
              ∀ h x, (f (s.action i h x)).toAdd =
                Representation.specialLinearNatural 2
                  (eQ (QuotientGroup.mk' (pCore 2 H) h)) (f x).toAdd := by
  obtain ⟨hcl,hex,he,hcount⟩ :=
    original_psl2_four_structure_of_main_hypothesis hF S hu K e hf hno hmain
  obtain ⟨eQ,hK,hnatural⟩ :=
    original_psl2_four_natural_factors_of_structure hF S hu K e hf hno he hcount
  let _ : Fintype F := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa [Nat.card_eq_fintype_card] using hF)
  refine ⟨hcl,hex,?_,eQ,hK,hnatural⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hK.symm).trans e).trans
    (Theory.PSL2.sl2QuotientEquiv F).symm⟩

/-- The same final implication needs only the upper class and power bounds
from the Main Hypothesis producer; the original natural action proves both
bounds are sharp. -/
theorem niles_theoremB_four_of_main_bounds
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoCharacteristicNormal (S : Subgroup H))
    (hmain : ∀ (X : Type u) [Group X] [Finite X] (P : Sylow 2 X)
      (L : Subgroup X) [L.Normal],
      ((X ⧸ L) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) →
      generalizedFitting X = pCore 2 X →
      Order.HasUniqueMaximalOver (P : Subgroup X) ⊤ →
      (∃ β : MulAut P, NoInvariantNormal (P : Subgroup X) β) →
      Group.nilpotencyClass P ≤ 2 ∧ (∀ p : P, p ^ 4 = 1) ∧
        Nonempty ((X ⧸ pCore 2 X) ≃* Representation.SL2FourNatural.SL) ∧
        ∃ t : SeriesOn (pCore 2 X), t.noncentralCount = 1) :
    Group.nilpotencyClass S = 2 ∧ Monoid.exponent S = 4 ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∧
      ∃ eQ : (H ⧸ pCore 2 H) ≃* Representation.SL2FourNatural.SL,
        K = pCore 2 H ∧
        ∀ s : SeriesOn (pCore 2 H), s.noncentralCount = 1 ∧
          ∀ i : Fin s.series.length, ¬ s.Central i →
            Nat.card (s.Factor i) = 16 ∧
            ∃ f : s.Factor i ≃* Multiplicative Representation.SL2FourNatural.V,
              ∀ h x, (f (s.action i h x)).toAdd =
                Representation.specialLinearNatural 2
                  (eQ (QuotientGroup.mk' (pCore 2 H) h)) (f x).toAdd := by
  apply niles_theoremB_four_of_main_hypothesis hF S hu K e hf hno
  intro X _ _ P L _ eL hfX huP hb
  obtain ⟨hcl,hpow,he,ht⟩ := hmain X P L eL hfX huP hb
  obtain ⟨β,hβ⟩ := hb
  obtain ⟨hcl',hex⟩ := original_psl2_four_exact_of_bounds
    hF P huP L eL hfX hβ.noCharacteristicNormal hcl hpow
  exact ⟨hcl',hex,he,ht⟩

/-- The elementary Sylow center already proves fourth powers vanish once
class at most two holds, leaving only class, quotient and chief count as the
Main Hypothesis structure inputs. -/
theorem niles_theoremB_four_of_main_class_chief
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoCharacteristicNormal (S : Subgroup H))
    (hmain : ∀ (X : Type u) [Group X] [Finite X] (P : Sylow 2 X)
      (L : Subgroup X) [L.Normal],
      ((X ⧸ L) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) →
      generalizedFitting X = pCore 2 X →
      Order.HasUniqueMaximalOver (P : Subgroup X) ⊤ →
      (∃ β : MulAut P, NoInvariantNormal (P : Subgroup X) β) →
      Group.nilpotencyClass P ≤ 2 ∧
        Nonempty ((X ⧸ pCore 2 X) ≃* Representation.SL2FourNatural.SL) ∧
        ∃ t : SeriesOn (pCore 2 X), t.noncentralCount = 1) :
    Group.nilpotencyClass S = 2 ∧ Monoid.exponent S = 4 ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∧
      ∃ eQ : (H ⧸ pCore 2 H) ≃* Representation.SL2FourNatural.SL,
        K = pCore 2 H ∧
        ∀ s : SeriesOn (pCore 2 H), s.noncentralCount = 1 ∧
          ∀ i : Fin s.series.length, ¬ s.Central i →
            Nat.card (s.Factor i) = 16 ∧
            ∃ f : s.Factor i ≃* Multiplicative Representation.SL2FourNatural.V,
              ∀ h x, (f (s.action i h x)).toAdd =
                Representation.specialLinearNatural 2
                  (eQ (QuotientGroup.mk' (pCore 2 H) h)) (f x).toAdd := by
  apply niles_theoremB_four_of_main_bounds hF S hu K e hf hno
  intro X _ _ P L _ eL hfX huP hb
  obtain ⟨hcl,he,ht⟩ := hmain X P L eL hfX huP hb
  obtain ⟨β,hβ⟩ := hb
  let _ := P.isPGroup'.isNilpotent
  have hbot : (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hcl
  have hcomm : _root_.commutator P ≤ center P := by
    apply commutator_top_right_eq_bot_iff_le_center.mp
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.top_lowerCentralSeries_one] at hbot
    exact hbot
  exact ⟨hcl,original_psl2_four_pow_four_of_class_two hF P β huP L eL hfX hβ hcomm,he,ht⟩

end Glauberman
