module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.FixedPoints

/-!
# Excluding paired components using the original Cartan action

Recognition at the actual generation minimum gives the source Hall prime
and its exchanged disjoint factors. HallProduct constructs the whole Hall
product, and FixedPoints chooses the prime to prove square centralization
from the original common field action. The same Sylow actor has both a
moved prime-order point and a nonidentity fixed diagonal on the literal
Hall p-torsion. The common-power dichotomy gives the contradiction.

This proves normality relative to H and feeds RankOneReduction through
the seed residual identity. No whole-Hall abelianness, square-action or
fixed-point callback remains. Recognition at generationParameter H and
the genuine preceding 11.0.4 clauses remain explicit. Their discharge and
the doubled-parameter exclusion are still needed for unconditional
11.3.5--6; qt-d-1222-shadow-linear-geometry retains final source assembly.
Source: Aschbacher--Smith, 11.3.5(2), printed pp.771--772.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- Under recognition at the actual generation minimum, the paired case
is excluded by the original Hall prime and the actual SL3/Sp4 marking.
No Cartan-coordinate, square-action or whole-Hall abelianness callback remains. -/
theorem ComponentSeed.normal_of_paired_cartan (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ ChapterE.generationParameter H))
    (hk : ChapterE.generationParameter H = S.field.degree ∨
      ChapterE.generationParameter H = 2 * S.field.degree)
    (hmark : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∨
      Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))))
    (hres : ∀ r : ℕ, r.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          r ∣ 2 ^ S.field.degree - 1 ∧ 3 < r) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          r ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual r (normalizer (L : Set G)) =
        L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    (K.subgroupOf H).Normal := by
  by_contra hn
  obtain ⟨p,hp,_,_,A,_,_,hab,t,_,_,_,⟨x,hx,_,hmx⟩,⟨z,hz,hz1,hfix⟩,j,hj⟩ :=
    s.exists_paired_hall_mixed_action h pr hc hs hn hm hk hmark hres hcubic
  let : Fact p.Prime := ⟨hp⟩
  let := hab
  let : IsMulCommutative (A ⊓ K : Subgroup G) := .of_setLike_mul_comm
    (fun a ha b hb => setLike_mul_comm ha.1 hb.1)
  have hxQ : x ∈ Paired.primeTorsion A p := by
    obtain ⟨hxB,hxp⟩ := (Paired.mem_primeTorsion_iff (A ⊓ K) p x).mp hx
    exact (Paired.mem_primeTorsion_iff A p x).mpr ⟨hxB.1,hxp⟩
  rcases Paired.primeTorsion_power_dichotomy A p (2^j) t hj with hall | hnone
  · apply hmx
    have he := mem_centralizer_singleton_iff.mp (hall hxQ)
    rw [←he,mul_inv_cancel_right]
  · apply hz1
    apply mem_bot.mp
    rw [←hnone]
    exact ⟨hz,mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp hfix).symm⟩

/-- Recognition of the seed at the true generation minimum now feeds the
existing 11.3.5/11.3.6 assembly boundary. The paired-collapse clause is
proved here; the model-recognition input remains a separate local obligation. -/
theorem ComponentSeed.rankOneReduction_of_model (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ ChapterE.generationParameter H))
    (hmark : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∨
      Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))))
    (hres : ∀ r : ℕ, r.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          r ∣ 2 ^ S.field.degree - 1 ∧ 3 < r) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          r ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual r (normalizer (L : Set G)) =
        L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) : RankOneReduction S H := by
  refine ⟨K,s.component,s.span,hm,fun hk => ?_⟩
  exact s.normal_iff_eq_residual.mp
    (s.normal_of_paired_cartan h pr hc hs hm hk hmark hres hcubic)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
