module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.CartanExclusion
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.Linear
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.Faithful
public import Mathlib.Data.Nat.GCD.Basic

/-!
# Restricting paired field exponents before recognition at the minimum

Let f be the exponent of the literal PSL₂ model of K/O₂(K), and let n
be the degree of the original natural module for L. A prime common to
2^f - 1 and 2^n - 1 supplies a nonidentity element of the actual odd Hall
factor A intersect K. Its Sylow exchange conjugator carries it into the
disjoint conjugate factor. The original SL₃/Sp₄ marking acts by one common
field power on the literal Ω₁(Oₚ(A)), so preserves its cyclic subgroup:
this is impossible. The equality gcd(2^n-1,2^f-1)=2^gcd(n,f)-1 therefore
forces n and f to be coprime in the paired case. The original bound
n ≤ n(H) ≤ f further gives n < f.

These restrictions feed the constructed component catalogue. If the
literal model instead has f = n, the upper and lower bounds prove n(H)=n,
and the component is the actual embedded O²(H), giving the full Conclusion
in that row. Arbitrary model exponents are never relabelled as n(H).

The original natural marking and preceding 11.0.4 residual/cubic clauses
remain explicit, produced by qt-d-1222-natural-local-geometry; final source
discharge remains with qt-d-1222-shadow-linear-geometry. The remaining
coprime PSL₂, Suzuki and normal higher-rank rows, recognition at n(H), and
the retained fixed-point construction remain this task's obligations.
This module does not assert unconditional 11.3.5 or 11.3.6.
Source: Aschbacher--Smith, 11.0.4 and 11.3.5(2), pp.760,771--772.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- A shared odd torus prime excludes exchange, at the independent model exponent.
The source field marking acts on the original Hall torsion and original actor. -/
theorem ComponentSeed.normal_of_overlap_common_prime (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hsolv : Group.IsSolvable (H ⊓ normalizer (L : Set G) : Subgroup G))
    (p : ℕ) (hp : p.Prime) (hd : p ∣ 2 ^ S.field.degree - 1)
    (hpOverlap : p ∣ Nat.card ((H ⊓ normalizer (L : Set G)) ⊓ K : Subgroup G))
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
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    : (K.subgroupOf H).Normal := by
  by_contra hn
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    have h2 : 2 ∣ 2 ^ S.field.degree := dvd_pow_self 2 S.field.degree_pos.ne'
    have hpow : 1 ≤ 2 ^ S.field.degree := Nat.one_le_pow _ _ (by decide)
    have hx := Nat.mod_eq_zero_of_dvd hd
    have hy := Nat.mod_eq_zero_of_dvd h2
    omega
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨A,hA,hHall,ho,t,htA,htK,hdis⟩ :=
    s.paired_hall_exchange_of_solvable h pr hc hs hn hsolv
  have hpA := s.paired_hall_factor_prime_dvd h pr hc hs hn A hA hHall p hp hp2 hpOverlap
  obtain ⟨x₀,hx₀⟩ := exists_prime_orderOf_dvd_card' (G := (A ⊓ K : Subgroup G)) p hpA
  let x : G := x₀
  have hx : x ∈ A ⊓ K := x₀.property
  have hox : orderOf x = p := (orderOf_coe x₀).trans hx₀
  have exclude (c : Coordinates D S.field)
      (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
        Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
      (hpower : Paired.primeTorsion A p ≤ cartanNormalizer T L →
        ∃ j : ℕ, ∀ x ∈ Paired.primeTorsion A p,
          (t : G)*x*(t : G)⁻¹ = x ^ (2 ^ j)) : False := by
    have hinner : H ⊓ L ≤ cartanNormalizer T L := by
      rw [cartanNormalizer_eq_intersection_normalizer]
      exact le_inf inf_le_right
        (solvable_overlap_normalizes_inner_sylow h.outside.1.1.2 hsolv halt)
    obtain ⟨X,hX,hAX⟩ := odd_subgroup_in_cartan c (A ⊓ L)
      (ho.of_dvd_nat (card_dvd_of_le inf_le_left))
      ((inf_le_inf_right L (hA.trans inf_le_left)).trans hinner)
    let e := (c.cartanTorusEquiv hX).toMonoidHom.comp (inclusion hAX)
    have he : Function.Injective e :=
      (c.cartanTorusEquiv hX).injective.comp (inclusion_injective hAX)
    let : IsMulCommutative (A ⊓ L : Subgroup G) :=
      .of_comm fun a b => he (by simp only [map_mul,mul_comm])
    have hQL := Paired.source_primeTorsion_le S A hA p hp hd halt hres hcubic
    have hxL := Paired.source_prime_order_mem S A hA p hp hd halt hres hcubic x hx.1 hox
    have hxQ := Paired.mem_primeTorsion_of_intersection A L p (hA.trans inf_le_right)
      x ⟨hx.1,hxL⟩ (hox ▸ pow_orderOf_eq_one x)
    obtain ⟨j,hj⟩ := hpower
      ((le_inf (Paired.primeTorsion_le A p) hQL).trans (hAX.trans hX.1))
    have hy : (t : G)*x*(t : G)⁻¹ ∈ A ⊓ K := by
      rw [hj x hxQ]
      exact (A ⊓ K).pow_mem hx _
    have hy' : (t : G)*x*(t : G)⁻¹ ∈
        (A ⊓ K).map (MulAut.conj (t : G)).toMonoidHom := mem_map_of_mem _ hx
    have hx1 : x = 1 := (MulAut.conj (t : G)).injective
      ((disjoint_def.mp hdis hy hy').trans (map_one _).symm)
    exact hp.ne_one (hox.symm.trans (hx1 ▸ orderOf_one))
  rcases hmark with hmL | hmL
  · obtain ⟨m⟩ := hmL
    exact exclude (.sl3 m)
      (.inl ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨m.groupEquiv⟩⟩)
      (fun hQ => Paired.source_primeTorsion_power_sl3 m A p hp2 hQ t htA)
  · obtain ⟨m⟩ := hmL
    exact exclude (.sp4 m)
      (.inr ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨m.groupEquiv⟩⟩)
      (fun hQ => Paired.source_primeTorsion_power_sp4 m A p hp2 hQ t htA)

/-- Apply the shared-prime contradiction to the original PSL₂ model. -/
theorem ComponentSeed.normal_of_linear_common_prime (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    {f : ℕ} (hf : 0 < f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
    (p : ℕ) (hp : p.Prime) (hd : p ∣ 2 ^ S.field.degree - 1)
    (hdf : p ∣ 2 ^ f - 1)
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
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    : (K.subgroupOf H).Normal := by
  by_contra hn
  exact hn (s.normal_of_overlap_common_prime h pr hc hs
    (s.paired_linear_overlap_solvable_of_model h pr hc hs hn hf hm) p hp hd
    (hdf.trans (s.paired_linear_overlap_torus_dvd_of_model h pr hc hs hn hf hm))
    hmark hres hcubic)

/-- A genuinely paired PSL₂ model has field exponent coprime to the original
natural-module degree. No equality with the generation minimum is used. -/
theorem ComponentSeed.paired_linear_field_coprime (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    {f : ℕ} (hf : 0 < f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
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
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    : Nat.Coprime S.field.degree f := by
  by_contra hcop
  have hpos : 0 < Nat.gcd S.field.degree f := Nat.gcd_pos_of_pos_left f S.field.degree_pos
  have hg : 2 ≤ Nat.gcd S.field.degree f := by
    change Nat.gcd S.field.degree f ≠ 1 at hcop
    omega
  have hpow : 4 ≤ 2 ^ Nat.gcd S.field.degree f :=
    pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) hg
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd
    (by omega : 2 ^ Nat.gcd S.field.degree f - 1 ≠ 1)
  rw [← Nat.pow_sub_one_gcd_pow_sub_one] at hpd
  exact hn (s.normal_of_linear_common_prime h pr hc hs hf hm p hp
    (hpd.trans (Nat.gcd_dvd_left _ _)) (hpd.trans (Nat.gcd_dvd_right _ _))
    hmark hres hcubic)

/-- Apply the new restriction to the actual paired component catalogue.
The PSL₂ alternatives retain their real model exponent and the true upper bound. -/
theorem ComponentSeed.paired_coprime_binary_models (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
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
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    : (∃ f : ℕ, S.field.degree < f ∧ ChapterE.generationParameter H ≤ f ∧
        Nat.Coprime S.field.degree f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∨
      (∃ m : ℕ, 1 ≤ m ∧ ChapterE.generationParameter H ≤ 2 * m + 1 ∧
        Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) := by
  rcases s.paired_binary_models h pr hc hs hn with ⟨f,hf,hu,hm⟩ | hsz
  · have hcop := s.paired_linear_field_coprime h pr hc hs hn (by omega) hm
      hmark hres hcubic
    have hlt : S.field.degree < f := by
      have hl := (degree_le_parameter h pr hc hs).trans hu
      have hne : S.field.degree ≠ f := by
        intro he
        have hh : Nat.gcd S.field.degree f = 1 := hcop
        rw [← he, Nat.gcd_self] at hh
        have := S.nonbinary
        omega
      exact lt_of_le_of_ne hl hne
    exact .inl ⟨f,hlt,hu,hcop,hm⟩
  · exact .inr hsz

/-- If the model exponent shares a nontrivial factor with n, the selected
component is the literal ambient two-residual; its given field is retained. -/
theorem ComponentSeed.eq_residual_of_linear_not_coprime (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    {f : ℕ} (hf : 0 < f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
    (hcop : ¬ Nat.Coprime S.field.degree f)
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
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    : K = residual H := by
  apply s.normal_iff_eq_residual.mp
  by_contra hn
  exact hcop (s.paired_linear_field_coprime h pr hc hs hn hf hm hmark hres hcubic)

/-- When the literal PSL₂ model has the source field, the original lower
bound and the model upper bound prove n(H)=n, and give the full conclusion. -/
theorem ComponentSeed.conclusion_of_matching_linear_model (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ S.field.degree))
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
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    : Conclusion S H := by
  have hf : 2 ≤ S.field.degree := by have := S.nonbinary; omega
  have hk := Nat.le_antisymm (s.linear_parameter_le h pr hc hs hf hm)
    (degree_le_parameter h pr hc hs)
  have he := s.eq_residual_of_linear_not_coprime h pr hc hs S.field.degree_pos hm
    (by
      intro hcop
      have hh : Nat.gcd S.field.degree S.field.degree = 1 := hcop
      rw [Nat.gcd_self] at hh
      have := S.nonbinary
      omega)
    hmark hres hcubic
  exact assemble h ⟨K,s.component,s.span,hk.symm ▸ hm,fun _ => he⟩ hk

/-- The original counterexample yields a faithful maximal overcomponent and
this sharpened paired catalogue. The normal branch remains a recognition task. -/
theorem exists_componentSeed_normal_or_coprime_models
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
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
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    : ∃ K J : Subgroup G, ComponentSeed T H K ∧ K ≤ J ∧
      J ∈ Chapter1.LStar G (T : Subgroup G) ∧
      J ∈ MainForward.faithfulLocalComponents T ∧
      ¬ J ≤ normalizer (L : Set G) ∧ ⁅sourceZ T,J⁆ ≠ ⊥ ∧
      ((K.subgroupOf H).Normal ∨
        (∃ f : ℕ, S.field.degree < f ∧ ChapterE.generationParameter H ≤ f ∧
          Nat.Coprime S.field.degree f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∨
        (∃ m : ℕ, 1 ≤ m ∧ ChapterE.generationParameter H ≤ 2 * m + 1 ∧
          Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))) := by
  obtain ⟨K,J,s,hKJ,hJ,hfaith,ho,hm⟩ := exists_componentSeed_with_faithful_maximal h pr hc hs
  refine ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,?_⟩
  by_cases hn : (K.subgroupOf H).Normal
  · exact .inl hn
  · exact .inr (s.paired_coprime_binary_models h pr hc hs hn hmark hres hcubic)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
