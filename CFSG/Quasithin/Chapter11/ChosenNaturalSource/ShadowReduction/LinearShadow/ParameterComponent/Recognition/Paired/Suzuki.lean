module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.ModelCartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.FieldCoprime
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Suzuki

/-!
# Excluding the original paired Suzuki component

The normalizer of a Sylow two-subgroup of Sz(2^(2m+1)) has order
q²(q−1). Its q−1 divisor lifts through the original minimal-parabolic
quotient to H ∩ N_G(L) ∩ K. The genuine Hall subgroup and the same Sylow
exchange actor then give a nonidentity prime-order point in A ∩ K.
The original natural Cartan action preserves its cyclic subgroup, whereas
the exchange takes it into the disjoint conjugate Hall factor.

Thus the shared-prime obstruction applies to Suzuki as well as PSL₂.
The checked model-field recognition gives k=n for the paired Suzuki row,
so a prime of 2^n−1 excludes it. Together with the PSL₂ Cartan argument,
every original component seed is normal in H and hence is the literal
embedded O²(H). The final catalogue constructs that residual and its
faithful maximal overcomponent, with the higher-rank star images retained.

The preceding odd-kernel normalizer, global-s and residual/cubic clauses
remain explicit inputs with their existing local-geometry producers.
The normal Suzuki, unitary and rank-two FF exclusions remain necessary
for 11.3.5(1); this module does not assert the full parameter/component result.
Source: Aschbacher--Smith, 11.0.4 and 11.3.5, printed pp.760,771--772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
open LocalGeometry ChapterB.QuasisimpleSource
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels

private theorem suzuki_normalizer_card {X : Type*} [Group X] [Finite X]
    (P : Sylow 2 X) {m : ℕ} (hm : 0 < m)
    (em : Nonempty (X ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    Nat.card (normalizer (P : Set X)) =
      (2^(2*m+1))^2 * (2^(2*m+1)-1) := by
  obtain ⟨e⟩ := em
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have he : (normalizer (P : Set X)).map e.toMonoidHom =
      normalizer (Q : Set (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) := by
    change (normalizer ((P : Subgroup X) : Set X)).map _ = _
    rw [map_normalizer_eq_of_bijective _ e.bijective]
    rfl
  obtain ⟨g,hg⟩ := ChapterF.Source.suzuki_sylow_normalizer_eq_conjugate_borel m Q
  rw [←card_map_of_injective (K := normalizer (P : Set X)) (f := e.toMonoidHom) e.injective,
    he,hg,card_map_of_injective (MulAut.conj g).injective]
  exact BenderSuzuki.MatrixGroups.suzukiBorelSubgroup_card m hm

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H K : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The Suzuki torus divisor in the literal component overlap. -/
theorem ComponentSeed.paired_suzuki_overlap_torus_dvd (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal) {m : ℕ} (hm : 0 < m)
    (em : Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    2^(2*m+1)-1 ∣ Nat.card ((H ⊓ normalizer (L : Set G)) ⊓ K : Subgroup G) := by
  apply s.paired_rankOne_overlap_divisor h pr hc hs hn (.inr ⟨m,em⟩) (2^(2*m+1)-1)
  intro Q
  rw [suzuki_normalizer_card Q hm em]
  exact dvd_mul_left _ _

/-- A common torus prime excludes exchange in the Suzuki row, without
assuming equality of the natural and model exponents. -/
theorem ComponentSeed.normal_of_suzuki_common_prime (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    {m : ℕ} (hm : 0 < m)
    (em : Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
    (p : ℕ) (hp : p.Prime) (hd : p ∣ 2 ^ S.field.degree - 1)
    (hdf : p ∣ 2 ^ (2*m+1) - 1)
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
    (s.paired_binary_rankOne_overlap_solvable h pr hc hs hn (.inr ⟨m,em⟩)) p hp hd
    (hdf.trans (s.paired_suzuki_overlap_torus_dvd h pr hc hs hn hm em))
    hmark hres hcubic)

/-- Both paired source models are impossible. Normality is relative to H,
and the Hall exchange is excluded before using the residual identification. -/
theorem ComponentSeed.normal_of_source_odd_kernel (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : LocalGeometry.Coordinates D S.field} (F : InvariantFlag c)
    (hpoint : c.binarySubspace (F.space 0) = U₁)
    (hs : @ChapterE.globalS G _ V D.elementary = WeakClosure.Parameters.naturalParameter D S c)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
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
  have hgen := WeakClosure.Generation.Doubling.conclusion_of_automizer_bounds D S
    hcontrol (WeakClosure.Generation.Automizer.automizerBounds D S) h.outside
  obtain ⟨hmark,hsn,_⟩ := source_marking_and_parameter h pr hc c hs hgen
  have hs' : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary := hsn.symm.le
  obtain ⟨hk,hmodels⟩ := s.paired_binary_models_at_parameter h pr hc hs' hcontrol F hpoint hn
  rcases hmodels with hlin | ⟨hkn,m,hm,hkm,em⟩
  · apply hn
    exact s.normal_of_paired_cartan h pr hc hs' hlin
      (hk.imp id (fun hh => hh.1)) hmark hres hcubic
  · have hdiv := s.paired_suzuki_overlap_torus_dvd h pr hc hs' hn (by omega) em
    rw [←hkm] at hdiv
    obtain ⟨p,hp,_,hd,_⟩ := source_prime_divisor_of_parameter S (.inl hkn) hdiv
    apply hn
    apply s.normal_of_suzuki_common_prime h pr hc hs' (by omega) em p hp hd
    · simpa only [←hkm,hkn] using hd
    · exact hmark
    · exact hres
    · exact hcubic

/-- The original source catalogue now has a normal residual component in
all surviving rows. Its faithful maximal overcomponent and the literal
star image are constructed, and every model uses generationParameter H. -/
theorem exists_residual_component_with_models_at_parameter
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : LocalGeometry.Coordinates D S.field} (F : InvariantFlag c)
    (hpoint : c.binarySubspace (F.space 0) = U₁)
    (hs : @ChapterE.globalS G _ V D.elementary = WeakClosure.Parameters.naturalParameter D S c)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    (hres : ∀ r : ℕ, r.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          r ∣ 2 ^ S.field.degree - 1 ∧ 3 < r) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          r ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual r (normalizer (L : Set G)) =
        L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    let P := T.subtype h.outside.1.1.2
    let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
    let k := ChapterE.generationParameter H
    Source.NormalComponentIn H (residual H) ∧
      H = residual H ⊔ (T : Subgroup G) ∧
      ¬ residual H ≤ normalizer (L : Set G) ∧
      ∃ J : Subgroup G, ComponentSeed T H (residual H) ∧ residual H ≤ J ∧
        J ∈ Chapter1.LStar G (T : Subgroup G) ∧
        J ∈ MainForward.faithfulLocalComponents T ∧
        ¬ J ≤ normalizer (L : Set G) ∧ ⁅sourceZ T,J⁆ ≠ ⊥ ∧
        (k = S.field.degree ∨ (k = 2*S.field.degree ∧ WeakClosure.Generation.DoubledNatural D S)) ∧
        (let I := sourceImage (ChapterB.minimalParabolicMax P hP) ((residual H).subgroupOf H)
         ClassicalGroup.IsPSL I 2 (2^k) ∨ ClassicalGroup.IsPSU I 3 (2^k) ∨
           ClassicalGroup.IsPSL I 3 (2^k) ∨ ClassicalGroup.IsPSp I 2 (2^k) ∨
           (k = S.field.degree ∧ ∃ m : ℕ, 1 ≤ m ∧ k = 2*m+1 ∧
             Nonempty (I ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))) := by
  have hgen := WeakClosure.Generation.Doubling.conclusion_of_automizer_bounds D S
    hcontrol (WeakClosure.Generation.Automizer.automizerBounds D S) h.outside
  obtain ⟨_,hsn,_⟩ := source_marking_and_parameter h pr hc c hs hgen
  have hs' : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary := hsn.symm.le
  obtain ⟨K,J,s,hKJ,hJ,hfaith,ho,hm⟩ := exists_componentSeed_with_faithful_maximal h pr hc hs'
  have hn := s.normal_of_source_odd_kernel h pr hc F hpoint hs hcontrol hres hcubic
  have he := s.normal_iff_eq_residual.mp hn
  subst K
  obtain ⟨hk,hmodels⟩ := s.normal_binary_models_at_parameter h pr hc hs' hcontrol F hpoint hn
  refine ⟨⟨s.component,hn⟩,s.supplement.symm,s.outside h,J,s,hKJ,hJ,hfaith,ho,hm,hk,?_⟩
  rcases hmodels with hlin | huni | hthree | hsp | ⟨m,hm,hkm,em⟩
  · exact .inl hlin
  · exact .inr (.inl huni)
  · exact .inr (.inr (.inl hthree))
  · exact .inr (.inr (.inr (.inl hsp)))
  · have hkn : ChapterE.generationParameter H = S.field.degree := by
      rcases hk with hk | ⟨hk,_⟩ <;> omega
    exact .inr (.inr (.inr (.inr ⟨hkn,m,hm,hkm,em⟩)))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
