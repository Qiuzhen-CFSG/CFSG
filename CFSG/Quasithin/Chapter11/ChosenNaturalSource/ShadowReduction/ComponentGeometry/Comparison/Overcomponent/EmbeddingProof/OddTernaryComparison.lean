module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.OddTernarySeven
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification.OddExtensions
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.SpecificGroups.G2Even.TwoRank
public import Theory.SpecificGroups.Triality.StandardTwoRank
public import Theory.SpecificGroups.SU3.PrimeCentralKernel
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder
public import Theory.GroupTheory.PerfectSmallNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.SpecificGroups.Rudvalis.Model.Order

/-!
# The complete odd ternary proper-pair comparison on the chosen flag

The faithful point quotient has two-rank at most two. The full 11.1.1
point catalogue therefore loses all characteristic-two Lie rows. The
order-eight Sylow obstruction excludes A₇ and its triple cover. Quintic
ternary order divisibility removes every exceptional-prime and sporadic
row; quasisimplicity excludes the odd extensions. A remaining ternary
point quotient would give a proper subgroup of index at most three in a
perfect group, a contradiction. Properness here is preserved through the
original containing two-core projection.

Thus the point quotient is nonquasisimple. OddTernaryPairs now supplies
the literal elementary-plane-by-SL₂(5) embedding, forces p = 5, and excludes
the unitary sign, without a point-quasisimplicity branch assumption.
Both special and projective containing carriers were retained throughout.

Earlier geometry and the original seed marking retain final discharge by
qt-d-1222-shadow-components. Other proper pairs, inner radical placement,
strict omega-center containment and final Kz = K remain with
qt-d-1222-shadow-component-comparison; the positive normalized-module input
retains qt-d-1222-normalized-nonff. This is not full source 11.4.2.
Source: Aschbacher--Smith 11.1.1 and 11.4.2, printed pp.761,776--777.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings Chapter1.Section02.LocalModels

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}

/-- The actual point quotient in either signed ternary carrier at five
has two-rank at most two, through its faithful containing projection. -/
theorem ofFlag_odd_ternary_point_twoRank
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hle : (ofFlag S f X z H).Kz ≤ J)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : IsPSLSign (J ⧸ pCore 2 J) u 3 p ∨ IsSLSign (J ⧸ pCore 2 J) u 3 p) :
    primeRank 2 ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ≤ 2 := by
  obtain ⟨hp5,_,⟨i,hi,_⟩,_⟩ :=
    ofFlag_odd_ternary_faithful_point_quotient S f X z H h hne hlinear h1132 e hJ hle hp ho u hm
  subst p
  exact (Theory.GroupTheory.primeRank_le_of_injective 2 i hi).trans (odd_three_two_rank (by decide : Odd 5) u hm)

private theorem fieldFour_lie_twoRank
    {A : Type*} [Group A] [Finite A]
    (hm : LocalGeometry.Components.LieOvergroup A 2) : 3 ≤ primeRank 2 A := by
  cases hm with
  | sl3 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [primeRank_equiv 2 e]
    have hh := primeRank_quotient_le_of_coprime 2 (center SL(3,F))
      (Nat.coprime_two_left.mpr (Matrix.SL3.odd_card_center F))
    change primeRank 2 PSL(3,F) ≤ _ at hh
    rw [Matrix.PSL3Even.two_rank F (by decide : 0 < 2) hF] at hh
    omega
  | psl3 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [primeRank_equiv 2 e,Matrix.PSL3Even.two_rank F (by decide : 0 < 2) hF]
    decide
  | sp4 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [primeRank_equiv 2 e,Theory.SpecificGroups.SymplecticFour.EvenTwoRank.rank hF (by decide)]
    decide
  | g2 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [primeRank_equiv 2 e,Atlas.G2.EvenTwoRank.two_rank F hF]
    decide
  | ree m hm he _ => omega
  | triality hm =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff A 2 (by decide)).mp hm
    rw [primeRank_equiv 2 e]
    exact le_trans (by decide : 3 ≤ 3 * 2)
      (Triality.Standard.TwoRank.twoRank_ge_three_mul 2 (by decide))
  | trialityCube m hm he _ => omega

/-- The full original point catalogue in an odd ternary proper container
reduces to its field-four rows. Both alternating-seven rows are excluded,
and the remaining point quotient has rank at most two. No shortened
proper-pair catalogue is assumed. -/
theorem ofFlag_odd_ternary_point_catalogue
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : IsPSLSign (J ⧸ pCore 2 J) u 3 p ∨ IsSLSign (J ⧸ pCore 2 J) u 3 p) :
    S.field.degree = 2 ∧
      LocalGeometry.Components.FieldFourOvergroup
        ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ∧
      primeRank 2 ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ≤ 2 ∧
      ¬ (IsAlternating ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) 7 ∨
        IsAlternatingCover ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) 7) := by
  have hn := (ofFlag_proper_overcomponent_fieldFour S f X z H h hne hlinear h1132 e hJ hlt).1
  have hr := ofFlag_odd_ternary_point_twoRank S f X z H h hne hlinear h1132 e hJ hlt.le hp ho u hm
  refine ⟨hn,?_,hr,ofFlag_not_alternating_seven_point_in_odd_ternary
    S f X z H h hne hlinear h1132 e hJ hlt.le hp ho u hm⟩
  cases ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl with
  | equal he =>
    exact ((h.strict_comparison (fixed_and_transitive D S _ hlinear h1132).1 hne).2.1.ne he).elim
  | lie hm =>
    rw [hn] at hm
    have hh := fieldFour_lie_twoRank hm
    omega
  | four _ hm => exact hm

private theorem linear_five_card {A : Type*} [Group A]
    (hm : ClassicalGroup.IsPSL A 3 5 ∨ IsSL A 3 5) : Nat.card A = 372000 := by
  rcases hm with hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective F,hF]
    norm_num
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let b := Matrix.SL3.equivProjectiveOfCenterEqBot F
      ((Matrix.SL3.center_eq_bot_iff_card_mod_three F).mpr (by rw [hF]; decide))
    rw [Nat.card_congr (e.trans b).toEquiv,Matrix.PSL3.LinearThree.card_projective F,hF]
    norm_num

private theorem unitary_five_projective_card
    {F : Type*} [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (hF : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5) :
    Nat.card (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) = 126000 := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 5 1 (by decide)
    (by simpa using hF) (by simpa using hconj)
  rw [Representation.SU3.BinaryDegree.card_projective J hF (by simpa using hf)]
  norm_num

/-- The two quintic signed ternary orders bound every actual subgroup.
Special unitary covers retain their central kernel of order dividing three. -/
theorem odd_ternary_five_card_bounds {A : Type*} [Group A] [Finite A]
    (u : Bool) (hm : IsPSLSign A u 3 5 ∨ IsSLSign A u 3 5) :
    (Nat.card A ∣ 372000 ∨ Nat.card A ∣ 378000) ∧
      126000 ≤ Nat.card A ∧ Nat.card A ≤ 378000 := by
  cases u with
  | false => rw [linear_five_card hm]; norm_num
  | true =>
    rcases hm with hm | hm
    · obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
      rw [Nat.card_congr e.toEquiv,unitary_five_projective_card J hF hconj]
      norm_num
    · obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
      have he := J.specialToProjective.ker.card_mul_index
      rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr J.specialToProjective_surjective,
        card_top,unitary_five_projective_card J hF hconj] at he
      have hd := J.card_specialToProjective_ker_dvd_three
      have hpos := Nat.card_pos (α := J.specialToProjective.ker)
      rw [Nat.card_congr e.toEquiv,←he]
      refine ⟨.inr ?_,?_,?_⟩
      · exact mul_dvd_mul_right hd 126000
      · nlinarith
      · have := Nat.le_of_dvd (by decide : 0 < 3) hd
        nlinarith

private theorem exceptional_prime_not_divisor {p : ℕ} (hp : Source.ExceptionalPrime p)
    (hd : p ∣ 372000 ∨ p ∣ 378000) : False := by
  have hh : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 31 := by
    rcases hd with hd | hd
    · rw [show 372000 = 2^5*3*5^3*31 by decide] at hd
      simp only [hp.1.dvd_mul] at hd
      rcases hd with ((hd | hd) | hd) | hd
      · exact .inl ((Nat.prime_dvd_prime_iff_eq hp.1 (by decide)).mp (hp.1.dvd_of_dvd_pow hd))
      · exact .inr (.inl ((Nat.prime_dvd_prime_iff_eq hp.1 (by decide)).mp hd))
      · exact .inr (.inr (.inl ((Nat.prime_dvd_prime_iff_eq hp.1 (by decide)).mp (hp.1.dvd_of_dvd_pow hd))))
      · exact .inr (.inr (.inr (.inr ((Nat.prime_dvd_prime_iff_eq hp.1 (by decide)).mp hd))))
    · rw [show 378000 = 2^4*3^3*5^3*7 by decide] at hd
      simp only [hp.1.dvd_mul] at hd
      rcases hd with ((hd | hd) | hd) | hd
      · exact .inl ((Nat.prime_dvd_prime_iff_eq hp.1 (by decide)).mp (hp.1.dvd_of_dvd_pow hd))
      · exact .inr (.inl ((Nat.prime_dvd_prime_iff_eq hp.1 (by decide)).mp (hp.1.dvd_of_dvd_pow hd)))
      · exact .inr (.inr (.inl ((Nat.prime_dvd_prime_iff_eq hp.1 (by decide)).mp (hp.1.dvd_of_dvd_pow hd))))
      · exact .inr (.inr (.inr (.inl ((Nat.prime_dvd_prime_iff_eq hp.1 (by decide)).mp hd))))
  rcases hp with ⟨_,h5,h8⟩
  rcases hh with rfl | rfl | rfl | rfl | rfl <;> norm_num at *

private theorem fieldFour_small_order
    {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (hc : pCore 2 A = ⊥) (hm : LocalGeometry.Components.FieldFourOvergroup A)
    (hd : Nat.card A ∣ 372000 ∨ Nat.card A ∣ 378000)
    (hb : Nat.card A ≤ 378000)
    (hseven : ¬ (IsAlternating A 7 ∨ IsAlternatingCover A 7)) :
    ∃ u, IsPSLSign A u 3 5 ∨ IsSLSign A u 3 5 := by
  cases hm with
  | alternating hm => exact (hseven (.inl hm)).elim
  | alternatingCover hm => exact (hseven (.inr hm)).elim
  | primeLinear p hp hm =>
    have hpd : p ∣ Nat.card A := by
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      have hodd : Odd p := hp.1.odd_of_ne_two (by have := hp.2.1; omega)
      rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
        ⟨p,1,hp.1,hodd,by decide,by simpa using hF⟩,hF]
      have he : 2 ∣ p^2-1 := by
        obtain ⟨a,ha⟩ := hodd
        refine ⟨2*a*(a+1),?_⟩
        nlinarith [Nat.sub_add_cancel (show 1 ≤ p^2 by have := hp.1.two_le; nlinarith)]
      apply (Nat.dvd_div_iff_mul_dvd (dvd_mul_of_dvd_right he p)).mpr
      simpa only [Nat.mul_comm] using Nat.mul_dvd_mul (dvd_refl p) he

    exact (exceptional_prime_not_divisor hp (hd.imp hpd.trans hpd.trans)).elim
  | linearTwentyFive hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
      ⟨5,2,by decide,by decide,by decide,by simpa using hF⟩,hF] at hd
    norm_num at hd
  | three u hm => exact ⟨u,hm⟩
  | m22 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m22_order] at hb
    omega
  | m22Cover hm =>
    have hh := Nat.card_le_card_of_surjective (QuotientGroup.mk' (center A))
      (QuotientGroup.mk'_surjective (center A))
    rw [Nat.card_congr hm.2.2.some.toEquiv,Sporadic.Mathieu.m22_order] at hh
    omega
  | m23 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m23_order] at hb
    omega
  | j1 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Janko1.card_model] at hd
    norm_num at hd
  | j2 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hb
    omega
  | j4 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Janko4.Cardinality.model_card] at hb
    omega
  | hs hm =>
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier] at hb
    omega
  | ru hm =>
    rw [Nat.card_congr hm.some.toEquiv,Rudvalis.model_card] at hb
    omega
  | nilpotentExtension hm =>
    exact (Quasisimple.Classification.not_odd_sl2_extension hc _ (by decide : Odd 5) hm).elim
  | elementaryExtension p hp hm =>
    exact (Quasisimple.Classification.not_odd_sl2_extension hc _
      (hp.1.odd_of_ne_two (by have := hp.2.1; omega)) hm).elim

/-- A quasisimple point quotient is impossible in either quintic signed
ternary container. The original full point catalogue is exhausted, and
its final ternary row would have index at most three in a perfect group. -/
theorem ofFlag_not_quasisimple_point_in_odd_ternary
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : IsPSLSign (J ⧸ pCore 2 J) u 3 p ∨ IsSLSign (J ⧸ pCore 2 J) u 3 p) :
    ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) := by
  intro hqs
  let := hqs
  obtain ⟨hp5,_,⟨i,hi,_⟩,_⟩ :=
    ofFlag_odd_ternary_faithful_point_quotient S f X z H h hne hlinear h1132 e hJ hlt.le hp ho u hm
  subst p
  obtain ⟨_,hrows,_,hseven⟩ := ofFlag_odd_ternary_point_catalogue S f X z H h hne
    hlinear h1132 e hJ hlt hp ho u hm
  have hdiv := card_dvd_of_injective i hi
  obtain ⟨horders,_,hbound⟩ := odd_ternary_five_card_bounds u hm
  obtain ⟨v,hsmall⟩ := fieldFour_small_order (pCore_quotient_pCore_eq_bot 2) hrows
    (horders.imp hdiv.trans hdiv.trans)
    ((Nat.card_le_card_of_injective i hi).trans hbound) hseven
  have hsmallcard := (odd_ternary_five_card_bounds v hsmall).2.1
  obtain ⟨P,C,hC,hproper,_,⟨b⟩,htop⟩ := proper_local_model_image h.point_mem_local_family
    hJ (sylow_normalizes_overcomponent h hJ hlt.le) (sylow_normalizes_point h) hlt
    (MulEquiv.refl (J ⧸ pCore 2 J))
  have hCcard : 126000 ≤ Nat.card C := by
    rw [Nat.card_congr b.toEquiv] at hsmallcard
    exact hsmallcard.trans (Nat.card_le_card_of_surjective (QuotientGroup.mk' (pCore 2 C))
      (QuotientGroup.mk'_surjective _))
  have hindex : C.index ≤ 4 := by
    have he := C.card_mul_index
    nlinarith
  let := htop.perfect
  exact hproper (top_unique ((perfect_le_normalCore_of_index_le_four ⊤ C hindex).trans C.normalCore_le))

/-- The complete signed odd ternary comparison on the original flag.
The point quotient is the elementary-plane-by-SL₂(5) extension, the
containing sign is linear, and the literal proper-embedding contract holds.
No quasisimplicity branch or source pair is assumed. -/
theorem ofFlag_properEmbedding_of_odd_ternary
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : IsPSLSign (J ⧸ pCore 2 J) u 3 p ∨ IsSLSign (J ⧸ pCore 2 J) u 3 p) :
    p = 5 ∧ u = false ∧
      HasExtension ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)
        (ElementaryModel 5 2) (fun Q _ => IsSL Q 2 5) ∧
      ProperEmbedding (ofFlag S f X z H).Kz J := by
  exact ofFlag_properEmbedding_of_nonquasisimple_odd_ternary S f X z H h hne
    hlinear h1132 e hcent hJ hlt
    (ofFlag_not_quasisimple_point_in_odd_ternary S f X z H h hne hlinear h1132 e hJ.1 hlt hp ho u hm)
    hp ho u hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
