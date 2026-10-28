module
public import Theory.SpecificGroups.OddThreePerfectCentralizers
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.OddThree
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SmallModels
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.CoverSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.ComponentKnownSimple

/-!
# The odd ternary larger-span branch with its actual full Sylow

A perfect centerless subgroup of two-rank at least two cannot centralize
an involution in an odd ternary model. Its full Sylow normalizer therefore
acts faithfully. For binary PSL₂ the actual automorphism order then
contradicts the containing group's Sylow order. Restriction uses the
original Sylow intersection with the containing subnormal group.

The final applications retain the literal images in X/O₂(X). The fixed-free
source excludes all odd ternary models, and the general source forces the
exceptional SL₂(5) smaller cover, leaving its field-parameter recognition
as the remaining natural branch.

Source: Aschbacher–Smith A.3.12(9), pp.47–48, and C.5.12, p.163.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
open Theory.SpecificGroups.OddThreePerfectCentralizers
open Theory.SpecificGroups.OddThreeRank
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem odd_three_model_centralizer_rank
    {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (hz : center K = ⊥) {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : IsPSLSign G u 3 p ∨ IsSLSign G u 3 p)
    (t : G) (ht : orderOf t = 2)
    (j : K →* centralizer ({t} : Set G)) (hj : Function.Injective j) :
    primeRank 2 K ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  cases u with
  | false =>
    rcases hm with hm | hm
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let c := Matrix.SU3.InnerThreeRank.centralizerEquiv e t
      exact projective_linear_rank
        (two_ne_zero_of_odd_card ho (k := 1) (by simpa using hF))
        (e t) ((e.orderOf_eq t).trans ht) (c.toMonoidHom.comp j) (c.injective.comp hj)
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let c := Matrix.SU3.InnerThreeRank.centralizerEquiv e t
      exact special_linear_rank
        (two_ne_zero_of_odd_card ho (k := 1) (by simpa using hF))
        (e t) ((e.orderOf_eq t).trans ht) (c.toMonoidHom.comp j) (c.injective.comp hj)
  | true =>
    rcases hm with hm | hm
    · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
      let c := Matrix.SU3.InnerThreeRank.centralizerEquiv e t
      exact projective_unitary_rank p ho F J hF hc
        (e t) ((e.orderOf_eq t).trans ht) (c.toMonoidHom.comp j) (c.injective.comp hj)
    · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
      let c := Matrix.SU3.InnerThreeRank.centralizerEquiv e t
      exact special_unitary_rank p ho F J hF hc hz
        (e t) ((e.orderOf_eq t).trans ht) (c.toMonoidHom.comp j) (c.injective.comp hj)

/-- In an odd ternary model, the full Sylow meets the centralizer of a
centerless perfect subgroup of two-rank at least two trivially. -/
theorem odd_three_perfect_sylow_faithful
    (T : Sylow 2 G) (B : Subgroup G) [Group.IsPerfect B]
    (hz : center B = ⊥) (hr : 2 ≤ primeRank 2 B)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : IsPSLSign G u 3 p ∨ IsSLSign G u 3 p) :
    (T : Subgroup G) ⊓ centralizer (B : Set G) = ⊥ := by
  let R := (T : Subgroup G) ⊓ centralizer (B : Set G)
  by_contra hne
  have hR : IsPGroup 2 R := T.isPGroup'.to_le inf_le_left
  have hd : 2 ∣ Nat.card R := hR.card_eq_or_dvd.resolve_left
    (fun he => hne (card_eq_one.mp he))
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 hd
  let j : B →* centralizer ({(t : G)} : Set G) := B.subtype.codRestrict _ (by
    intro b
    exact mem_centralizer_singleton_iff.mpr (t.property.2 b b.property))
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : centralizer ({(t : G)} : Set G) => (z : G)) he)
  have hh := odd_three_model_centralizer_rank hz hp ho u hm t
    ((orderOf_coe t).trans ht) j hj
  omega

omit [Finite G] in
private theorem top_projective_model {p : ℕ} (u : Bool)
    (hm : IsPSLSign G u 3 p) : IsPSLSign (⊤ : Subgroup G) u 3 p := by
  cases u with
  | false => exact hm.of_mulEquiv topEquiv
  | true =>
    obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
    exact ⟨F,inferInstance,inferInstance,J,hF,hc,⟨topEquiv.trans e⟩⟩

omit [Finite G] in
private theorem top_special_model {p : ℕ} (u : Bool)
    (hm : IsSLSign G u 3 p) : IsSLSign (⊤ : Subgroup G) u 3 p := by
  cases u with
  | false =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact ⟨F,inferInstance,inferInstance,hF,⟨topEquiv.trans e⟩⟩
  | true =>
    obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
    exact ⟨F,inferInstance,inferInstance,J,hF,hc,⟨topEquiv.trans e⟩⟩

/-- A full Sylow of an odd ternary group cannot normalize a binary PSL₂
subgroup with noncubic parameter. Faithfulness follows from the model. -/
theorem not_odd_three_binary_intrinsic
    (T : Sylow 2 G) (B : Subgroup G) [Group.IsPerfect B]
    {n : ℕ} (hn : 1 < n) (hB : ClassicalGroup.IsPSL B 2 (2^n))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool) :
    ¬ IsPSLSign G u 3 p ∧ ¬ IsSLSign G u 3 p := by
  have hf (hm : IsPSLSign G u 3 p ∨ IsSLSign G u 3 p) :=
    odd_three_perfect_sylow_faithful T B (binary_center_eq_bot hB)
      (by have := binary_rank_lower hB; omega) hp ho u hm
  constructor
  · intro hm
    exact not_odd_three_projective_containing T B ⊤ le_top hn hB hTB
      (hf (.inl hm)) hp ho u (top_projective_model u hm)
  · intro hm
    exact not_odd_three_special_containing T B ⊤ le_top hn hB hTB
      (hf (.inr hm)) hp ho u (top_special_model u hm)

/-- Restrict the original Sylow to the actual subnormal containing group.
No action-faithfulness hypothesis is added to the embedding interface. -/
theorem not_odd_three_binary_containing
    (T : Sylow 2 G) (B D : Subgroup G) [Group.IsPerfect B]
    (hBD : B ≤ D) (hD : D.IsSubnormal)
    {n : ℕ} (hn : 1 < n) (hB : ClassicalGroup.IsPSL B 2 (2^n))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool) :
    ¬ IsPSLSign D u 3 p ∧ ¬ IsSLSign D u 3 p := by
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_subnormal D hD
  let e := subgroupOfEquivOfLe hBD
  let : Group.IsPerfect (B.subgroupOf D) := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  apply not_odd_three_binary_intrinsic S (B.subgroupOf D) hn (hB.of_mulEquiv e) ?_ hp ho u
  rw [hS, ← subgroupOf_normalizer_eq hBD]
  intro s hs
  exact hTB hs


/-- The binary branch of the actual larger-span quotient is excluded from
all odd ternary models using its intrinsic full Sylow, with no A.3.12 input. -/
theorem source_larger_not_odd_three_of_binary_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hUT : U K ≤ T) (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G))
    {n : ℕ} (hn : 1 < n)
    (hB : ClassicalGroup.IsPSL ((K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) 2 (2^n))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool) :
    let E := ((conjugateSpanBy K X).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    ¬ IsPSLSign E u 3 p ∧ ¬ IsSLSign E u 3 p := by
  have hKX : K ≤ X := le_sup_left.trans hAX
  let r := QuotientGroup.mk' (pCore 2 X)
  let B := (K.subgroupOf X).map r
  let D := conjugateSpanBy K X
  let E := (D.subgroupOf X).map r
  let Q := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  have hsmall := noncubic_twoCore_small_models_with_quotient
    K T X hK h3 hUT hT hTK hKX hX S hS hVC
  let : IsQuasisimple B := hsmall.1
  have hD := source_larger_span_component_knownSimple hG K T X hK h3 hTK hAX hX S hS
  let := pCore_isNilpotent (p := 2) (G := X)
  have hE : E.IsCComponent := hD.map_quotient (pCore 2 X)
  apply not_odd_three_binary_containing Q B E
    (map_mono (subgroupOf_mono X (le_conjugateSpanBy K X))) hE.subnormal hn hB ?_ hp ho u
  change (S : Subgroup X).map r ≤ normalizer (B : Set (X ⧸ pCore 2 X))
  apply (map_mono (f := r) ?_).trans (le_normalizer_map _)
  rw [← subgroupOf_normalizer_eq hKX]
  intro s hs
  exact hTK (hS ▸ mem_map_of_mem X.subtype hs)

/-- In the original larger-span setup, an odd ternary containing model
forces precisely the exceptional SL₂(5) smaller cover. This discharges the
entire binary smaller-image branch of the natural selection. -/
theorem source_larger_odd_three_forces_small_cover
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hUT : U K ≤ T) (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : let E := ((conjugateSpanBy K X).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
      IsPSLSign E u 3 p ∨ IsSLSign E u 3 p) :
    ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∧
      IsSL ((K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) 2 5 := by
  obtain ⟨_,n,hn,hq,_,hb | ⟨hn2,hb⟩⟩ := noncubic_twoCore_small_models_with_quotient
    K T X hK h3 hUT hT hTK (le_sup_left.trans hAX) hX S hS hVC
  · have he := source_larger_not_odd_three_of_binary_image hG K T X hK h3 hUT hT hTK
      hAX hX S hS hVC hn hb hp ho u
    exact (hm.elim he.1 he.2).elim
  · exact ⟨by simpa only [hn2,Nat.reducePow] using hq,hb⟩


open ConjugateSource.RankOne Chapter1.Section02
open scoped IsMulCommutative

/-- The fixed-free original block gives a literal binary image in X/O₂(X),
so its full conjugate span has no odd ternary containing model. -/
theorem fixedFree_source_larger_not_odd_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hUT : U K ≤ T) (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G))
    (hz : blockFixed K = ⊥) {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool) :
    let E := ((conjugateSpanBy K X).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    ¬ IsPSLSign E u 3 p ∧ ¬ IsSLSign E u 3 p := by
  let V := conjugateSpanBy (U K) X
  have hKX : K ≤ X := le_sup_left.trans hAX
  have hVX : V ≤ X := conjugateSpanBy_le_self ((map_subtype_le _).trans hKX)
  have hXV : X ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
  have hr := noncubic_full_span_reduced K T hK h3 hUT hT hTK X hKX S hS hVC
  let : (V.subgroupOf X).Normal := hr.normal
  let : IsElementaryAbelian 2 V := by
    let : IsElementaryAbelian 2 (U K) := hK.chi.short.elementary.map K.subtype
    let : IsMulCommutative V :=
      (conjugateSpanBy_commutative_iff (U K) X).mpr (le_centralizer_iff.mp hVC)
    exact conjugateSpanBy_elementary_of_commutative (U K) X
  obtain ⟨eK⟩ := short_fixedFree_twoCore_image_equiv K X V hK.chi.short hKX hVX hXV
    (le_conjugateSpanBy _ _) S (hS ▸ hTK) hr (Chapter1.mem_He_iff.mp hX) hz
  obtain ⟨n,hn,hm⟩ := noncubic_binary_model K hK h3
  exact source_larger_not_odd_three_of_binary_image hG K T X hK h3 hUT hT hTK
    hAX hX S hS hVC hn (hm.of_mulEquiv eK.symm) hp ho u

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
