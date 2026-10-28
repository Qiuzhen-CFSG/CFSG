module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.Inputs
public import Theory.SpecificGroups.BinaryLinear.SixSubgroupCentralizers
public import Theory.GroupTheory.CentralKernelSubgroupEmbedding
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.FieldTheory.Finite.GaloisField
public import Theory.Alternating.Theorem523Reduction
public import Theory.Alternating.SixInEightDoubleCover
public import Theory.GroupTheory.CoveringKernelCard
public import Theory.GroupTheory.PerfectCentralCoverEmbeddingRigidity
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.PSL5Two.UniversalCover


/-!
# Binary central-cover and inner-action reductions for E.6.23

Every embedded A₆ in a group with central quotient PSL₄(2) or PSL₅(2)
has centralizer equal to the center. Its image embeds faithfully in the
quotient, and the actual binary natural model has trivial centralizer of
that image. Thus the given order-two automorphism group fixing A₆ cannot
be contained in the inner automorphism group, even before cover removal.

The established Schur multiplier calculation bounds the center in the
PSL₄(2) branch by two. A nontrivial center would identify the group with
the explicit Schur double cover of A₈, which contains no embedded A₆.
The PSL₅(2) branch uses the trivial kernel of its actual universal central
projection. These two proved model facts remove both central covers and
discharge the published `BinaryCoverAnalysis` contract. The conditional
assembly remains available separately.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.6.23,
printed p.254 (PDF p.265), with I.1.3 on printed p.407; GLS3, Theorem
5.2.3, Proposition 5.2.4 and Theorem 6.1.4. The field, matrix and exceptional
A₈ comparisons are actual multiplicative equivalences.
-/

public section

open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification
universe u
variable {D : Type u} [Group D]

private noncomputable def binaryProjectiveEquiv {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL D n 2) :
    D ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2) := Classical.choice <| by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = Fintype.card (ZMod 2) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard
  exact ⟨e.trans (Atlas.fieldEquivPSL n (FiniteField.ringEquivOfCardEq hcard'))⟩

private theorem center_eq_bot_of_alt6 {H : Type*} [Group H]
    (e : H ≃* alternatingGroup (Fin 6)) : center H = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  apply e.injective
  have he : e x ∈ center (alternatingGroup (Fin 6)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    simpa only [← map_mul] using congrArg e (mem_center_iff.mp hx z)
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
  simpa only [map_one] using he

/-- Every embedded A₆ has exactly the center as its centralizer in a group
whose central quotient is one of the two binary models. -/
theorem six_centralizer_eq_center_of_binary_quotient
    (hm : ClassicalGroup.IsPSL (D ⧸ center D) 4 2 ∨
      ClassicalGroup.IsPSL (D ⧸ center D) 5 2)
    (S : Subgroup D) (hS : Chapter1.Section02.LocalModels.IsAlternating S 6) :
    centralizer (S : Set D) = center D := by
  obtain ⟨n, hn, hm⟩ : ∃ n, (n = 4 ∨ n = 5) ∧
      ClassicalGroup.IsPSL (D ⧸ center D) n 2 := by
    rcases hm with hm | hm
    · exact ⟨4, Or.inl rfl, hm⟩
    · exact ⟨5, Or.inr rfl, hm⟩
  obtain ⟨es⟩ := hS
  let e := (binaryProjectiveEquiv hm).trans (projectiveEquivLinear (by omega : 0 < n))
  let q := QuotientGroup.mk' (center D)
  let f := e.toMonoidHom.comp q
  have hk : f.ker = center D := by
    ext x
    change e (q x) = 1 ↔ x ∈ center D
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  let P := S.map f
  let d : P ≃* alternatingGroup (Fin 6) :=
    (f.subgroupMapEquivOfKerLeCenter hk.le S (center_eq_bot_of_alt6 es)).symm.trans es
  have hP : Nat.card P = 360 := by
    rw [Nat.card_congr d.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hPc := BinaryLinear.SixSubgroupCentralizers.centralizer_eq_bot hn P hP
    (center_eq_bot_of_alt6 d)
  apply le_antisymm
  · intro x hx
    have hfx : f x ∈ centralizer (P : Set (LinearGroup n)) := by
      apply mem_centralizer_iff.mpr
      rintro _ ⟨y, hy, rfl⟩
      simpa only [← map_mul] using congrArg f (mem_centralizer_iff.mp hx y hy)
    have hker : x ∈ f.ker := mem_bot.mp (hPc ▸ hfx)
    exact hk ▸ hker
  · intro x hx
    exact mem_centralizer_iff.mpr (fun y _ => mem_center_iff.mp hx y)

/-- An order-two group of automorphisms fixing the embedded A₆ is not inner,
even before removing the central cover. -/
theorem outer_of_binary_quotient
    (hm : ClassicalGroup.IsPSL (D ⧸ center D) 4 2 ∨
      ClassicalGroup.IsPSL (D ⧸ center D) 5 2)
    (R : Subgroup (MulAut D)) (hR : Nat.card R = 2)
    (S : Subgroup D) (hfix : S ≤ FixedPoints.subgroup R D)
    (hS : Chapter1.Section02.LocalModels.IsAlternating S 6) :
    ¬ R ≤ (MulAut.conj : D →* MulAut D).range := by
  intro hinner
  have hbot : R = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    obtain ⟨x, rfl⟩ := hinner ha
    have hx : x ∈ centralizer (S : Set D) := by
      apply mem_centralizer_iff.mpr
      intro y hy
      have hxy : MulAut.conj x y = y := hfix hy ⟨MulAut.conj x, ha⟩
      exact (mul_inv_eq_iff_eq_mul.mp hxy).symm
    rw [six_centralizer_eq_center_of_binary_quotient hm S hS] at hx
    apply mem_bot.mpr
    ext y
    change x * y * x⁻¹ = y
    rw [← mem_center_iff.mp hx y, mul_inv_cancel_right]
  rw [hbot, card_bot] at hR
  omega

open GLS3.Chapter5.SchurPresentation

private theorem quotient_model_map_ker {H : Type*} [Group H]
    (e : D ⧸ center D ≃* H) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (center D))).ker = center D := by
  ext x
  change e (QuotientGroup.mk x) = 1 ↔ x ∈ center D
  rw [← e.map_one, e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

private theorem card_of_surjective {H K : Type*} [Group H] [Group K]
    (f : H →* K) (hf : Function.Surjective f) :
    Nat.card H = Nat.card K * Nat.card f.ker := by
  rw [card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]

/-- The established alternating multiplier bound leaves only the trivial
cover and the genuine Schur double cover in the degree-four branch. -/
theorem center_card_dvd_two_of_four_quotient [Finite D] [IsQuasisimple D]
    (hm : ClassicalGroup.IsPSL (D ⧸ center D) 4 2) :
    Nat.card (center D) ∣ 2 := by
  let e := (binaryProjectiveEquiv hm).trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
  let f : Covering D (alternatingGroup (Fin 8)) :=
    { toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center D))
      surjective := e.surjective.comp (QuotientGroup.mk'_surjective _) }
  obtain ⟨l, hl, _⟩ :=
    (theorem_5_2_3_b_universality 3 (by decide) (by decide)) D f
  have hd := kernel_card_dvd_of_surjective_factor
    (schurAlternatingCovering 3).toMonoidHom f.toMonoidHom l.toMonoidHom l.surjective
    (congrArg Covering.toMonoidHom hl)
  rw [natCard_ker_schurAlternatingCovering] at hd
  exact (quotient_model_map_ker e) ▸ hd

/-- To eliminate the degree-four central cover, it suffices to exclude an
actual A₆ subgroup of the explicit Schur double cover of A₈. -/
theorem center_eq_bot_four_of_no_six_in_double_cover [Finite D] [IsQuasisimple D]
    (hno : ∀ ι : alternatingGroup (Fin 6) →* SchurAlternatingGroup 3,
      ¬ Function.Injective ι)
    (hm : ClassicalGroup.IsPSL (D ⧸ center D) 4 2)
    (S : Subgroup D) (hS : Chapter1.Section02.LocalModels.IsAlternating S 6) :
    center D = ⊥ := by
  by_contra hz
  have hd := center_card_dvd_two_of_four_quotient hm
  have htwo : Nat.card (center D) = 2 :=
    (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left (fun h => hz (card_eq_one.mp h))
  let e := (binaryProjectiveEquiv hm).trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
  let f : Covering D (alternatingGroup (Fin 8)) :=
    { toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center D))
      surjective := e.surjective.comp (QuotientGroup.mk'_surjective _) }
  obtain ⟨l, hl, _⟩ :=
    (theorem_5_2_3_b_universality 3 (by decide) (by decide)) D f
  have hc : Nat.card (SchurAlternatingGroup 3) = Nat.card D := by
    rw [card_of_surjective (schurAlternatingCovering 3).toMonoidHom
      (schurAlternatingCovering 3).surjective, natCard_ker_schurAlternatingCovering]
    rw [card_of_surjective f.toMonoidHom f.surjective, quotient_model_map_ker e, htwo]
  let d : SchurAlternatingGroup 3 ≃* D :=
    MulEquiv.ofBijective l.toMonoidHom
      ((Nat.bijective_iff_surjective_and_card l.toMonoidHom).mpr ⟨l.surjective, hc⟩)
  obtain ⟨es⟩ := hS
  let ι := d.symm.toMonoidHom.comp (S.subtype.comp es.symm.toMonoidHom)
  exact hno ι (d.symm.injective.comp (S.subtype_injective.comp es.symm.injective))

/-- A trivial universal multiplier removes the degree-five cover, using the
actual binary projective model rather than an abstract family label. -/
theorem center_eq_bot_five_of_trivial_multiplier [IsQuasisimple D]
    (hfive : (PerfectCentralCovering.universalProjection
      (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2))).ker = ⊥)
    (hm : ClassicalGroup.IsPSL (D ⧸ center D) 5 2) :
    center D = ⊥ := by
  let e := binaryProjectiveEquiv hm
  let f : PerfectCentralCovering.Cover D
      (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    { toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center D))
      surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
      isPerfect := inferInstance
      ker_le_center := (quotient_model_map_ker e).le }
  have hi := f.injective_of_universalProjection_ker_eq_bot hfive
  exact (quotient_model_map_ker e).symm.trans (f.toMonoidHom.ker_eq_bot_iff.mpr hi)

/-- Conditional assembly of the published contract. The two
model facts are independent: A₆ does not embed in 2A₈, and PSL₅(2) has
trivial universal multiplier. Neither fact is assumed by the source contract. -/
theorem binaryCoverAnalysis_of_cover_facts
    (hfour : ∀ ι : alternatingGroup (Fin 6) →* SchurAlternatingGroup 3,
      ¬ Function.Injective ι)
    (hfive : (PerfectCentralCovering.universalProjection
      (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2))).ker = ⊥) :
    BinaryCoverAnalysis.{u} := by
  intro D _ _ _ _ _ hm R hR S hfix _ hS
  refine ⟨?_, outer_of_binary_quotient hm R hR S hfix hS⟩
  rcases hm with hm | hm
  · exact center_eq_bot_four_of_no_six_in_double_cover hfour hm S hS
  · exact center_eq_bot_five_of_trivial_multiplier hfive hm

/-- The binary-model step of E.6.23: the quasisimple cover is centerless,
and the given order-two automorphism group fixing the actual A₆ component
is not contained in the inner automorphisms. Both cover facts are discharged
on their concrete models, with no additional premise. -/
theorem binaryCoverAnalysis : BinaryCoverAnalysis.{u} :=
  binaryCoverAnalysis_of_cover_facts
    not_injective_six_to_schurAlternatingGroup_three
    Theory.SpecificGroups.PSL5Two.UniversalCover.universalProjection_ker_eq_bot

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification
