module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.CenterBounds
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.ResidualQuotients
public import Theory.Mathieu.M24.Properties.InvolutionFixedOrders
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.PRadicalSylowNormalizer
public import Theory.GroupTheory.SimpleSectionNormalAlternative
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity

/-!
# The original unitary residual excludes the entire Mathieu local branch

For a nontrivial elementary subgroup A of M₂₄ of order at most sixteen,
conjugation on A has centralizer kernel and image in Aut(A). The former lies
in an involution centralizer, whose order is not divisible by nine; the latter
has order not divisible by 27. A simple U₃(3) section must occur in one of
these two layers, contradicting its order 6048 in either case.

A large-center native radical with whole normalizer in max1 has exactly such
a small elementary Mathieu image. The literal projection has binary kernel,
so the residual marking survives after removing the full intrinsic cores.
If the Mathieu image is trivial, the radical is the native kernel and normality
of the residual in its whole normalizer excludes the M₂₄ quotient. Conjugation
transports all radicals, full normalizers and residual markings together.

This is a source-specific exit for Aschbacher--Smith 4.2.13 and its original
13.3.16 application, using the local reduction in An--O'Brien--Wilson (2003),
Section 4, p.122. It does not classify all large-center radical quotients or
assert arbitrary native placement. The trivial-image step needs normality in
the whole normalizer; no normality in max1 is assumed.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
open Sporadic.Mathieu
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.localKernel Cardinality.max1Subgroup

private theorem simple_section_card_dvd_kernel_or_target
    {G H S : Type*} [Group G] [Group H] [Group S] [IsSimpleGroup S]
    [Finite G] [Finite H] (f : G →* H) (B : Subgroup G)
    (b : B →* S) (hb : Function.Surjective b) :
    Nat.card S ∣ Nat.card f.ker ∨ Nat.card S ∣ Nat.card H := by
  rcases simple_section_normal_or_quotient f.ker B b hb with ⟨W,g,hg⟩ | ⟨W,g,hg⟩
  · exact Or.inl ((card_dvd_of_surjective g hg).trans W.card_subgroup_dvd_card)
  · right
    have hc := (card_dvd_of_surjective g hg).trans W.card_subgroup_dvd_card
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at hc
    exact hc.trans f.range.card_subgroup_dvd_card

private theorem small_binary_aut_not_twentyseven
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 16) : ¬ 27 ∣ Nat.card (MulAut E) := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hnle : n ≤ 4 := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    rw [←hn] at hp
    norm_num at hp
    omega
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E n hn]
  interval_cases n <;> decide

private theorem involution_centralizer_not_nine (t : M24) (ht : orderOf t = 2) :
    ¬ 9 ∣ Nat.card (centralizer ({t} : Set M24)) := by
  have ho : orderOf (MulAut.conj t) = 2 :=
    (orderOf_injective MulAut.conj
      (MulAut.conj_injective_of_center_eq_bot M24InvolutionCentralizers.center_eq_bot) t).trans ht
  simpa only [MulAut.fixedSubgroup_conj] using m24_involution_not_nine_dvd_fixed_card _ ho

/-- A nontrivial small elementary Mathieu subgroup has no unitary simple
section in its whole normalizer. This uses the full centralizer kernel of its
conjugation action, not just the order of the normalizer. -/
theorem small_elementary_normalizer_unitary_section_excluded
    (A : Subgroup M24) [IsElementaryAbelian 2 A] (hne : A ≠ ⊥) (hA : Nat.card A ≤ 16)
    (B : Subgroup (normalizer (A : Set M24)))
    (b : B →* commutator (Atlas.G2.Model (ZMod 2))) (hb : Function.Surjective b) : False := by
  let := Atlas.G2.isSimple_commutator_binary
  obtain ⟨t,ht⟩ := ne_bot_iff_exists_ne_one.mp hne
  have ht2 : orderOf (t : M24) = 2 := by
    exact (orderOf_injective A.subtype A.subtype_injective t).trans
      (orderOf_eq_prime
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 A) t) ht)
  have hc : centralizer (A : Set M24) ≤ centralizer ({(t : M24)} : Set M24) :=
    centralizer_le (Set.singleton_subset_iff.mpr t.property)
  have hk : Nat.card A.normalizerMonoidHom.ker ∣
      Nat.card (centralizer ({(t : M24)} : Set M24)) := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (A : Set M24))).toEquiv]
    exact card_dvd_of_le hc
  rcases simple_section_card_dvd_kernel_or_target A.normalizerMonoidHom B b hb with hd | hd
  · rw [Atlas.G2.LieAutomorphismExtensions.card_binaryDerived] at hd
    exact involution_centralizer_not_nine t ht2 ((by decide : 9 ∣ 6048).trans (hd.trans hk))
  · rw [Atlas.G2.LieAutomorphismExtensions.card_binaryDerived] at hd
    exact small_binary_aut_not_twentyseven hA ((by decide : 27 ∣ 6048).trans hd)

/-- The whole Mathieu local branch is impossible for a large-center radical
carrying the original normal unitary residual. -/
theorem unitary_radical_normalizer_not_le_mathieu (P : Subgroup Model)
    (hP : P.IsPRadical 2) (hlarge : 64 ≤ Nat.card (center P))
    (B : Subgroup (normalizer (P : Set Model))) [B.Normal]
    (b : (B ⧸ pCore 2 B) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ¬ normalizer (P : Set Model) ≤ ElementaryNormalizerCover.max1 := by
  intro hN
  let A := (P.subgroupOf ElementaryNormalizerCover.max1).map MathieuHallActors.projection
  obtain ⟨hElem,hsmall⟩ := radical_mathieu_image_small P hP hN hlarge
  let := hElem
  have heP : P = preimage A := radical_eq_preimage P hP hN
  by_cases hz : A = ⊥
  · have hP0 : P = ElementaryNormalizerCover.embeddedKernel := by
      rw [heP,hz,preimage_bot]
    let eN := MulEquiv.subgroupCongr
      (congrArg (fun U : Subgroup Model => normalizer (U : Set Model)) hP0)
    exact unitary_normal_residual_quotients_excluded B b
      (Or.inr (Or.inl ⟨(coreQuotientCongr eN).trans kernelNormalizerQuotientEquiv⟩))
  · let H := normalizer (A : Set M24)
    let eN : normalizer (P : Set Model) ≃* preimage H :=
      MulEquiv.subgroupCongr ((congrArg (fun U : Subgroup Model => normalizer (U : Set Model))
        heP).trans (normalizer_preimage A))
    let f : normalizer (P : Set Model) →* H := (preimageProjection H).comp eN.toMonoidHom
    have hk : IsPGroup 2 f.ker :=
      (preimageProjection_kernel_two H).comap_of_injective eN.toMonoidHom eN.injective
    let g := f.subgroupMap B
    have hgk : IsPGroup 2 g.ker := by
      have he : g.ker = f.ker.comap B.subtype := by
        ext x
        exact Subtype.ext_iff
      rw [he]
      exact hk.comap_of_injective B.subtype B.subtype_injective
    let c := (g.quotientPCoreEquivOfSurjective (f.subgroupMap_surjective B) hgk).symm.trans b
    exact small_elementary_normalizer_unitary_section_excluded A hz hsmall (B.map f)
      (c.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (B.map f))))
      (c.surjective.comp (QuotientGroup.mk'_surjective _))

/-- The same source residual excludes every ambient conjugate of max1,
transporting the radical and the entire normalizer together. -/
theorem unitary_radical_normalizer_not_le_mathieu_conjugate (P : Subgroup Model)
    (hP : P.IsPRadical 2) (hlarge : 64 ≤ Nat.card (center P))
    (B : Subgroup (normalizer (P : Set Model))) [B.Normal]
    (b : (B ⧸ pCore 2 B) ≃* commutator (Atlas.G2.Model (ZMod 2))) (g : Model) :
    ¬ normalizer (P : Set Model) ≤
      ElementaryNormalizerCover.max1.map (MulAut.conj g).toMonoidHom := by
  intro hN
  let c := (MulAut.conj g).symm
  let Q := P.map c.toMonoidHom
  let a : normalizer (P : Set Model) ≃* normalizer (Q : Set Model) :=
    (c.subgroupMap _).trans (MulEquiv.subgroupCongr (map_equiv_normalizer_eq P c))
  have hQ := hP.map_equiv c
  have hlargeQ : 64 ≤ Nat.card (center Q) := by
    exact hlarge.trans_eq (Nat.card_congr (centerCongr (c.subgroupMap P)).toEquiv)
  let B' := B.map a.toMonoidHom
  let : B'.Normal := Normal.map inferInstance a.toMonoidHom a.surjective
  let b' := (coreQuotientCongr (a.subgroupMap B).symm).trans b
  have hQc : normalizer (Q : Set Model) ≤ ElementaryNormalizerCover.max1 := by
    rw [← map_equiv_normalizer_eq P c]
    have hh := map_mono (f := c.toMonoidHom) hN
    have hi : c.toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id Model := by
      ext x
      exact (MulAut.conj g).symm_apply_apply x
    simpa only [map_map,hi,map_id] using hh
  exact unitary_radical_normalizer_not_le_mathieu Q hQ hlargeQ B' b' hQc

end Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
