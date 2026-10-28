module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.AlternatingCovers.SevenExclusion.ModelInputs
public import Theory.Alternating.SevenInvolutionGeneration
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
public import Theory.Representation.BinaryIrreducibleCentralizer
public import Theory.ElementaryAbelian.Quotient
public import Theory.Representation.Quotient
public import Theory.GroupTheory.PerfectNormalizerLift

/-!
# Triple-seven normalizer geometry

Conjugation embeds every elementary two-subgroup into automorphisms of the
perfect triple cover. Faithful descent to A₇ and Aut(A₇) ≃ S₇ give order at
most eight. An automorphism fixing the cubic center is inner, since every
outer automorphism inverts a central element of order three. Cubing an inner
representative gives an involution; the characteristic-two Schur obstruction
then places the ambient involution in the actual component.

Perfectness lifts generation by three conjugate involutions from A₇ to its
triple cover. The proved A₇ generation theorem therefore completes the exact
`NormalizerGeometry` contract, with no degree or offender hypothesis.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.1.13,
printed pp.73–74, and K.1, printed p.452. The automorphism input is
GLS3, Theorem 5.2.1 and Proposition 5.2.8.
-/

public noncomputable section

open Subgroup Theory.GroupTheory GLS3.Chapter5 GLS3.Chapter5.OddCentralCovers
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.AlternatingCovers.SevenExclusion

universe v w

private theorem projection_ker : tripleSevenProjection.ker = center TripleSeven := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  exact tripleSevenCovering.ker_eq_center_of_isSimple

private def cover : PerfectCentralCovering.Cover TripleSeven (alternatingGroup (Fin 7)) where
  toMonoidHom := tripleSevenProjection
  surjective := tripleSevenProjection_surjective
  isPerfect := inferInstance
  ker_le_center := projection_ker.le

private def autPerm : MulAut TripleSeven →* Equiv.Perm (Fin 7) :=
  (theorem_5_2_1_a (by simp : 5 < Fintype.card (Fin 7)) (by simp)).toMonoidHom.comp
    (cover.autMap projection_ker)

private theorem autPerm_injective : Function.Injective autPerm :=
  (theorem_5_2_1_a (by simp : 5 < Fintype.card (Fin 7)) (by simp)).injective.comp
    (cover.autMap_injective projection_ker)

variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]

private theorem range_irreducible (ι : TripleSeven →* H) (hi : Function.Injective ι)
    (σ : Representation (ZMod 2) H W) (hirr : Representation.IsIrreducible (σ.comp ι)) :
    Representation.IsIrreducible (σ.comp ι.range.subtype) := by
  exact (Representation.irreducible_comp_surjective_iff
    (MonoidHom.ofInjective hi).toMonoidHom (MonoidHom.ofInjective hi).surjective
    (σ.comp ι.range.subtype)).mp hirr

/-- Every elementary two-subgroup of a faithful binary overgroup has order at most eight. -/
theorem elementary_card_le_eight (ι : TripleSeven →* H) (hi : Function.Injective ι)
    (hn : ι.range.Normal) (σ : Representation (ZMod 2) H W) (hf : Function.Injective σ)
    (hirr : Representation.IsIrreducible (σ.comp ι))
    (A : Subgroup H) (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ 8 := by
  let := hn
  let := hA
  let := range_irreducible ι hi σ hirr
  have hAL : A ≤ normalizer (ι.range : Set H) := by rw [normalizer_eq_top]; exact le_top
  let f := ι.range.normalizerMonoidHom.comp (inclusion hAL)
  have hfi : Function.Injective f :=
    Representation.BinaryIrreducibleCentralizer.elementary_conjugation_injective σ ι.range hf A hAL
  let e := MonoidHom.ofInjective hi
  let g := autPerm.comp ((MulAut.congr e.symm).toMonoidHom.comp f)
  have hgi : Function.Injective g := autPerm_injective.comp ((MulAut.congr e.symm).injective.comp hfi)
  have heg : IsElementaryAbelian 2 g.range :=
    IsElementaryAbelian.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have hc := Representation.AlternatingSevenConjugatePair.ElementaryGeometry.elementary_card_le heg
  exact (Nat.card_congr (MonoidHom.ofInjective hgi).toEquiv).le.trans hc

private def action (ι : TripleSeven →* H) (hi : Function.Injective ι)
    [ι.range.Normal] : H →* MulAut TripleSeven :=
  (MulAut.congr (MonoidHom.ofInjective hi).symm).toMonoidHom.comp MulAut.conjNormal

private theorem action_apply (ι : TripleSeven →* H) (hi : Function.Injective ι)
    [ι.range.Normal] (a : H) (k : TripleSeven) :
    ι (action ι hi a k) = a * ι k * a⁻¹ := by
  have he := congrArg Subtype.val ((MonoidHom.ofInjective hi).apply_symm_apply
    (MulAut.conjNormal (H := ι.range) a (MonoidHom.ofInjective hi k)))
  exact he

private theorem center_fixing_inner (ι : TripleSeven →* H) (hi : Function.Injective ι)
    [ι.range.Normal] (a : H)
    (ha : a ∈ centralizer ((center TripleSeven).map ι : Set H)) :
    ∃ k : TripleSeven, action ι hi a = MulAut.conj k := by
  by_contra h
  have hnon : ∀ k : TripleSeven, action ι hi a ≠ MulAut.conj k := by simpa using h
  obtain ⟨c, _, hc1, hcz, hc3, _, hc⟩ := a7_outer_exists_center_orderThree_inverted
    tripleSevenCovering (Or.inl tripleSevenCovering_kernel_card)
    (action ι hi a) (cover.autMap projection_ker (action ι hi a))
    (fun k => (cover.autMap_apply projection_ker _ k).symm) hnon
  have hfix : action ι hi a c = c := by
    apply hi
    rw [action_apply, ← (mem_centralizer_iff.mp ha) (ι c) (mem_map_of_mem ι hcz),
      mul_inv_cancel_right]
  have hc2 : c ^ 2 = 1 := by
    rw [pow_two, ← inv_eq_iff_mul_eq_one]
    exact (hfix.symm.trans hc).symm
  apply hc1
  calc c = c ^ 3 := by rw [pow_succ, hc2, one_mul]
       _ = 1 := hc3

private theorem center_cube (c : TripleSeven) (hc : c ∈ center TripleSeven) : c ^ 3 = 1 := by
  have h := pow_card_eq_one' (x := (⟨c, hc⟩ : center TripleSeven))
  rw [tripleSeven_center_card] at h
  exact congrArg (center TripleSeven).subtype h

/-- An ambient involution centralizing the cubic center belongs to the triple cover. -/
theorem involution_mem_range (ι : TripleSeven →* H) (hi : Function.Injective ι)
    (hn : ι.range.Normal) (σ : Representation (ZMod 2) H W) (hf : Function.Injective σ)
    (hirr : Representation.IsIrreducible (σ.comp ι)) (a : H) (ha2 : a ^ 2 = 1)
    (ha : a ∈ centralizer ((center TripleSeven).map ι : Set H)) : a ∈ ι.range := by
  let := hn
  let := range_irreducible ι hi σ hirr
  obtain ⟨k, hk⟩ := center_fixing_inner ι hi a ha
  have hk2 : MulAut.conj (k ^ 2) = 1 := by
    rw [map_pow, ← hk, ← map_pow, ha2, map_one]
  have hkz : k ^ 2 ∈ center TripleSeven := by
    apply mem_center_iff.mpr
    intro x
    have he := DFunLike.congr_fun hk2 x
    change k ^ 2 * x * (k ^ 2)⁻¹ = x at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hk6 : (k ^ 3) ^ 2 = 1 := by
    rw [← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul]
    exact center_cube _ hkz
  have hk3 : MulAut.conj (k ^ 3) = action ι hi a := by
    rw [pow_succ, map_mul, hk2, one_mul, hk]
  have hconj (x : TripleSeven) : a * ι x * a⁻¹ = ι (k ^ 3) * ι x * (ι (k ^ 3))⁻¹ := by
    rw [← action_apply ι hi, ← hk3]
    simp only [MulAut.conj_apply, map_mul, map_inv]
  have hak : Commute a (ι (k ^ 3)) := by
    have he := hconj (k ^ 3)
    rw [mul_inv_cancel_right] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hd2 : (a * (ι (k ^ 3))⁻¹) ^ 2 = 1 := by
    rw [hak.inv_right.mul_pow, ha2, inv_pow, ← map_pow, hk6, map_one, inv_one, mul_one]
  have hdc : a * (ι (k ^ 3))⁻¹ ∈ centralizer (ι.range : Set H) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨x, rfl⟩
    have he := hconj x
    have he' : a * ι x = ι (k ^ 3) * ι x * (ι (k ^ 3))⁻¹ * a :=
      (mul_inv_eq_iff_eq_mul).mp he
    calc
      ι x * (a * (ι (k ^ 3))⁻¹) = ι x * ((ι (k ^ 3))⁻¹ * a) := by rw [hak.inv_right.eq]
      _ = (ι (k ^ 3))⁻¹ * (ι (k ^ 3) * ι x * (ι (k ^ 3))⁻¹ * a) := by group
      _ = (ι (k ^ 3))⁻¹ * (a * ι x) := by rw [he']
      _ = (a * (ι (k ^ 3))⁻¹) * ι x := by rw [← mul_assoc, ← hak.inv_right.eq]
  have hd := Representation.BinaryIrreducibleCentralizer.centralizing_square_one_eq_one
    σ ι.range hf hd2 hdc
  exact ⟨k ^ 3, (mul_inv_eq_one.mp hd).symm⟩

/-- Three-conjugate generation lifts from the central quotient to its perfect cover. -/
theorem tripleSeven_three_conjugates_of_alternating
    (hgen : ∀ a : alternatingGroup (Fin 7), a ≠ 1 → a ^ 2 = 1 →
      ∃ g h : alternatingGroup (Fin 7),
        zpowers a ⊔ zpowers (g * a * g⁻¹) ⊔ zpowers (h * a * h⁻¹) = ⊤)
    (a : TripleSeven) (ha : a ≠ 1) (ha2 : a ^ 2 = 1) :
    ∃ g h : TripleSeven, zpowers a ⊔ zpowers (g * a * g⁻¹) ⊔
      zpowers (h * a * h⁻¹) = ⊤ := by
  have hqa : tripleSevenProjection a ≠ 1 := by
    intro he
    have hc : a ∈ center TripleSeven := projection_ker ▸ he
    have ha3 := center_cube a hc
    have heq : a = 1 := by
      simpa only [pow_succ, ha2, one_mul] using ha3
    exact ha heq
  have hqa2 : (tripleSevenProjection a) ^ 2 = 1 := by rw [← map_pow, ha2, map_one]
  obtain ⟨g, h, hgh⟩ := hgen (tripleSevenProjection a) hqa hqa2
  obtain ⟨g, rfl⟩ := tripleSevenProjection_surjective g
  obtain ⟨h, rfl⟩ := tripleSevenProjection_surjective h
  refine ⟨g, h, top_unique ?_⟩
  apply le_of_map_le_of_perfect tripleSevenProjection projection_ker.le
  rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hgh]
  exact le_top

/-- Exact normalizer contract, reduced solely to generation in the ordinary A₇. -/
theorem normalizerGeometry_of_alternating_generation
    (hgen : ∀ a : alternatingGroup (Fin 7), a ≠ 1 → a ^ 2 = 1 →
      ∃ g h : alternatingGroup (Fin 7),
        zpowers a ⊔ zpowers (g * a * g⁻¹) ⊔ zpowers (h * a * h⁻¹) = ⊤) :
    NormalizerGeometry.{v,w} := by
  intro H W _ _ _ _ _ ι hi hn σ hf hirr
  refine ⟨elementary_card_le_eight ι hi hn σ hf hirr, ?_⟩
  intro a ha ha2 hac
  obtain ⟨b, rfl⟩ := involution_mem_range ι hi hn σ hf hirr a ha2 hac
  have hb : b ≠ 1 := by intro he; exact ha (he ▸ map_one ι)
  have hb2 : b ^ 2 = 1 := hi (by rw [map_pow, ha2, map_one])
  obtain ⟨g, h, hgh⟩ := tripleSeven_three_conjugates_of_alternating hgen b hb hb2
  refine ⟨ι g, ι h, ?_⟩
  have he := congrArg (Subgroup.map ι) hgh
  rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers, ← MonoidHom.range_eq_map] at he
  simpa only [map_mul, map_inv] using he.ge

/-- The full normalizer geometry of a faithfully and irreducibly acting triple
cover of A₇, with both the elementary-order bound and three-conjugate generation. -/
theorem normalizerGeometry : NormalizerGeometry.{v,w} :=
  normalizerGeometry_of_alternating_generation
    alternatingGroup.SevenInvolutionGeneration.three_conjugates_generate

end CFSG.Quasithin.ChapterB.ComponentRecognition.AlternatingCovers.SevenExclusion
