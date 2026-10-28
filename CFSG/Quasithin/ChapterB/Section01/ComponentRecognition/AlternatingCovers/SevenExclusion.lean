module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.AlternatingCovers.SevenExclusion.ModelInputs
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.AlternatingCovers.SevenExclusion.Degree
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.AlternatingCovers.SevenExclusion.NormalizerGeometry
public import Theory.Representation.BinaryOffender.NormalThree
public import Theory.Representation.SL2SevenCentralProductOffenders
public import Theory.Representation.Quotient
public import Theory.Frattini.OmegaProducts

/-!
# Faithful irreducible triple-seven FF exclusion

Schur's lemma makes the cubic center move the entire faithful irreducible
module. A quadratic offender moving this center would have rank one and
force degree at most two. Otherwise it centralizes the center. Three
conjugates of any nonidentity involution in that offender generate the
component, so the elementary-order bound eight forces degree at most nine.
The independent degree lower bound ten then gives the contradiction.

The final adapter uses the actual isomorphism to the universal-cover quotient
and the literal faithful action image. The proved degree and normalizer
geometry theorems discharge both model inputs, giving `SevenFFExclusion`
without any additional premise. The source section construction remains with
the B.1.13 assembly: its restriction must be faithful and irreducible.

Source: Aschbacher–Smith, B.1.13, printed p.74; K.1, printed p.452,
and its reference to Guralnick–Malle, Theorem 6.2 and Table 6.3.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.AlternatingCovers.SevenExclusion
open GLS3.Chapter5.OddCentralCovers
universe u v w

private theorem center_image_normal {L H : Type*} [Group L] [Group H]
    (ι : L →* H) (hi : Function.Injective ι) (hn : ι.range.Normal) :
    ((center L).map ι).Normal := by
  let := hn
  let e : L ≃* ι.range := MonoidHom.ofInjective hi
  have he : (center L).map ι = (center ι.range).map ι.range.subtype := by
    rw [← center_map_equiv e, map_map]
    rfl
  rw [he]
  exact ConjAct.normal_of_characteristic_of_normal

private theorem center_moves {L H W : Type*} [Group L] [Group H]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ι : L →* H) (σ : Representation (ZMod 2) H W)
    (hf : Function.Injective (σ.comp ι)) (hirr : Representation.IsIrreducible (σ.comp ι))
    (hc : Nat.card (center L) = 3) :
    subspaceCommutator σ ⊤ ((center L).map ι) = ⊤ := by
  let := hirr
  have hn : center L ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hc
    omega
  obtain ⟨z, hz, hz1⟩ := (center L).bot_or_exists_ne_one.resolve_left hn
  let τ := σ.comp ι
  let f : Representation.IntertwiningMap τ τ := {
    toLinearMap := τ z - 1
    isIntertwining' := by
      intro l
      ext v
      change τ z (τ l v) - τ l v = τ l (τ z v - v)
      rw [map_sub]
      have he := congrArg (fun x : L => τ x v) ((mem_center_iff.mp hz l).symm)
      exact congrArg (fun x : W => x - τ l v) (by
        simpa only [map_mul, Module.End.mul_apply] using he) }
  have hfi : Function.Injective f := by
    rcases Representation.IsIrreducible.injective_or_eq_zero f with h | h
    · exact h
    · exfalso
      apply hz1
      apply hf
      change τ z = τ 1
      rw [map_one]
      ext v
      have he := congrArg (fun q : Representation.IntertwiningMap τ τ => q v) h
      exact sub_eq_zero.mp he
  have hfs : Function.Surjective f := LinearMap.surjective_of_injective hfi
  apply top_unique
  intro v _
  obtain ⟨w, hw⟩ := hfs v
  rw [← hw]
  exact Submodule.subset_span ⟨ι z, mem_map_of_mem ι hz, w, Submodule.mem_top, rfl⟩

/-- Quadratic replacement centralizes a fully moving normal cubic subgroup
as soon as the degree exceeds two. -/
theorem quadratic_offender_centralizes_cubic
    {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) H W)
    (hf : Function.Injective σ) (Z : Subgroup H) (hn : Z.Normal)
    (hc : Nat.card Z = 3) (hm : subspaceCommutator σ ⊤ Z = ⊤)
    (hd : 2 < Module.finrank (ZMod 2) W)
    (A : Subgroup H) (hA : IsOffender σ A) (hq : IsQuadratic σ A) :
    A ≤ centralizer (Z : Set H) := by
  by_contra hnot
  obtain ⟨hr, he⟩ := normalThree_quadratic_rank_fixedCodim σ hf Z hn hc hm A hA.1 hq hnot
  have ho := hA.2
  omega

/-- A cubic-center reduction of FF exclusion. The inputs concern dimension,
subgroup orders and generation; the argument derives the offender contradiction. -/
theorem not_ff_of_cubic_and_three_conjugates
    {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) H W)
    (hf : Function.Injective σ) (L Z : Subgroup H) (hn : Z.Normal)
    (hc : Nat.card Z = 3) (hm : subspaceCommutator σ ⊤ Z = ⊤) (hZL : Z ≤ L)
    (hd : 10 ≤ Module.finrank (ZMod 2) W)
    (hcard : ∀ A : Subgroup H, IsElementaryAbelian 2 A → Nat.card A ≤ 8)
    (hgen : ∀ a : H, a ≠ 1 → a ^ 2 = 1 → a ∈ centralizer (Z : Set H) →
      ∃ g h : H, L ≤ zpowers a ⊔ zpowers (g * a * g⁻¹) ⊔ zpowers (h * a * h⁻¹)) :
    ¬ IsFFModule σ := by
  rintro ⟨A, hA⟩
  obtain ⟨B, _, hB, hq, _⟩ := hA.exists_quadratic_minimalBestOffender σ
  have ho := hB.1.isOffender σ
  have hcent := quadratic_offender_centralizes_cubic σ hf Z hn hc hm (by omega) B ho hq
  let : IsElementaryAbelian 2 B := ho.1.2
  obtain ⟨a, ha, ha1⟩ := B.bot_or_exists_ne_one.resolve_left ho.1.1
  obtain ⟨g, h, hgh⟩ := hgen a ha1 (elemPow_eq_one_of_isElementaryAbelian a ha) (hcent ha)
  have hLmove : subspaceCommutator σ ⊤ L = ⊤ := by
    apply top_unique
    calc
      ⊤ = subspaceCommutator σ ⊤ Z := hm.symm
      _ ≤ subspaceCommutator σ ⊤ L := by
        apply Submodule.span_mono
        rintro v ⟨z, hz, w, hw, rfl⟩
        exact ⟨z, hZL hz, w, hw, rfl⟩
  have hupper := SL2SevenCentralProduct.finrank_le_three_mul_fixedCodim_of_three_conjugates
    σ L hLmove a g h hgh
  have hr : rank B ≤ 3 := by
    have hh := Nat.log_mono_right (b := 2) (hcard B ho.1.2)
    simpa only [rank, show Nat.log 2 8 = 3 from by decide] using hh
  have hfixed := Submodule.finrank_mono (fixedSpace_antitone σ (zpowers_le.mpr ha))
  have hdimB := fixedCodim_add_finrank σ B
  have hdima := fixedCodim_add_finrank σ (zpowers a)
  have hcodim := ho.2
  omega

/-- Application to the actual triple-seven carrier, keeping its two independent
model inputs explicit. -/
theorem model_not_ff (hdegree : DegreeBound.{w}) (hgeometry : NormalizerGeometry.{v,w})
    {H : Type v} {W : Type w} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (ι : TripleSeven →* H)
    (hi : Function.Injective ι) (hn : ι.range.Normal)
    (σ : Representation (ZMod 2) H W) (hf : Function.Injective σ)
    (hirr : Representation.IsIrreducible (σ.comp ι)) : ¬ IsFFModule σ := by
  obtain ⟨hcard, hgen⟩ := hgeometry ι hi hn σ hf hirr
  apply not_ff_of_cubic_and_three_conjugates σ hf ι.range ((center TripleSeven).map ι)
    (center_image_normal ι hi hn) _ (center_moves ι σ (hf.comp hi) hirr tripleSeven_center_card)
    (map_le_range _ _) (hdegree (σ.comp ι) (hf.comp hi) hirr) hcard hgen
  rw [card_map_of_injective hi, tripleSeven_center_card]

/-- The literal source contract follows from the degree and normalizer model
facts. This includes passage to the faithful action image and transport from
an arbitrary quasisimple triple cover. -/
theorem sevenFFExclusion_of_degree_and_geometry
    (hdegree : DegreeBound.{w}) (hgeometry : NormalizerGeometry.{w,w}) :
    SevenFFExclusion.{u,v,w} := by
  intro L H W _ _ _ _ _ _ _ _ ι hi hn σ he hc hf hirr
  obtain ⟨e⟩ := triple_seven_equiv he.some hc
  let j : TripleSeven →* actionImage σ := (actionHom σ).comp (ι.comp e.symm.toMonoidHom)
  have hj : Function.Injective j := by
    intro a b hab
    apply e.symm.injective
    apply hf
    exact congrArg (imageRepresentation σ) hab
  have heq : j.range = ι.range.map (actionHom σ) := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp,
      e.symm.toMonoidHom.range_eq_top_of_surjective e.symm.surjective,
      ← MonoidHom.range_eq_map]
  have hjn : j.range.Normal := by
    rw [heq]
    exact hn.map (actionHom σ) σ.asGroupHom.rangeRestrict_surjective
  have hjirr : Representation.IsIrreducible ((imageRepresentation σ).comp j) :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (σ.comp ι)).mpr hirr
  exact model_not_ff hdegree hgeometry j hj hjn (imageRepresentation σ)
    (imageRepresentation_injective σ) hjirr

/-- A faithful irreducible binary representation of a quasisimple triple cover
of A₇ has no FF extension to a finite normalizing overgroup. This is the exact
intrinsic exclusion used in B.1.13, with the degree and geometry inputs proved. -/
theorem sevenFFExclusion : SevenFFExclusion.{u,v,w} :=
  sevenFFExclusion_of_degree_and_geometry degreeBound normalizerGeometry

end CFSG.Quasithin.ChapterB.ComponentRecognition.AlternatingCovers.SevenExclusion
