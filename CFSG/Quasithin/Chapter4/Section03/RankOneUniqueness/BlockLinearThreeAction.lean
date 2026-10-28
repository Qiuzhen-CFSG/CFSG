module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockCrossing
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesPreparation
public import Theory.SpecificGroups.SL3.ParabolicFixer

/-!
# The actual L-image and the special-linear action obstruction

The literal image of L in K/O₂(K) is nontrivial and perfect, and the
core-to-star isomorphism preserves this image with both original inclusions.
If a concrete quotient marking places this image as a standard parabolic
solvable residual, every automorphism fixing it pointwise is the identity.

The placement premise is explicit here and must be discharged by the C.4.1
marking assembly. This module supplies the obstruction used by original
4.3.7; it does not prove the missing placement or the full commutator identity.
Source: Aschbacher--Smith C.4.1(3) and original 4.3.7,
printed pp.151--153 and615--616.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The literal image of L in K/O₂(K), using both original inclusions. -/
abbrev SourceConfiguration.componentQuotientL (c : SourceConfiguration T L) :
    Subgroup (c.K ⧸ pCore 2 c.K) :=
  ((L.subgroupOf c.H).subgroupOf c.K).map (QuotientGroup.mk' (pCore 2 c.K))

omit [Finite G] in
private theorem intrinsic_component_le (c : SourceConfiguration T L) :
    L.subgroupOf c.H ≤ c.K := by
  intro x hx
  obtain ⟨k,hk,he⟩ := c.le_component hx
  exact (Subtype.ext he : k = x) ▸ hk

private noncomputable def originalComponentEquiv (c : SourceConfiguration T L) :
    ((L.subgroupOf c.H).subgroupOf c.K) ≃* L :=
  (subgroupOfEquivOfLe (intrinsic_component_le c)).trans
    (subgroupOfEquivOfLe (c.le_I.trans c.I_le_H))

omit [Finite G] in
private theorem originalComponent_perfect (c : SourceConfiguration T L) :
    Group.IsPerfect ((L.subgroupOf c.H).subgroupOf c.K) := by
  have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
    le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
  let : Group.IsPerfect L := hs ▸ c.c28.span_perfect
  exact Group.IsPerfect.ofSurjective
    (f := (originalComponentEquiv c).symm.toMonoidHom) (originalComponentEquiv c).symm.surjective

omit [Finite G] in
/-- The actual quotient image retains the source component's perfectness. -/
theorem SourceConfiguration.componentQuotientL_perfect (c : SourceConfiguration T L) :
    Group.IsPerfect c.componentQuotientL := by
  let := originalComponent_perfect c
  exact Group.IsPerfect.map (QuotientGroup.mk' (pCore 2 c.K))

/-- The actual L image is nontrivial: a perfect subgroup cannot disappear
in the two-core, and the source supplies a nonzero module inside L. -/
theorem SourceConfiguration.componentQuotientL_ne_bot (c : SourceConfiguration T L) :
    c.componentQuotientL ≠ ⊥ := by
  let A := (L.subgroupOf c.H).subgroupOf c.K
  have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
    le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
  have hL : L ≠ ⊥ := by
    intro he
    have hh := c.c28.module_le
    rw [hs] at hh
    have hh := hh.trans he.le
    exact c.c28.module_nontrivial (bot_unique hh)
  let : Nontrivial L := L.nontrivial_iff_ne_bot.mpr hL
  let : Nontrivial A := (originalComponentEquiv c).toEquiv.nontrivial
  let : Group.IsPerfect A := originalComponent_perfect c
  intro he
  have hA : A ≤ pCore 2 c.K := by
    simpa only [QuotientGroup.ker_mk'] using (map_eq_bot_iff A).mp he
  exact Group.IsPerfect.not_isNilpotent A (pCore_isPGroup.to_le hA).isNilpotent

omit [Finite G] in
/-- The full quotient action has no nonidentity fixer once the actual image
of L is placed as either standard parabolic residual. This does not construct
that placement. -/
theorem SourceConfiguration.quotientAut_eq_one_of_parabolic_image
    (c : SourceConfiguration T L)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (e : (c.K ⧸ pCore 2 c.K) ≃* SL(3,F))
    (he : c.componentQuotientL.map e.toMonoidHom = Matrix.PSL3.LinearThree.pointLocalSL F ∨
      c.componentQuotientL.map e.toMonoidHom = Matrix.PSL3.LinearThree.lineLocalSL F)
    (a : MulAut (c.K ⧸ pCore 2 c.K))
    (ha : ∀ x ∈ c.componentQuotientL, a x = x) : a = 1 := by
  let b := MulAut.congr e a
  have hb : ∀ x ∈ c.componentQuotientL.map e.toMonoidHom, b x = x := by
    rintro x ⟨y,hy,rfl⟩
    change e (a (e.symm (e y))) = e y
    rw [e.symm_apply_apply,ha y hy]
  have hb1 : b = 1 := by
    rcases he with he | he
    · rw [he] at hb
      exact Matrix.PSL3.LinearThree.pointLocalSL_fixer_eq_one hn hF b hb
    · rw [he] at hb
      exact Matrix.PSL3.LinearThree.lineLocalSL_fixer_eq_one hn hF b hb
  exact (MulAut.congr e).injective (hb1.trans (map_one _).symm)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness


open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterC Chapter1.RadicalExclusions.ModelReduction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual L image is preserved by the full core-to-star quotient
isomorphism, with both subgroup restrictions retained. -/
theorem SourceConfiguration.componentQuotientL_star
    (c : SourceConfiguration T L) (hb : IsBlock c.K) :
    c.componentQuotientL.map (c.block_star_quotientEquiv hb).toMonoidHom =
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) L).subgroupOf
        (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)) := by
  ext x
  constructor
  · rintro ⟨y,⟨k,hk,rfl⟩,rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, c.block_star_quotientEquiv_mk]
    refine ⟨⟨((k : c.K) : c.H), ?_⟩, hk, rfl⟩
    exact (show c.K.map c.H.subtype ≤ c.K.map c.H.subtype ⊔ c.I.pCoreIn 2 from le_sup_left)
      (mem_map_of_mem c.H.subtype k.property)
  · intro hx
    change (x : StarQuotient (c.K.map c.H.subtype) (c.I.pCoreIn 2)) ∈
      starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) L at hx
    obtain ⟨j,hj,hx⟩ := hx
    obtain ⟨k,hk,hkj⟩ := c.le_component hj
    let z : c.K := ⟨k,hk⟩
    refine ⟨QuotientGroup.mk' (pCore 2 c.K) z,⟨z,?_,rfl⟩,?_⟩
    · change (k : G) ∈ L
      exact (congrArg (fun y : G => y ∈ L) hkj).mpr hj
    · apply Subtype.ext
      simp only [MulEquiv.coe_toMonoidHom, c.block_star_quotientEquiv_mk]
      change QuotientGroup.mk' (starKernel (c.K.map c.H.subtype) (c.I.pCoreIn 2))
        ⟨(k : G),_⟩ = _
      rw [← hx]
      exact congrArg (QuotientGroup.mk' _ ) (Subtype.ext hkj)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
