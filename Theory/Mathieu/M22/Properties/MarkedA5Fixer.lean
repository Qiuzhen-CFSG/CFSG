module

public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Nonsplit.FixedVectors
public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Natural.Coordinates
public import Theory.Mathieu.M22.ChapterHLocalClassification.Sylow.Centralizers
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Automorphisms.Compatibility
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.NaturalQuotient.Geometry
public import Theory.GroupTheory.SylowCentralizerOfNormalizer

-- Intentional internal extension: reuse the certified hexacode fixed-vector
-- proof and its literal lifts without widening shared implementation APIs.
import all Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Nonsplit.FixedVectors
import all Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Natural.Coordinates

/-!
# Involutory fixers of the literally marked E16:A5 subgroup in M22

In the compatible outer Sylow, an element centralizing the inner translations
belongs to the outer translation module. The literal tetrad-pointwise actor
has no common fixed vector there. This actor is normal in the quintet, and the
compatible Sylow normalizes it. Sylow restriction in its centralizer therefore
removes the Sylow-membership condition for every square-one fixing element.

The original pair-to-automorphism equivalence and faithful central-quotient
action transport this calculation to perfect covers, retaining the actual
image of the marked subgroup. An abstract E16:A5 carrier tag is not an input.

Source: Aschbacher--Smith 10.2.9, pp.750--751, A.3.14, pp.48--49, and H.14.3,
p.397. The imported hexacode certificates reuse the licensed ATLAS ports;
see the attribution in Quintet.Nonsplit.FixedVectors and LICENSES/ATLAS.txt.
-/

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode Atlas.Codes
open scoped Pointwise
namespace Sporadic.Mathieu.M22ChapterH.Quintet
open Sextet
set_option maxRecDepth 4096

private theorem actor_mem_naturalActor (g : hexPointKernel (hexPos 0)) :
    actor g ∈ naturalActor := by
  apply (mem_naturalActor_iff _).mpr
  intro k
  rw [actor_coe]
  have hp : naturalPointCoordinates (naturalIndex,k) =
      m22GeometryConjugator.val (atlasPointEquiv (hexPos 0,k)) := by
    change (atlasPointEquiv.trans m22GeometryConjugator.val) (naturalIndex,k) = _
    rw [Equiv.trans_apply]
    apply congrArg m22GeometryConjugator.val
    apply congrArg atlasPointEquiv
    apply congrArg (fun i : HexIndex => (i,k))
    rfl
  rw [hp]
  exact lift_fixed_row g k

/-- The actual E16:A5 actor fixes no outer translation except zero. -/
public theorem outerTranslationConjugation_naturalActor_fixed_eq_zero
    (v : Additive outerTranslationGroup)
    (hv : ∀ g : naturalActor, outerTranslationConjugation g.val v = v) : v = 0 := by
  obtain ⟨u, hu⟩ := sourceTranslationEquiv.surjective
    (⟨v.toMul.val.val, v.toMul.property⟩ : sourceCore)
  have he : (sourceTranslationEquiv u).val = v.toMul.val.val := congrArg Subtype.val hu
  have hw (g : hexPointKernel (hexPos 0)) : hexAction g.val.val u.toAdd = u.toAdd := by
    have hf := congrArg (fun w : Additive outerTranslationGroup => w.toMul.val.val)
      (hv ⟨actor g, actor_mem_naturalActor g⟩)
    rw [outer_action_ambient, actor_coe] at hf
    have hc : (lift g.val.val).val * (sourceTranslationEquiv u).val *
        (lift g.val.val).val⁻¹ = (sourceTranslationEquiv u).val := by
      calc
        _ = (lift g.val.val).val * v.toMul.val.val * (lift g.val.val).val⁻¹ :=
          congrArg (fun x : M24 => (lift g.val.val).val * x * (lift g.val.val).val⁻¹) he
        _ = v.toMul.val.val := hf
        _ = _ := he.symm
    have hh := word_fixed_of_conjugation (lift g.val.val) u.toAdd hc
    rw [lift_quotient] at hh
    exact hh
  have hz : u = 1 := congrArg Multiplicative.ofAdd (hex_fixed_zero u.toAdd hw)
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  change v.toMul.val.val = 1
  rw [← he, hz, map_one]
  rfl

private theorem innerTranslationGroup_le_naturalActor_image :
    innerTranslationGroup ≤ naturalActor.map M22Quintet.Q.subtype := by
  intro x hx
  obtain ⟨w, hw⟩ := naturalTranslation_bijective.2 (⟨x,hx⟩ : innerTranslationGroup)
  let a := naturalActorEquiv (SemidirectProduct.inl w)
  refine ⟨a.val,a.property,?_⟩
  change (naturalActorInclusion (SemidirectProduct.inl w)).val = x
  exact (naturalActorInclusion_inl w).trans (congrArg Subtype.val hw)

/-- The marked actor has trivial centralizer inside the compatible outer Sylow. -/
public theorem pair_eq_one_of_mem_outer_centralizes_naturalActor
    (g : m22PairStabilizer) (hg : g ∈ CompatibleSylow.outer.toSubgroup)
    (hc : ∀ a : naturalActor, g * a.val.val = a.val.val * g) : g = 1 := by
  have ht : g ∈ outerTranslationGroup := by
    apply CompatibleSylow.centralizer_translations g hg
    intro x hx
    have hm : m22ToPairStabilizer x ∈ innerTranslationGroup := by
      rw [← innerTranslations_map]
      exact ⟨x,hx,rfl⟩
    obtain ⟨a,ha,he⟩ := innerTranslationGroup_le_naturalActor_image hm
    have hh := hc ⟨a,ha⟩
    change g * a.val = a.val * g at hh
    change a.val = m22ToPairStabilizer x at he
    rw [he] at hh
    exact congrArg Subtype.val hh
  have hz := outerTranslationConjugation_naturalActor_fixed_eq_zero
    (Additive.ofMul (⟨g,ht⟩ : outerTranslationGroup)) (by
      intro a
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [outerTranslationConjugation_apply]
      exact mul_inv_eq_iff_eq_mul.mpr (hc a).symm)
  exact congrArg (fun v : Additive outerTranslationGroup => v.toMul.val) hz


private theorem naturalActor_normal_in_quintet : naturalActor.Normal := by
  refine ⟨fun a ha g => ?_⟩
  apply (mem_naturalActor_iff _).mpr
  intro k
  have ht := congrArg Subtype.val
    (M22Quintet.CocodeTransfer.NaturalQuotient.partAction_fixes_first g⁻¹)
  change g.val.val⁻¹ • m22SourceTetrad 0 = m22SourceTetrad 0 at ht
  have hp : naturalPointCoordinates (naturalIndex,k) ∈ m22SourceTetrad 0 := by
    rw [←naturalActor_tetrad]
    exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
  have hm : g.val.val⁻¹ • naturalPointCoordinates (naturalIndex,k) ∈
      m22SourceTetrad 0 := by
    rw [←ht]
    exact Finset.smul_mem_smul_finset hp
  rw [←naturalActor_tetrad] at hm
  obtain ⟨j,_,he⟩ := Finset.mem_image.mp hm
  have hf := (mem_naturalActor_iff a).mp ha j
  change g.val.val.val (a.val.val.val
    (g.val.val.val.symm (naturalPointCoordinates (naturalIndex,k)))) = _
  change naturalPointCoordinates (naturalIndex,j) =
    g.val.val.val.symm (naturalPointCoordinates (naturalIndex,k)) at he
  rw [←he,hf,he,Equiv.apply_symm_apply]

/-- The compatible outer Sylow normalizes the literal pair image of E16:A5. -/
public theorem outer_le_naturalActorPair_normalizer : CompatibleSylow.outer.toSubgroup ≤
    Subgroup.normalizer (naturalActor.map M22Quintet.Q.subtype : Set m22PairStabilizer) := by
  let : naturalActor.Normal := naturalActor_normal_in_quintet
  have hn := naturalActor.le_normalizer_map M22Quintet.Q.subtype
  rw [Subgroup.normalizer_eq_top,←MonoidHom.range_eq_map,Subgroup.range_subtype] at hn
  apply le_trans _ hn
  intro g hg
  exact CompatibleSylow.ambient_le_sextet hg

/-- No nontrivial square-one pair element centralizes the marked actor. -/
public theorem pair_involutory_eq_one_of_centralizes_naturalActor
    (g : m22PairStabilizer) (hg : g ^ 2 = 1)
    (hc : ∀ a : naturalActor, g * a.val.val = a.val.val * g) : g = 1 := by
  let B := naturalActor.map M22Quintet.Q.subtype
  let C := Subgroup.centralizer (B : Set m22PairStabilizer)
  have he : CompatibleSylow.outer.toSubgroup ⊓ C = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply pair_eq_one_of_mem_outer_centralizes_naturalActor x hx.1
    intro a
    exact (hx.2 a.val.val ⟨a.val,a.property,rfl⟩).symm
  obtain ⟨P,hP⟩ := CompatibleSylow.outer.exists_centralizer_sylow_of_normalizes B
    outer_le_naturalActorPair_normalizer
  have hpb : (P : Subgroup C) = ⊥ := by
    apply Subgroup.map_injective (f := C.subtype) C.subtype_injective
    rw [hP,he,Subgroup.map_bot]
  have hgc : g ∈ C := by
    rintro _ ⟨a,ha,rfl⟩
    exact (hc ⟨a,ha⟩).symm
  let x : C := ⟨g,hgc⟩
  have hx : x ^ 2 = 1 := Subtype.ext hg
  have hz : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hx)
  obtain ⟨R,hR⟩ := hz.exists_le_sylow
  have hxR : x ∈ R := hR (Subgroup.mem_zpowers x)
  let e := R.equiv P
  have hy : e ⟨x,hxR⟩ = 1 := by
    apply Subtype.ext
    have hp := (e ⟨x,hxR⟩).property
    change (e ⟨x,hxR⟩).val ∈ (P : Subgroup C) at hp
    exact Subgroup.mem_bot.mp (hpb.le hp)
  have hxone : (⟨x,hxR⟩ : R) = 1 := e.injective (hy.trans e.map_one.symm)
  exact congrArg (fun y : R => y.val.val) hxone

end Sporadic.Mathieu.M22ChapterH.Quintet

public section
namespace Sporadic.Mathieu
open Subgroup MathieuCode M22ChapterH

/-- A literal marked A5 block has trivial pointwise fixer for involutory automorphisms. The original pair-to-automorphism equivalence is retained. -/
theorem m22_marked_involutory_fixer_eq_one (B : Subgroup M22)
    (hB : Quintet.naturalActor.map M22Quintet.Q.subtype ≤ B.map m22ToPairStabilizer)
    (a : MulAut M22)
    (ha : a ^ 2 = 1)
    (hfix : ∀ b ∈ B, a b = b) : a = 1 := by
  let g := m22PairStabilizerEquivAut.symm a
  have hs : g ^ 2 = 1 := by
    change (m22PairStabilizerEquivAut.symm a) ^ 2 = 1
    rw [←map_pow,ha,map_one]
  have hg : g = 1 := Quintet.pair_involutory_eq_one_of_centralizes_naturalActor g hs (by
    intro x
    have hm : x.val.val ∈ B.map m22ToPairStabilizer := hB ⟨x.val,x.property,rfl⟩
    obtain ⟨b,hb,he⟩ := hm
    rw [←he]
    apply Subtype.ext
    change g.val * m22Embedding b = m22Embedding b * g.val
    have hh := m22PairStabilizerEquivAut_apply g b
    rw [m22PairStabilizerEquivAut.apply_symm_apply, hfix b hb] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh.symm)
  have hh := congrArg m22PairStabilizerEquivAut hg
  simpa only [g,MulEquiv.apply_symm_apply,map_one] using hh

/-- Central-cover transport for the actual marked A5 block. The action
representative, quotient image and Sylow marking are all literal. -/
theorem m22_perfect_cover_marked_involutory_fixer_eq_one
    {K : Type*} [Group K] [Group.IsPerfect K]
    (e : K ⧸ center K ≃* M22) (L : Subgroup K)
    (hB : Quintet.naturalActor.map M22Quintet.Q.subtype ≤
      ((L.map (QuotientGroup.mk' (center K))).map e.toMonoidHom).map m22ToPairStabilizer)
    (a : MulAut K)
    (ha : a ^ 2 = 1)
    (hfix : ∀ l ∈ L, a l = l) : a = 1 := by
  let B := (L.map (QuotientGroup.mk' (center K))).map e.toMonoidHom
  have hf : ∀ b ∈ B, MulAut.centralQuotientAction e a b = b := by
    rintro _ ⟨x, ⟨l,hl,rfl⟩,rfl⟩
    change MulAut.centralQuotientAction e a
      (e (QuotientGroup.mk' (center K) l)) = e (QuotientGroup.mk' (center K) l)
    rw [MulAut.centralQuotientAction_apply,hfix l hl]
  apply MulAut.centralQuotientAction_injective e
  rw [map_one]
  have hs : (MulAut.centralQuotientAction e a) ^ 2 = 1 := by
    rw [←map_pow,ha,map_one]
  exact m22_marked_involutory_fixer_eq_one B hB _ hs hf

end Sporadic.Mathieu
