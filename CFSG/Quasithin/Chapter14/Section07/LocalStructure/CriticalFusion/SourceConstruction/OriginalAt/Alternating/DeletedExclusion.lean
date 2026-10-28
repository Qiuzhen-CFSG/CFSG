module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.DeletedExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.AlternatingBranch

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingBranch
public import Theory.Representation.BinaryAlternatingFiveBorel
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.SpecificGroups.Alternating.FiveOrderTwentyFour
public import Theory.GroupTheory.SubgroupPartitionCounting

/-!
# Deleted-module exclusion at the same G,T

The point parabolic maps to an actual point stabilizer in every S₅ marking. Seed separation would embed the seed plane in its deleted-module commutator space. The checked absence of an invariant plane excludes that quotient.

Only Structural1222At at the original G,T is used. Independent model and
section lemmas are reused from LocalReduction; its universal APIs are preserved.
Source: Aschbacher–Smith, final paragraph of 14.7.40, printed p.1063,
and 14.7.52–63, printed pp.1065–1069. Earlier structural source discharge
and the unconditional classification remain with their existing owners.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
local notation "S5" => ChapterJ.S5
local notation "D" => BinaryPermutation.core (Fin 5)
local notation "δ" => BinaryPermutation.coreRepresentation (Fin 5)

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
local notation "B" => (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)

/-- Under every star marking, the original point parabolic is a literal
point stabilizer in S₅. -/
theorem point_image_stabilizer_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (e : HStar F.H ≃* S5) :
    ∃ i : Fin 5, ((B).subgroupOf F.H).map (quotientMarking e) =
      MulAction.stabilizer S5 i := by
  let I := ((B).subgroupOf F.H).map (quotientMarking e)
  have hker : (quotientMarking e).ker ≤ (B).subgroupOf F.H := by
    rw [quotientMarking, MonoidHom.ker_comp_of_injective _ _ e.injective,
      starMap, QuotientGroup.ker_mk']
    intro a ha
    exact pCoreIn_le 2 B (core_le_point_core (mem_map_of_mem _ ha))
  have hi : I.index = 5 := by
    dsimp only [I]
    rw [index_map_eq _ (e.surjective.comp (QuotientGroup.mk'_surjective _)) hker]
    exact point_index_five_at h structural e
  have hc := I.card_mul_index
  have hs : Nat.card S5 = 120 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  rw [hi, hs] at hc
  have hc' : Nat.card I * 5 = 120 := hc
  have hcard : Nat.card I = 24 := by omega
  exact Theory.SpecificGroups.Alternating.FivePointTwentyFour.exists_eq_stabilizer I hcard

/-- The original seed plane excludes every surjective deleted-permutation
quotient of the literal U/V₁ action. -/
theorem no_deleted_quotient_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (e : HStar F.H ≃* S5)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap ((δ).comp (quotientMarking e))) : ¬ Function.Surjective p := by
  intro hp
  let : Finite W := Finite.of_surjective (fun u : F.U => (c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let X := c.imageSpace V
  let P := X.map p.toLinearMap
  have hVU : V ≤ F.U := le_conjugateSpanBy V F.H
  have hdim : Module.finrank (ZMod 2) X = 2 := by
    apply c.imageSpace_finrank_of_index V hVU 2
    have hc := relIndex_mul_card_of_le (F.le_seed 1)
    have hV : Nat.card V = 8 := by simpa only [F.last, Nat.reducePow] using F.card 3 (by decide)
    have hP : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    rw [hV, hP] at hc
    norm_num at hc ⊢
    omega
  have hkproper : p.toLinearMap.ker ≠ ⊤ := by
    intro hk
    have hz : p.toLinearMap = 0 := LinearMap.ker_eq_top.mp hk
    have hr := LinearMap.range_eq_top.mpr hp
    rw [hz, LinearMap.range_zero] at hr
    have hd : Module.finrank (ZMod 2) D = 4 := by
      rw [BinaryPermutation.finrank_core]
      rfl
    have hb := congrArg (fun Q : Submodule (ZMod 2) D => Module.finrank (ZMod 2) Q) hr
    simp only [finrank_bot, finrank_top] at hb
    omega
  have hki : ∀ g w, w ∈ p.toLinearMap.ker → ρ g w ∈ p.toLinearMap.ker := by
    intro g w hw
    change p (ρ g w) = 0
    rw [p.isIntertwining, show p w = 0 from hw, map_zero]
  have hinj : Disjoint X p.toLinearMap.ker := by
    apply Submodule.disjoint_def.mpr
    intro w hw hk
    obtain ⟨v,hv,rfl⟩ := (c.mem_imageSpace_iff V w).mp hw
    have hvp := (seed_intersection h c p.toLinearMap.ker hki hkproper v hv).mp hk
    exact (c.coordinates_eq_one_iff v).mpr hvp
  have hPdim : Module.finrank (ZMod 2) P = 2 := by
    let f := p.toLinearMap.comp X.subtype
    have hf : Function.Injective f := by
      apply (LinearMap.ker_eq_bot).mp
      apply bot_unique
      intro x hx
      apply Subtype.ext
      exact (Submodule.disjoint_def.mp hinj) x.val x.property hx
    have hr : LinearMap.range f = P := by
      dsimp only [f]
      rw [LinearMap.range_comp, Submodule.range_subtype]
    exact hr ▸ (LinearMap.finrank_range_of_inj hf).trans hdim
  obtain ⟨i,hi⟩ := point_image_stabilizer_at h structural e
  have hBH : B ≤ F.H := sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
  have hBV : B ≤ normalizer (V : Set G) :=
    sup_le ((F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes))
      (by simpa only [F.last] using F.invariant 3)
  have hX : ∀ b : F.H, (b : G) ∈ B → ∀ w ∈ X, ρ b w ∈ X := by
    intro b hb w hw
    obtain ⟨v,hv,rfl⟩ := (c.mem_imageSpace_iff V w).mp hw
    refine (c.mem_imageSpace_iff V _).mpr ⟨⟨b*v*(b:G)⁻¹,
      (mem_normalizer_iff.mp (c.normalized b.property) v).mp v.property⟩,
      (mem_normalizer_iff.mp (hBV hb) v).mp hv, c.equivariant b v⟩
  have hPstable : ∀ g : S5, g i = i → ∀ v ∈ P, δ g v ∈ P := by
    intro g hg v hv
    have hgm : g ∈ ((B).subgroupOf F.H).map (quotientMarking e) := by
      rw [hi]; exact hg
    obtain ⟨b,hb,rfl⟩ := hgm
    obtain ⟨w,hw,rfl⟩ := hv
    exact ⟨ρ b w, hX b hb w hw, LinearMap.congr_fun (p.isIntertwining' b) w⟩
  have hzero : ∀ v ∈ P, v.val i = 0 := by
    let N : Submodule (ZMod 2) W :=
      ((LinearMap.proj i).comp ((BinaryPermutation.core (Fin 5)).subtype.comp p.toLinearMap)).ker
    have hXN : X ≤ N := by
      dsimp only [X]
      have he : c.imageSpace V = c.imageSpace ⁅F.Li L 1, V⁆ :=
        congrArg c.imageSpace ((seed_commutator h F).trans (commutator_comm V (F.Li L 1)))
      rw [he, c.imageSpace_commutator
        (F.Li L 1) V ((F.Li_le L 1).trans inf_le_right) hVU]
      apply Submodule.span_le.mpr
      rintro _ ⟨b,hb,w,hw,rfl⟩
      change (p (ρ b w - w)).val i = 0
      rw [map_sub, p.isIntertwining]
      have hbi : quotientMarking e b i = i := by
        have hm : quotientMarking e b ∈ ((B).subgroupOf F.H).map (quotientMarking e) :=
          mem_map_of_mem _ (show (b:G) ∈ B from mem_sup_left hb)
        rw [hi] at hm
        exact hm
      change (p w).val ((quotientMarking e b)⁻¹ i) - (p w).val i = 0
      rw [show (quotientMarking e b)⁻¹ i = i from
        (quotientMarking e b).symm_apply_eq.mpr hbi.symm, sub_self]
    rintro _ ⟨w,hw,rfl⟩
    exact hXN hw
  exact deleted_point_no_plane i P hPstable hzero hPdim

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
