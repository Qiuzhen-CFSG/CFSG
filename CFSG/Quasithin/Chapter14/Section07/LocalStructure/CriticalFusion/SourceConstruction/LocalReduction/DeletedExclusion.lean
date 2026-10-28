module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingBranch
public import Theory.Representation.BinaryAlternatingFiveBorel
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.SpecificGroups.Alternating.FiveOrderTwentyFour
public import Theory.GroupTheory.SubgroupPartitionCounting

/-!
# Excluding the deleted five-point quotient before natural recognition

Every S₅ marking sends the original point parabolic L₁T onto an actual
point stabilizer. A surjective equivariant map from U/V₁ to the deleted
five-point module would be injective on the original seed plane, by seed
separation. Commutator generation places its image in the three-dimensional
point-stabilizer commutator module. That module has no invariant plane.

The coordinate permutation moving the marked point to the fifth point
transports the checked A₄ calculation, so the exclusion applies to every
star marking and every literal conjugation section. No Data record or
natural quotient is assumed. This proves the deleted-module exclusion in
the final paragraph of 14.7.40; it does not classify all chief factors or
exclude the case of two noncentral natural chief factors.

Source: Aschbacher–Smith, proof of 14.7.40, printed p.1063. The underlying
A₄ calculation is shared with the proof of 13.6.15, printed p.930.
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

/-- The deleted five-point module has no invariant plane in the point-stabilizer
commutator three-space, at any of the five points. -/
theorem deleted_point_no_plane (i : Fin 5) (P : Submodule (ZMod 2) D)
    (hP : ∀ g : S5, g i = i → ∀ v ∈ P, δ g v ∈ P)
    (hzero : ∀ v ∈ P, (v : Fin 5 → ZMod 2) i = 0) :
    Module.finrank (ZMod 2) P ≠ 2 := by
  let s : S5 := Equiv.swap i 4
  let e : D ≃ₗ[ZMod 2] D := {
    toLinearMap := δ s
    invFun := δ s⁻¹
    left_inv := by
      intro v
      have he := congrArg (fun f : Module.End (ZMod 2) D => f v) ((δ).map_mul s⁻¹ s)
      rw [inv_mul_cancel, map_one] at he
      exact he.symm
    right_inv := by
      intro v
      have he := congrArg (fun f : Module.End (ZMod 2) D => f v) ((δ).map_mul s s⁻¹)
      rw [mul_inv_cancel, map_one] at he
      exact he.symm }
  let Q := P.map e.toLinearMap
  have hQ : Q ≤ BinaryPermutation.AlternatingFiveBorel.moved := by
    rintro _ ⟨v,hv,rfl⟩
    rw [BinaryPermutation.AlternatingFiveBorel.mem_moved]
    change (δ s v).val 4 = 0
    rw [BinaryPermutation.coreRepresentation_apply, BinaryPermutation.representation_apply]
    change v.val (s⁻¹ 4) = 0
    simpa only [s, Equiv.swap_inv, Equiv.swap_apply_right] using hzero v hv
  let R := Q.comap BinaryPermutation.AlternatingFiveBorel.moved.subtype
  have hR : ∀ g : BinaryPermutation.AlternatingFiveBorel.B, ∀ v ∈ R,
      BinaryPermutation.AlternatingFiveBorel.movedRepresentation g v ∈ R := by
    intro g v hv
    obtain ⟨w,hw,he⟩ := hv
    let a : S5 := s⁻¹ * g.val.val * s
    have hai : a i = i := by
      change s⁻¹ (g.val.val (s i)) = i
      rw [show s i = 4 from Equiv.swap_apply_left _ _, (show g.val.val 4 = 4 from g.property)]
      exact Equiv.swap_apply_right _ _
    refine ⟨δ a w, hP a hai w hw, ?_⟩
    change δ s (δ a w) = (BinaryPermutation.AlternatingFiveBorel.movedRepresentation g v).val
    rw [BinaryPermutation.AlternatingFiveBorel.movedRepresentation_apply]
    change δ s (δ a w) = δ g.val.val v.val
    rw [← show δ (s * a) w = δ s (δ a w) from
      congrArg (fun f : Module.End (ZMod 2) D => f w) ((δ).map_mul s a)]
    have hsa : s * a = g.val.val * s := by simp [a, mul_assoc]
    rw [hsa]
    have hm := congrArg (fun f : Module.End (ZMod 2) D => f w) ((δ).map_mul g.val.val s)
    rw [hm]
    change δ s w = v.val at he
    change δ g.val.val (δ s w) = δ g.val.val v.val
    rw [he]
  have hdim : Module.finrank (ZMod 2) R = Module.finrank (ZMod 2) P :=
    (Submodule.comapSubtypeEquivOfLe hQ).finrank_eq.trans (e.finrank_map_eq P)
  exact hdim ▸ BinaryPermutation.AlternatingFiveBorel.no_invariant_plane R hR

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
local notation "B" => (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)

/-- Under every star marking, the original point parabolic is a literal
point stabilizer in S₅. -/
theorem point_image_stabilizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
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
    exact point_index_five h structural e
  have hc := I.card_mul_index
  have hs : Nat.card S5 = 120 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  rw [hi, hs] at hc
  have hc' : Nat.card I * 5 = 120 := hc
  have hcard : Nat.card I = 24 := by omega
  exact Theory.SpecificGroups.Alternating.FivePointTwentyFour.exists_eq_stabilizer I hcard

/-- The original seed plane excludes every surjective deleted-permutation
quotient of the literal U/V₁ action. -/
theorem no_deleted_quotient
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
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
  obtain ⟨i,hi⟩ := point_image_stabilizer h structural e
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
