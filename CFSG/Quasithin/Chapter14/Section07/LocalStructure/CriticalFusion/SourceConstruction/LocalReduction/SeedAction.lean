module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SeedSeparation
public import Theory.Representation.NormalPSubgroupKernel

/-!
# The original point core before natural recognition

The natural seed quotient is irreducible under L₁, hence under L₁T.
Its normal two-core acts trivially in characteristic two. Transport
through the actual quotient action gives [R₁,V] ≤ V₁ and fixedness of
the seed in every literal U/V₁ conjugation section. The core of H lies
in R₁. Its invariant space is H-stable and contains the seed, so seed
separation forces it to be the whole section. This descends the original
action through H/O₂(H), keeping the same coordinates.

This extracts the argument of Source/Rechoice/SourceCompletion/SeedAction
before the source datum is constructed. It supplies the fixed-seed input
for the local natural-module reduction without recognition assumptions.

Source: Aschbacher–Smith, Notation 12.8.2 and 14.7.1–2,
printed pp.849 and 1043.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Representation Chapter12.Section08 CriticalFusion.Source
open scoped IsMulCommutative MonoidAlgebra
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

omit [Finite G] in
private theorem group_le_H : (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) ≤ F.H :=
  sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)

/-- The natural point quotient kills the intrinsic core of L₁T. -/
theorem point_core_commutator_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) : ⁅F.Ri L 1, V⁆ ≤ F.Vi 1 := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  have hBV : (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) ≤ normalizer (V : Set G) :=
    sup_le ((F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes))
      (by simpa only [F.last] using F.invariant 3)
  let f := F.tildeAction ((F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)) V group_le_H hBV
  let ρ := Representation.elementaryRepresentation (p := 2) f
  let τ := F.localSeedRepresentation L h.chosen.normalizes
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient (by decide : 3 ≤ 3)
    L h.chosen.normalizes h.naturalMarking
  let : τ.IsIrreducible := (irreducible_iff_isSimpleModule_asModule τ).mpr (D.seed_simple (by decide))
  let : Nontrivial (Additive (F.tilde V)) := Subrepresentation.irreducible_module_nontrivial τ
  let : ρ.IsIrreducible := by
    rw [Representation.IsIrreducible, isSimpleOrder_iff]
    refine ⟨inferInstance, fun S => ?_⟩
    let S₀ : Subrepresentation τ := {
      toSubmodule := S.toSubmodule
      apply_mem_toSubmodule l v hv := by
        exact S.apply_mem_toSubmodule
          (⟨l, (show F.Li L 1 ≤ (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) from le_sup_left) l.property⟩ : (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)) hv }
    rcases eq_bot_or_eq_top S₀ with he | he
    · left
      apply le_antisymm _ bot_le
      intro v hv
      exact (show v ∈ (⊥ : Subrepresentation τ) from he ▸ hv)
    · right
      apply top_unique
      intro v _
      exact (show v ∈ S₀ from he ▸ (show v ∈ (⊤ : Subrepresentation τ) from trivial))
  have hk : pCore 2 ((F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)) ≤ ρ.ker :=
    normal_p_subgroup_le_ker ρ (pCore 2 ((F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G))) pCore_isPGroup
  apply commutator_le.mpr
  intro r hr v hv
  obtain ⟨r, hr, rfl⟩ := hr
  have hrf : r ∈ f.ker := by
    apply MulEquiv.ext
    intro w
    have he := LinearMap.congr_fun (hk hr) (Additive.ofMul w)
    exact Additive.ofMul.injective he
  exact (F.mem_tildeAction_ker_iff ((F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)) V group_le_H
    ((le_conjugateSpanBy V F.H).trans F.U_le_H)
    hBV r).mp hrf v hv

/-- The actual R₁ action fixes the original seed image inside U/V₁. -/
theorem seed_fixed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    {ρ : Representation (ZMod 2) F.H W}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) : ∀ r : F.H, (r : G) ∈ F.Ri L 1 → ∀ v : F.U, (v : G) ∈ V →
    ρ r (c.coordinates v).toAdd =
      (c.coordinates v).toAdd := by
  intro r hr v hv
  apply c.fixed_on_imageSpace_of_commutator_le
    (F.Ri L 1) V (point_core_commutator_seed h) r hr
  exact (c.mem_imageSpace_iff _ _).mpr ⟨v, hv, rfl⟩


omit [Finite G] in
/-- The core of H lies in the core of the original point parabolic. -/
theorem core_le_point_core : F.H.pCoreIn 2 ≤ F.Ri L 1 := by
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have h := pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))
    change F.H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf F.H).map F.H.subtype at h
    intro x hx
    obtain ⟨y, hy, rfl⟩ := h hx
    exact hy
  apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 F.H)
    (hQT.trans (show (T : Subgroup G) ≤ (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)
      from le_sup_right))
  exact group_le_H.trans (F.H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H)))

/-- The actual two-core of H acts trivially on every literal U/V₁ section. -/
theorem core_le_action_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    {ρ : Representation (ZMod 2) F.H W}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) : pCore 2 F.H ≤ ρ.ker := by
  let A := Representation.invariants (ρ.comp (pCore 2 F.H).subtype)
  have hAtop : A = ⊤ := by
    by_contra hp
    have hAV : ∀ v : F.U, (v : G) ∈ V → (c.coordinates v).toAdd ∈ A := by
      intro v hv q
      exact seed_fixed h c q.val (core_le_point_core (mem_map_of_mem _ q.property)) v hv
    have hVP : V ≤ F.Vi 1 := by
      intro v hv
      let vU : F.U := ⟨v, le_conjugateSpanBy V F.H hv⟩
      exact (seed_intersection h c A (fun g w hw =>
        Representation.le_comap_invariants ρ (pCore 2 F.H) g hw) hp vU hv).mp (hAV vU hv)
    have hc := card_le_of_le hVP
    have hV : Nat.card V = 8 := by simpa only [F.last, Nat.reducePow] using F.card 3 (by decide)
    have hP : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    omega
  intro q hq
  apply LinearMap.ext
  intro w
  exact (show w ∈ A from hAtop ▸ Submodule.mem_top) ⟨q, hq⟩

/-- Descend the original action through the literal star map, retaining the
same vector space and the same coordinate homomorphism. -/
theorem exists_star_representation
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    {ρ : Representation (ZMod 2) F.H W}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ∃ σ : Representation (ZMod 2) (HStar F.H) W, σ.comp (starMap F) = ρ := by
  let : Representation.IsTrivial (ρ.comp (pCore 2 F.H).subtype) :=
    ⟨fun q => core_le_action_kernel h c q.property⟩
  exact ⟨ρ.ofQuotient (pCore 2 F.H), rfl⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
