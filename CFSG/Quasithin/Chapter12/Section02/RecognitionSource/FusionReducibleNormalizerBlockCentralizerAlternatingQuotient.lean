module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.AlternatingSixQuotient
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerLocalAlternating
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerAlternatingCubic

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry

/-!
# Original alternating-six quotient setup and terminal applications

The intrinsic block action supplies the six-letter map with kernel O₂(LT).
A simultaneous conjugate marking places the actual Sylow image in the
prescribed pair stabilizer. The ambient residual comparison constructs
local invariance directly from the original nonzero fixed subgroup.

The terminal applications below therefore need only the displayed remaining
subgroup-image geometry. They construct the invariant cubic and all later
invariant-core facts through the checked Cubic argument. The normalizer
application retains the original Hypothesis1223, ChosenModule, Structural1222
and NoEscape, and no longer asks for an independent A₆ invariance producer.
The local residual image and moved omega-module image still belong to the
final assembly in `qt-d-12216-normalizer-block-centralizer`; neither these
conditional applications nor the quotient setup asserts their construction.

Source: Aschbacher–Smith 3.3.25(2), 3.3.26 and 3.3.31, printed pp.599–602.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- A simultaneous relabelling puts the actual Sylow image in the prescribed pair stabilizer. -/
theorem exists_six_letter_sylow_marking
    (hb : ChapterC.IsAlternatingBlock L 6) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ q : ↥(L ⊔ (T : Subgroup G)) →* Equiv.Perm (Fin 6),
      q.ker = ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (L ⊔ (T : Subgroup G)) ∧
      (L.subgroupOf (L ⊔ (T : Subgroup G))).map q = alternatingGroup (Fin 6) ∧
      ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map q ≤
        Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1 := by
  obtain ⟨q, hk, hL⟩ := hb.exists_six_letter_quotient hTL
  let P := ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map q
  obtain ⟨S, hPS⟩ := (T.isPGroup'.comap_subtype.map q).exists_le_sylow
  obtain ⟨g, hg, _⟩ := Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.sylow_flag S
  let c := (MulAut.conj g⁻¹).toMonoidHom
  have hback : (S : Subgroup (Equiv.Perm (Fin 6))).map c =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1 ⊓
        Theory.SpecificGroups.SymmetricSix.BinaryFlags.H2 := by
    rw [← hg, map_map]
    have he : c.comp (MulAut.conj g).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x
      group
    rw [he, map_id]
  refine ⟨c.comp q, (MonoidHom.ker_comp_of_injective q c (MulAut.conj g⁻¹).injective).trans hk,
    ?_, ?_⟩
  · rw [← map_map, hL]
    exact mem_normalizer_iff_map_conj_eq.mp
      (show g⁻¹ ∈ normalizer (alternatingGroup (Fin 6) : Set (Equiv.Perm (Fin 6))) by
        rw [normalizer_eq_top]; trivial)
  · rw [← map_map]
    exact (map_mono (f := c) hPS).trans (hback.le.trans inf_le_left)


/-- The original A₆ row supplies both the literal quotient and local invariance. -/
theorem alternating_six_quotient_setup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) (hb : ChapterC.IsAlternatingBlock L 6) :
    BlockLocalInvariance T L ∧
    ∃ q : ↥(L ⊔ (T : Subgroup G)) →* Equiv.Perm (Fin 6),
      q.ker = ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (L ⊔ (T : Subgroup G)) ∧
      (L.subgroupOf (L ⊔ (T : Subgroup G))).map q = alternatingGroup (Fin 6) ∧
      ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map q ≤
        Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1 :=
  ⟨blockLocalInvariance_of_alternating h D hfixed hb,
    exists_six_letter_sylow_marking hb D.sylow_normalizes_component⟩

/-- Original source hypotheses discharge the local-invariance input to the marked terminal argument. -/
theorem false_of_alternating_six_marking_original
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) (hb : ChapterC.IsAlternatingBlock L 6)
    {d : G} (ho : Odd (orderOf d)) (hd : d ∈ normalizer (T : Set G))
    (hout : d ∉ normalizer (L : Set G)) (m : AlternatingSixLocalMarking T L d) : False :=
  false_of_alternating_six_marking h D hb ho hd hout m
    (((blockLocalInvariance_of_alternating h D hfixed hb).1 (Or.inl hb)).1 hd)

/-- The marking consumer now requires only the three specified subgroup images.
The permutation action and its exact core kernel are constructed internally;
local invariance and the invariant cubic are discharged from original inputs. -/
theorem false_of_alternating_six_quotient_images
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) (hb : ChapterC.IsAlternatingBlock L 6)
    {d : G} (ho : Odd (orderOf d)) (hd : d ∈ normalizer (T : Set G))
    (hout : d ∉ normalizer (L : Set G))
    {ρ : ChapterC.AlternatingSixBlockAction.Actor →*
      MulAut (Multiplicative ChapterC.AlternatingSixBlockAction.Vector)}
    (m : ChapterC.BlockModuleModel L ρ)
    (hρ : ∀ g v, (ρ g v).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) g v.toAdd)
    (hX : ((blockLocalResidual T L).subgroupOf (L ⊔ (T : Subgroup G))).map
      (ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ) =
        Theory.SpecificGroups.SymmetricSix.BinaryFlags.K)
    (hT : ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map
      (ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ) ≤
        Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1)
    (hW : (((blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom).subgroupOf
      (L ⊔ (T : Subgroup G))).map
      (ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ) =
        zpowers Theory.SpecificGroups.SymmetricSix.BinaryFlags.swap45) : False := by
  apply false_of_alternating_six_marking_original h D hfixed hb ho hd hout
  exact {
    quotient := ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ
    kernel := ChapterC.AlternatingSixBlockAction.joinPermutation_kernel
      D.sylow_normalizes_component m hρ hb.2.1
    local_image := hX
    sylow_image := hT
    moved_image := hW }

/-- The source normalizer application uses no independent local-invariance producer in the A₆ branch.
Construction of the remaining three marked images stays with this task's final assembly. -/
theorem sylow_normalizer_le_of_alternating_six_original_markings
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) (hb : ChapterC.IsAlternatingBlock L 6)
    (markings : AlternatingSixLocalMarkingSource T L V) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  have hi := blockLocalInvariance_of_alternating h D hfixed hb
  obtain ⟨d, ho, hd, hout, hmove, hnormal, _⟩ :=
    exists_odd_alternating_omega_movement h D hescape hi hb
  obtain ⟨m⟩ := markings h D structural hnone hfixed hescape hi hb d ho hd hout hmove hnormal
  exact false_of_alternating_six_marking_original h D hfixed hb ho hd hout m

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
