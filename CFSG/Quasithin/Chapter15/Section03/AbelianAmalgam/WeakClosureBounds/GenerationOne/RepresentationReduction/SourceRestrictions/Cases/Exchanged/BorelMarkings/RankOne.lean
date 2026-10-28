module

public import Theory.Representation.SylowNormalizerIntertwiner
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.LinearModels
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SLTwo
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.RemainingModels.Suzuki
public import Theory.SpecificGroups.Suzuki.RootOvoidGeometry

/-!
# Borel markings for the exchanged rank-one natural modules

The named SL₂ and Suzuki Borels are actual Sylow-two normalizers. The E.2.2
recognition of the group and its overlap therefore makes that literal overlap
a Sylow normalizer. Given an independently established natural-module
identification, conjugate its group map and act on its module coordinates by
the same element to align the overlap. No automorphism classification or
identification of concrete field carriers is needed.

Source: Aschbacher–Smith, E.2.2, printed pp.215–216; F.9.18(5), pp.325–326;
and 15.3.65(i), printed p.1152. These are marking lemmas, not module recognition.
-/

@[expose] public noncomputable section
open Matrix Matrix.SpecialLinearGroup Representation
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.BorelMarkings
open RemainingModels BorelReduction BorelReduction.SourceCases BenderSuzuki.MatrixGroups

/-- The named upper-triangular Borel is the normalizer of the actual upper-root Sylow. -/
theorem slTwo_borel_normalizer {F : Type*} [Field F] [Finite F] [CharP F 2] :
    ∃ P : Sylow 2 SL(2,F), Subgroup.normalizer (P : Set SL(2,F)) = rankOneBorel F := by
  exact ⟨upperUnipotentSylow F 2, rfl⟩

/-- The E.2.2 matrix Borel is the same subgroup as the natural-module Borel. -/
theorem slTwo_source_borel_eq {F : Type*} [Field F] :
    BenderSuzuki.Converse.Borel F = rankOneBorel F := by
  ext g
  exact (BenderSuzuki.Converse.mem_Borel_iff g).trans (mem_rankOneBorel_iff g).symm

/-- The actual Suzuki root Sylow has the named Suzuki Borel as its normalizer. -/
theorem suzuki_borel_normalizer (m : ℕ) (hm : 0 < m) :
    ∃ P : Sylow 2 (SuzukiMatrixGroup m),
      Subgroup.normalizer (P : Set (SuzukiMatrixGroup m)) = SuzukiBorelSubgroup m := by
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
  refine ⟨P, ?_⟩
  change Subgroup.normalizer ((P : Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m)) = _
  rw [hP]
  exact suzukiRootSubgroup_normalizer m hm

/-- E.2.2's actual overlap, in its literal source quotient, is a Sylow normalizer. -/
theorem source_overlap_normalizer {G : Type*} [Group G]
    {H M K : Subgroup G} {f : ℕ} (h : ExchangedModel H M K f) :
    ∃ P : Sylow 2 (sourceImage H M K),
      Subgroup.normalizer (P : Set (sourceImage H M K)) = componentOverlap H M K := by
  rcases h with ⟨F, hfield, hfinite, hchar, hf, hF, hB⟩ | ⟨m, hm, hf, a, ha⟩
  · obtain ⟨a, ha⟩ := hB.sl2
    rw [slTwo_source_borel_eq] at ha
    exact Subgroup.exists_sylow_normalizer_of_equiv a _ _ ha (slTwo_borel_normalizer (F := F))
  · exact Subgroup.exists_sylow_normalizer_of_equiv a _ _ ha (suzuki_borel_normalizer m hm)

/-- Align any established natural SL₂ module with the actual E.2.2 Borel pair.
The natural module's field need not be the source pair's concrete field carrier. -/
theorem source_slTwo_alignment {G V F : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [Field F] [Finite F]
    [CharP F 2] [Algebra (ZMod 2) F]
    {H M K : Subgroup G} {f : ℕ} (h : ExchangedModel H M K f)
    (ρ : Representation (ZMod 2) (sourceImage H M K) V)
    (φ : sourceImage H M K ≃* SL(2,F)) (e : V ≃ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ a v, e (ρ a v) = specialLinearNatural 2 (φ a) (e v)) :
    ∃ g : SL(2,F),
      (componentOverlap H M K).map (φ.trans (MulAut.conj g)).toMonoidHom = rankOneBorel F ∧
      ∀ a v,
        (e.trans (innerIntertwiner (restrictScalars (specialLinearNatural 2)) g)) (ρ a v) =
          specialLinearNatural 2 ((φ.trans (MulAut.conj g)) a)
            ((e.trans (innerIntertwiner (restrictScalars (specialLinearNatural 2)) g)) v) := by
  let : Finite (sourceImage H M K) := Finite.of_equiv (SL(2,F)) φ.symm.toEquiv
  exact exists_innerIntertwiner_sylowNormalizer _ _ (source_overlap_normalizer h)
    (slTwo_borel_normalizer (F := F)) ρ (restrictScalars (specialLinearNatural 2)) φ e he

/-- The same simultaneous alignment for the literal Suzuki natural module. -/
theorem source_suzuki_alignment {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    {H M K : Subgroup G} {f m : ℕ} (hm : 0 < m) (h : ExchangedModel H M K f)
    (ρ : Representation (ZMod 2) (sourceImage H M K) V)
    (φ : sourceImage H M K ≃* SuzukiMatrixGroup m)
    (e : V ≃ₗ[ZMod 2] (Fin 4 → BenderSuzuki.PFAppendixIII.BinaryGaloisField (2 * m + 1)))
    (he : ∀ a v, e (ρ a v) = suzukiNatural m (φ a) (e v)) :
    ∃ g : SuzukiMatrixGroup m,
      (componentOverlap H M K).map (φ.trans (MulAut.conj g)).toMonoidHom = SuzukiBorelSubgroup m ∧
      ∀ a v, (e.trans (innerIntertwiner (suzukiNatural m) g)) (ρ a v) =
        suzukiNatural m ((φ.trans (MulAut.conj g)) a)
          ((e.trans (innerIntertwiner (suzukiNatural m) g)) v) := by
  let : Finite (sourceImage H M K) := Finite.of_equiv (SuzukiMatrixGroup m) φ.symm.toEquiv
  exact exists_innerIntertwiner_sylowNormalizer _ _ (source_overlap_normalizer h)
    (suzuki_borel_normalizer m hm) ρ (suzukiNatural m) φ e he

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.BorelMarkings
