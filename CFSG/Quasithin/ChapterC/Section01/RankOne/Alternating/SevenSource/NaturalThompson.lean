module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.NaturalThompsonStable
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Source

/-!
# The source Thompson image in the natural seven-letter Sylow branch

For the original Sylow subgroup T, B.2.10 gives the stable family of images
of maximum elementary subgroups. Its local generators are exactly the image
of J(T), by Sylow localization. The seven-letter stable-family calculation
therefore identifies this image with a conjugate of the three disjoint swaps.
The fixed-codimension comparison is explicit so that the original module V,
including its fixed summand, remains the module in the source family.

This is the R = T specialization of Aschbacher–Smith C.1.24, printed p.131.
The general R ≤ T statement permits one or two disjoint swaps as well.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
open ChapterB BinaryPermutation

variable {G : Type*} [Group G] [Finite G]

/-- The original Sylow hypothesis saturates the stable family: all three
canonical disjoint transpositions occur after one simultaneous marking. -/
theorem natural_source_thompson_conjugate
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (T : Sylow 2 G) (hVT : V ≤ T)
    (q : G →* Equiv.Perm (Fin 7)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (V : Set G))
    (hc : ∀ A, fixedCodim (NormalElementaryQuotient.representation V q hq hk) A =
      fixedCodim (coreRepresentation (Fin 7)) A)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ q.ker) :
    ∃ a : Equiv.Perm (Fin 7), (elementaryAbelianMaxJ (T : Subgroup G)).map q =
      (ChapterB.Offenders.D 7).map (MulAut.conj a).toMonoidHom := by
  let ρ := NormalElementaryQuotient.representation V q hq hk
  have hs := (ChapterB.lemma_B_2_10_relative V T hVT q hq hk hJ).2.1
  have hstable : IsStable (coreRepresentation (Fin 7))
      (relativeMaxOffenderImages T V q) := by
    have hh := hs.map_of_fixedCodim ρ (coreRepresentation (Fin 7))
      (MulEquiv.refl (Equiv.Perm (Fin 7))) (by intro A; simpa using hc A)
    simpa using hh
  obtain ⟨g, hg⟩ := exists_generatedBy_marking hstable (T.mapSurjective hq)
  have hgen := SymmetricFive.source_family_generated T V q hq
  rw [Sylow.coe_mapSurjective, ← hgen] at hg
  refine ⟨g⁻¹, ?_⟩
  have hh := congrArg (fun A : Subgroup (Equiv.Perm (Fin 7)) =>
    A.map (MulAut.conj g⁻¹).toMonoidHom) hg
  have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id (Equiv.Perm (Fin 7)) := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hcancel (A : Subgroup (Equiv.Perm (Fin 7))) :
      (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
    rw [Subgroup.map_map, hid, Subgroup.map_id]
  simpa only [hcancel] using hh

/-- In literal coordinates containing D, no conjugation is needed. -/
theorem natural_source_thompson_image
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (T : Sylow 2 G) (hVT : V ≤ T)
    (q : G →* Equiv.Perm (Fin 7)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (V : Set G))
    (hc : ∀ A, fixedCodim (NormalElementaryQuotient.representation V q hq hk) A =
      fixedCodim (coreRepresentation (Fin 7)) A)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ q.ker)
    (hD : ChapterB.Offenders.D 7 ≤ (T : Subgroup G).map q) :
    (elementaryAbelianMaxJ (T : Subgroup G)).map q = ChapterB.Offenders.D 7 := by
  let ρ := NormalElementaryQuotient.representation V q hq hk
  have hs := (ChapterB.lemma_B_2_10_relative V T hVT q hq hk hJ).2.1
  have hstable : IsStable (coreRepresentation (Fin 7))
      (relativeMaxOffenderImages T V q) := by
    have hh := hs.map_of_fixedCodim ρ (coreRepresentation (Fin 7))
      (MulEquiv.refl (Equiv.Perm (Fin 7))) (by intro A; simpa using hc A)
    simpa using hh
  rw [SymmetricFive.source_family_generated T V q hq]
  exact stable_generatedBy_eq_D hstable _ (T.isPGroup'.map q) hD

end CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
