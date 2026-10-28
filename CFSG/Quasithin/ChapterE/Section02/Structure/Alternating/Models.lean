module
public import Theory.SpecificGroups.Alternating.SevenNormalSupplement
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import CFSG.Quasithin.ChapterE.Section02.Structure.BinaryExclusions.Models
public import CFSG.Quasithin.ChapterB.Section06To07.Structure
public import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# The normal alternating source rows of E.2.2

The normal A₇ supplement has two constructed proper overgroups of the
prescribed Sylow that generate H, contradicting minimal parabolicity.
The actual A₈≃PSL₄(2) equivalence invokes the already proved binary exclusion.
Smaller nonabelian simple alternating models have degree at least five;
the surviving A₅ and A₆ cases are carried by genuine equivalences to SL₂(4)
and the commutator of the actual projective symplectic group PSp₄(2).

Source: Aschbacher–Smith E.2.2, printed pp.215–216. The constructions use
the original normal K, original Sylow T and H=KT, with no extra overgroup
or model-recognition premise.
-/

public section
noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure.Alternating
variable {H : Type*} [Group H] [Finite H]

/-- The A₇ model contradicts the original unique maximal Sylow overgroup. -/
theorem not_seven (T : Sylow 2 H) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) :
    ¬ Nonempty (K ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  obtain ⟨P,Q,hTP,hTQ,hPQ,hPproper,hQproper⟩ :=
    alternatingGroup.SevenSolvableGeneration.exists_proper_overgroups_of_normal_supplement K T hgen e
  let M := ChapterB.minimalParabolicMax T hP
  have hM : (T : Subgroup H) ≤ M ∧ M ⋖ ⊤ :=
    ⟨(ChapterB.minimalParabolicMax_spec T hP).2,(ChapterB.minimalParabolicMax_spec T hP).1.covBy_top⟩
  have hPM : P ≤ M := hP.1.le_maximal hM hTP hPproper
  have hQM : Q ≤ M := hP.1.le_maximal hM hTQ hQproper
  have ht : ⊤ ≤ M := hPQ ▸ sup_le hPM hQM
  exact hM.2.ne (top_unique ht)

/-- The concrete exceptional A₈ equivalence feeds the binary rank-four exclusion. -/
theorem not_eight (T : Sylow 2 H) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) :
    ¬ Nonempty (K ≃* alternatingGroup (Fin 8)) := by
  rintro ⟨e⟩
  apply BinaryExclusions.not_linear_binary T K hgen hP (Or.inl rfl)
  exact ⟨ZMod 2,inferInstance,inferInstance,by simp,
    ⟨e.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two⟩⟩

private theorem degree_ge_five {G : Type*} [Group G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) {n : ℕ} (e : G ≃* alternatingGroup (Fin n)) : 5 ≤ n := by
  by_contra hh
  have hn : n ≤ 4 := by omega
  let : Group.IsPerfect G := ⟨
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) inferInstance).resolve_left
      (fun h => hna ((commutator_eq_bot_iff G).mp h))⟩
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let f : G →* Equiv.Perm (Fin 4) := (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb hn)).comp
    ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom)
  have hf : Function.Injective f := (Equiv.Perm.viaEmbeddingHom_injective _).comp
    ((alternatingGroup (Fin n)).subtype_injective.comp e.injective)
  let : Group.IsSolvable G := Group.isSolvable_of_isSolvable_injective (f := f) hf
  exact Group.IsPerfect.not_isSolvable G inferInstance

/-- The only normal alternating source models are the two surviving concrete rows. -/
theorem survivors (T : Sylow 2 H) (K : Subgroup H) [K.Normal] [IsSimpleGroup K]
    (hna : ¬ IsMulCommutative K) (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hm : ∃ n : ℕ, n ≤ 8 ∧ Nonempty (K ≃* alternatingGroup (Fin n))) :
    Nonempty (K ≃* SL(2,GaloisField 2 2)) ∨
      Nonempty (K ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  obtain ⟨n,hn,⟨e⟩⟩ := hm
  have hn5 := degree_ge_five hna e
  have hn7 : n ≠ 7 := by intro he; subst n; exact not_seven T K hgen hP ⟨e⟩
  have hn8 : n ≠ 8 := by intro he; subst n; exact not_eight T K hgen hP ⟨e⟩
  have hn56 : n = 5 ∨ n = 6 := by omega
  rcases hn56 with rfl | rfl
  · exact Or.inl ⟨(e.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm).trans
      (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := GaloisField 2 2)).symm⟩
  · exact Or.inr ⟨e.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix.symm⟩

/-- The same surviving rows in the exact E.2.2 model predicates. -/
theorem source_rows (T : Sylow 2 H) (K : Subgroup H) [K.Normal] [IsSimpleGroup K]
    (hna : ¬ IsMulCommutative K) (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hm : ∃ n : ℕ, n ≤ 8 ∧ Nonempty (K ≃* alternatingGroup (Fin n))) :
    ClassificationModels.IsBenderModel K ∨
      Nonempty (K ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  rcases survivors T K hna hgen hP hm with hleft | h
  · obtain ⟨e⟩ := hleft
    refine Or.inl (.linear 2 (by decide) ?_)
    exact ⟨GaloisField 2 2,inferInstance,inferInstance,GaloisField.card 2 2 (by decide),
      ⟨e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := GaloisField 2 2))⟩⟩
  · exact Or.inr h
end CFSG.Quasithin.ChapterE.Structure.Alternating
