module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.Algebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.Pencils

/-!
# Relative normal closure of the local commutator values

The value bound extends from a seed to its parabolic normal closure when the
bounding value space is normalized by that parabolic. Ambient normality of
the value space is unnecessary: express the local closure through its actual
conjugates, then use the central-valued commutator homomorphisms.

Source: Meierfrankenfeld--Stellmacher (1993), proof of (1.7)(i), p.847.
-/

public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction
open Subgroup
universe u
variable {M : Type u} [Group M]

/-- The local normal closure is bounded by the join of the ambient conjugates
whose actors lie in the specified local group. -/
theorem localGenerated_le_conjugates (P X : Subgroup M) :
    localGenerated P X ≤ ⨆ p : P, conjugate (p : M) X := by
  apply map_le_iff_le_comap.mpr
  change closure (Group.conjugatesOfSet (X.subgroupOf P : Set P)) ≤ _
  apply (closure_le _).mpr
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨a, rfl⟩ := isConj_iff.mp hxy
  exact (le_iSup (fun p : P => conjugate (p : M) X) a)
    (mem_map_of_mem (MulAut.conj (a : M)).toMonoidHom hy)

/-- Extension of a central-valued pairing bound using only relative
normalization of its target. -/
theorem localGenerated_commutator_bound_of_normalizes
    (U W Z P X D : Subgroup M) [U.Normal] [W.Normal]
    (hUW : ⁅U, W⁆ ≤ Z) (hZU : Z ≤ centralizer (U : Set M))
    (hXU : X ≤ U) (hXW : ⁅X, W⁆ ≤ D) (hPD : P ≤ normalizer (D : Set M)) :
    ⁅localGenerated P X, W⁆ ≤ D := by
  apply (commutator_mono (localGenerated_le_conjugates P X) le_rfl).trans
  apply pairing_iSup_bound U W Z D (fun p : P => conjugate (p : M) X) hUW hZU
  · intro p
    exact conjugate_le_normal X U hXU p
  · intro p
    have h := commutator_conjugate_left X W D hXW (p : M)
    have he : D.map (MulAut.conj (p : M)).toMonoidHom = D :=
      mem_normalizer_iff_map_conj_eq.mp (hPD p.property)
    exact h.trans he.le

/-- The value space is normalized by its actual local parabolic. -/
theorem localFixed_normalized (e : Extension (M := M)) (Z : Subgroup M)
    [Z.Normal] (j : Bool) :
    localParabolic e j ≤ normalizer (localFixed e Z j : Set M) := by
  have hcore : localParabolic e j ≤
      normalizer (localCore (localParabolic e j) : Set M) := by
    intro p hp
    apply (pCore 2 (localParabolic e j)).le_normalizer_map (localParabolic e j).subtype
    exact ⟨⟨p, hp⟩, by rw [normalizer_eq_top]; trivial, rfl⟩
  exact (le_inf le_normalizer_of_normal
    (normalizes_centralizer _ _ hcore)).trans inf_normalizer_le_normalizer_inf

/-- The seed commutator is invariant under its actual local normalizer. -/
theorem seed_commutator_normalized [Finite M]
    {e : Extension (M := M)} {i : Bool} {Z W X : Subgroup M}
    [Z.Normal] [W.Normal] (d : SourceData e i Z W X) (f : LocalFacts e Z) :
    localParabolic e i ≤ normalizer (↑(⁅X, W⁆ : Subgroup M) : Set M) := by
  intro p hp
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (f.seed_normalized d hp),
    mem_normalizer_iff_map_conj_eq.mp
      (show p ∈ normalizer (W : Set M) from le_normalizer_of_normal (mem_top p))]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction
