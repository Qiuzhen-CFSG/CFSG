module
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.SevenFourOffenders.Geometry
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.ActionTransport

/-!
# K.1.2: the four-dimensional A₇ branch

Recognition supplies G = L and an actual action equivalence with the
restriction A₇ ↪ A₈ ≃ SL₄(2) on the binary four-space. The fixed-space
and Sylow calculations in the descendants prove the full offender family
and q = 1. Equivariant transport gives these conclusions on the original
module and identifies its offender subgroup with L.

`sevenFour_source` constructs the corrected B.4.2(7) alternative using
exactly the supplied group equivalence. `sevenFour_conclusion` retains the
original action equivalence in `Conclusion.ff`. No module-recognition or
offender assertion is assumed beyond the task's actual model identification.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
K.1.2, printed p.452/PDF p.463. The separate alternating-module owner
supplies recognition and assembles the remaining K.1 branches.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.Alternating
open ChapterB.QuasisimpleSource
open Representation.AlternatingSevenConjugatePair

universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {L : Subgroup G}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- K.1.2's model recognition gives the literal binary dimension. -/
theorem sevenFour_dimension
    (e : ActionEquiv (ρ.comp L.subtype) Model.natural) :
    Module.finrank (ZMod 2) V = 4 :=
  e.linearEquiv.finrank_eq.trans Model.four_dimension

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- The full quadratic infimum for the source action. -/
theorem sevenFour_quadraticRatio (hL : L = ⊤)
    (e : ActionEquiv (ρ.comp L.subtype) Model.natural) : quadraticRatio ρ = 1 :=
  (quadraticRatio_eq (wholeAction hL e)).trans
    (SevenFourOffenders.quadraticRatio_eq_one Model.natural Model.natural_faithful Model.four_dimension)

omit [Finite G] in
/-- Every best offender is the required Klein-four conjugate through this same `e`. -/
theorem sevenFour_offenders (hL : L = ⊤)
    (e : ActionEquiv (ρ.comp L.subtype) Model.natural)
    (A : Subgroup G) (hA : IsBestOffender ρ A) :
    ∃ g : alternatingGroup (Fin 7),
      ((A.subgroupOf L).map ((alternatingGroup (Fin 7)).subtype.comp e.groupEquiv.toMonoidHom)) =
      (Subgroup.closure {ChapterB.Offenders.kleinFirst 7 (by decide),
        ChapterB.Offenders.kleinSecond 7 (by decide)}).map
          (MulAut.conj (g : Equiv.Perm (Fin 7))).toMonoidHom := by
  have hAL : A ≤ L := by rw [hL]; exact le_top
  have hb := ((hA.subgroupOf ρ hAL).isOffender (ρ.comp L.subtype)).map_equivariant
    (ρ.comp L.subtype) Model.natural e.groupEquiv.toMonoidHom e.groupEquiv.injective
    e.linearEquiv e.intertwines
  obtain ⟨g, hg⟩ := SevenFourOffenders.offender_conjugate
    Model.natural Model.natural_faithful Model.four_dimension hb
  refine ⟨g, ?_⟩
  rw [← Subgroup.map_map, hg, ← SevenFourOffenders.R1_map_eq_source,
    Subgroup.map_map, Subgroup.map_map]
  congr 1

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- An actual offender on the four-space transports back to the source actor. -/
theorem sevenFour_isFF (hL : L = ⊤)
    (e : ActionEquiv (ρ.comp L.subtype) Model.natural) : IsFFModule ρ := by
  let f := wholeAction hL e
  have hi : ∀ g v, f.linearEquiv.symm (Model.natural g v) =
      ρ (f.groupEquiv.symm g) (f.linearEquiv.symm v) := by
    intro g v
    apply f.linearEquiv.injective
    rw [f.linearEquiv.apply_symm_apply, f.intertwines,
      f.groupEquiv.apply_symm_apply, f.linearEquiv.apply_symm_apply]
  have hff : IsFFModule Model.natural := ⟨SevenFourOffenders.R1,
    (SevenFourOffenders.R1_best Model.natural Model.natural_faithful Model.four_dimension).isOffender _⟩
  exact hff.map_equivariant Model.natural ρ f.groupEquiv.symm.toMonoidHom f.groupEquiv.symm.injective
      f.linearEquiv.symm hi

omit [FiniteDimensional (ZMod 2) V] in
/-- The source's uniqueness assertion in each actual Sylow subgroup of G. -/
theorem sevenFour_exists_unique_offender (hL : L = ⊤)
    (e : ActionEquiv (ρ.comp L.subtype) Model.natural) (T : Sylow 2 G) :
    ∃! A : Subgroup G, A ≤ (T : Subgroup G) ∧ IsOffender ρ A := by
  let f := wholeAction hL e
  let F := f.groupEquiv.mapSubgroup
  let Q : Sylow 2 (alternatingGroup (Fin 7)) :=
    T.mapSurjective (f := f.groupEquiv.toMonoidHom) f.groupEquiv.surjective
  obtain ⟨B, ⟨hBQ, hB⟩, huniq⟩ := SevenFourOffenders.exists_unique_offender
    Model.natural Model.natural_faithful Model.four_dimension Q
  have hBT : F.symm B ≤ (T : Subgroup G) := F.symm_apply_le.mpr hBQ
  have hi : ∀ g v, f.linearEquiv.symm (Model.natural g v) =
      ρ (f.groupEquiv.symm g) (f.linearEquiv.symm v) := by
    intro g v
    apply f.linearEquiv.injective
    rw [f.linearEquiv.apply_symm_apply, f.intertwines,
      f.groupEquiv.apply_symm_apply, f.linearEquiv.apply_symm_apply]
  have hback : IsOffender ρ (F.symm B) := hB.map_equivariant Model.natural ρ
    f.groupEquiv.symm.toMonoidHom f.groupEquiv.symm.injective f.linearEquiv.symm hi
  refine ⟨F.symm B, ⟨hBT, hback⟩, ?_⟩
  rintro A ⟨hAT, hA⟩
  apply F.injective
  rw [F.apply_symm_apply]
  apply huniq
  exact ⟨F.monotone hAT, hA.map_equivariant ρ Model.natural
    f.groupEquiv.toMonoidHom f.groupEquiv.injective f.linearEquiv f.intertwines⟩

/-- The source offender subgroup is the entire component, with no generation premise. -/
theorem sevenFour_offenderSubgroup (hL : L = ⊤)
    (e : ActionEquiv (ρ.comp L.subtype) Model.natural) : offenderSubgroup ρ = L := by
  let _ : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 7))
  let _ : IsSimpleGroup G := (wholeAction hL e).groupEquiv.isSimpleGroup
  rw [hL]
  exact (offenderSubgroup_normal ρ).eq_bot_or_eq_top.resolve_left
    (offenderSubgroup_ne_bot_of_ff ρ (sevenFour_isFF ρ hL e))

/-- The corrected B.4.2(7) case, retaining the literal actor identification. -/
theorem sevenFour_source (hL : L = ⊤)
    (e : ActionEquiv (ρ.comp L.subtype) Model.natural) :
    ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) :=
  .alternatingSeven (sevenFour_offenderSubgroup ρ hL e) hL e.groupEquiv
    (sevenFour_dimension ρ e) (sevenFour_offenders ρ hL e) (sevenFour_quadraticRatio ρ hL e)

/-- K.1.2, four-dimensional branch. The extra Chapter K input needs no additional
use once its separate recognition owner supplies the genuine model intertwiner. -/
theorem sevenFour_conclusion {K : GroupClass.{u}} (_input : Input ρ K L) (hL : L = ⊤)
    (e : ActionEquiv (ρ.comp L.subtype) Model.natural) : Conclusion ρ L :=
  .ff (.sevenFour hL e) (sevenFour_source ρ hL e)

end CFSG.Quasithin.ChapterK.Alternating
