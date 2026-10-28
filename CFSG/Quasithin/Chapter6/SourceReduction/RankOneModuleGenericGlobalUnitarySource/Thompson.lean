module
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourThompson
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.ElementaryAbelianMaxJWeakClosure

/-!
# The inner Thompson subgroup in the prepared unitary-four rows

The original left residual is identified with the actual plane residual by
the ordinary or degree-two compatible amalgam comparison. Sylow and two-core
transport then identify J(T ∩ L) with the original ambient image O₂(L).
Consequently it is weakly closed in T ∩ L under conjugation by the full G.
Both orientations and the literal residual embedding are preserved.

This supplies the inner Thompson calculation used in F.4.35, printed p.292
of `refs/quasithin.pdf`. Equality with J(T), ambient fusion control, and
outer transfer require further arguments and are not asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The reduced common Sylow has precisely the original left two-core as
its elementary Thompson subgroup, including the actual degree-two rows. -/
theorem Preparation.unitary_inner_thompson
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    elementaryAbelianMaxJ ((T : Subgroup G) ⊓ L) = L.pCoreIn 2 := by
  obtain ⟨_,_,⟨e⟩,_⟩ := hc.elim
    (d.unitary_local_structure h hH.1.1.2 hp m hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm)
  let : NeZero m := ⟨by omega⟩
  obtain ⟨P,hP⟩ := exists_sylow_component h.sylow_normalizes
  have hJ : elementaryAbelianMaxJ (P : Subgroup L) = pCore 2 L := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [←elementaryAbelianMaxJ_map_injective e.toMonoidHom e.injective,
      pCore_map_iso]
    exact ChapterF.UnitarySource.FourThompson.plane_thompson m hm
      (P.mapSurjective e.surjective)
  rw [←hP,elementaryAbelianMaxJ_map_injective L.subtype L.subtype_injective,hJ]
  rfl

/-- Every elementary subgroup of maximum order in the reduced Sylow is
exactly O₂(L), rather than merely lying in its abstract isomorphism class. -/
theorem Preparation.unitary_inner_unique_maximum
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (E : Subgroup G)
    (hE : E ∈ elementaryAbelianMaxSubgroups ((T : Subgroup G) ⊓ L)) :
    E = L.pCoreIn 2 := by
  have hJ := d.unitary_inner_thompson h hH hp m hm hc
  have hEQ : E ≤ L.pCoreIn 2 := hJ ▸ le_sSup hE
  have hQS : L.pCoreIn 2 ≤ (T : Subgroup G) ⊓ L := by
    rw [←hJ]
    exact sSup_le fun _ hF => hF.1
  let : IsElementaryAbelian 2 (pCore 2 L) :=
    (d.unitary_core_structure h hH.1.1.2 hp m hm hc).2.2.1
  have hQ : IsElementaryAbelian 2 (L.pCoreIn 2) := IsElementaryAbelian.map L.subtype
  exact eq_of_le_of_card_ge hEQ (hE.2.2 _ hQS hQ)

/-- Ambient conjugation cannot move O₂(L) to a different subgroup inside
the reduced common Sylow. This does not replace that Sylow by T. -/
theorem Preparation.unitary_inner_core_weakly_closed
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (g : G) (hg : (L.pCoreIn 2).conjBy g ≤ (T : Subgroup G) ⊓ L) :
    (L.pCoreIn 2).conjBy g = L.pCoreIn 2 := by
  have hJ := d.unitary_inner_thompson h hH hp m hm hc
  have he := elementaryAbelianMaxJ_map_eq_of_le ((T : Subgroup G) ⊓ L)
    (MulAut.conj g) (by rwa [hJ])
  simpa only [hJ, Subgroup.conjBy] using he

/-- The inner Thompson subgroup recovers the actual full left normalizer.
Nontriviality of the model core makes its normalizer two-local, so the
original maximality of N_G(L) identifies it exactly. -/
theorem Preparation.unitary_inner_thompson_normalizer
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    normalizer (elementaryAbelianMaxJ ((T : Subgroup G) ⊓ L) : Set G) =
      normalizer (L : Set G) := by
  rw [d.unitary_inner_thompson h hH hp m hm hc]
  have hle : normalizer (L : Set G) ≤ normalizer (L.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  have hQ : L.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hz : pCore 2 L = ⊥ :=
      (map_eq_bot_iff_of_injective _ L.subtype_injective).mp he
    have hcard := (d.unitary_core_structure h hH.1.1.2 hp m hm hc).2.2.2.1
    rw [hz,Nat.card_unique] at hcard
    have hgt : 1 < (2^m)^4 :=
      Nat.one_lt_pow (by decide) (Nat.one_lt_pow (by omega) (by decide))
    omega
  exact le_antisymm
    (h.maximal.2 ⟨L.pCoreIn 2,hQ,isPGroup_pCoreIn 2 L,rfl⟩ hle) hle

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
