module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Ambient

/-!
# The mixed-plane orbit certificate

The source choice in MS93 (5.6), used in (5.12)(3), retains the fixed plane
of the original first edge. Two generation identities alone do not retain
this marking. The finite construction here chooses one conjugator giving
both identities and normalizing the three-pair cube of that original edge.

The proof uses the normalizer orbit of the sixteen mixed planes generating
S6 with the marked plane. Every remaining mixed plane has a nonidentity
common centralizer, so cannot generate S6 with it. All finite certificates
are checked by kernel reduction.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
local notation "S" => Equiv.Perm (Fin 6)

private def cross : S := Equiv.swap 1 2 * Equiv.swap 3 4
private def rotate : S :=
  (Equiv.swap 0 2 * Equiv.swap 2 4) * (Equiv.swap 1 3 * Equiv.swap 3 5)
private def normalWords : List S :=
  let r : Fin 8 → S := ![1, Equiv.swap 0 1, Equiv.swap 2 3,
    Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 0 1,
    Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 2 3,
    Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 0 1 * Equiv.swap 2 3]
  (List.ofFn r) ++ (List.ofFn fun i => r i * swap45)
private def allWords : List S := permsOfList [0,1,2,3,4,5]

private theorem mem_allWords (x : S) : x ∈ allWords := by
  apply mem_permsOfList_of_mem
  intro i _
  fin_cases i <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem orbit_certificate : allWords.all (fun u =>
    normalWords.any (fun r => decide (∀ i : Fin 4,
      (MulAut.conj u) (planeWords 0 i) =
        (MulAut.conj r) ((MulAut.conj cross) (planeWords 0 i)))) ||
    normalWords.any (fun r => decide (r ≠ 1 ∧ ∀ i : Fin 4,
      r * (MulAut.conj u) (planeWords 0 i) =
        (MulAut.conj u) (planeWords 0 i) * r))) = true := by decide +kernel

private theorem normalWords_centralize : ∀ r ∈ normalWords, ∀ i : Fin 4,
    r * planeWords 0 i = planeWords 0 i * r := by
  have cert : normalWords.all (fun r => decide (∀ i : Fin 4,
      r * planeWords 0 i = planeWords 0 i * r)) = true := by decide +kernel
  simpa only [List.all_eq_true,decide_eq_true_eq] using cert

private theorem normalWords_normalize_cube : ∀ r ∈ normalWords,
    ∀ i : Fin 8, ∃ j : Fin 8, (MulAut.conj r) (dWords i) = dWords j := by
  have cert : normalWords.all (fun r => decide (∀ i : Fin 8,
      ∃ j : Fin 8, (MulAut.conj r) (dWords i) = dWords j)) = true := by decide +kernel
  simpa only [List.all_eq_true,decide_eq_true_eq] using cert

private theorem normalWords_mem_normalizer (r : S) (hr : r ∈ normalWords) :
    r ∈ normalizer ((D 6) : Set S) := by
  apply (mem_normalizer_iff_map_conj_eq).mpr
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨g,hg,rfl⟩
    obtain ⟨i,rfl⟩ := (mem_disjointTranspositions_iff 3 g).mp hg
    obtain ⟨j,hj⟩ := normalWords_normalize_cube r hr i
    exact (mem_disjointTranspositions_iff 3 _).mpr ⟨j,hj.symm⟩
  · rw [card_map_of_injective (MulAut.conj r).injective]

private theorem canonical_plane_orbit (u : S)
    (hgen : plus ⊔ plus.map (MulAut.conj u).toMonoidHom = ⊤) :
    ∃ r ∈ normalWords,
      plus.map (MulAut.conj u).toMonoidHom =
        (plus.map (MulAut.conj cross).toMonoidHom).map (MulAut.conj r).toMonoidHom := by
  have cert : ∀ u ∈ allWords,
      (∃ r ∈ normalWords, ∀ i : Fin 4, (MulAut.conj u) (planeWords 0 i) =
        (MulAut.conj r) ((MulAut.conj cross) (planeWords 0 i))) ∨
      (∃ r ∈ normalWords, r ≠ 1 ∧ ∀ i : Fin 4,
        r * (MulAut.conj u) (planeWords 0 i) = (MulAut.conj u) (planeWords 0 i) * r) := by
    simpa only [List.all_eq_true,Bool.or_eq_true,List.any_eq_true,decide_eq_true_eq] using orbit_certificate
  rcases cert u (mem_allWords u) with ⟨r,hr,he⟩ | ⟨r,hr,hne,hcomm⟩
  · refine ⟨r,hr,?_⟩
    ext x
    constructor
    · rintro ⟨g,hg,rfl⟩
      obtain ⟨i,rfl⟩ := (mem_plus_iff g).mp hg
      change (MulAut.conj u) (planeWords 0 i) ∈ _
      rw [he i]
      exact mem_map_of_mem _ (mem_map_of_mem _ ((mem_plus_iff _).mpr ⟨i,rfl⟩))
    · rintro ⟨_,⟨g,hg,rfl⟩,rfl⟩
      obtain ⟨i,rfl⟩ := (mem_plus_iff g).mp hg
      change (MulAut.conj r) ((MulAut.conj cross) (planeWords 0 i)) ∈ _
      rw [←he i]
      exact mem_map_of_mem _ ((mem_plus_iff _).mpr ⟨i,rfl⟩)
  · exfalso
    apply hne
    have hcentral : plus ⊔ plus.map (MulAut.conj u).toMonoidHom ≤ centralizer ({r} : Set S) := by
      apply sup_le
      · intro g hg
        obtain ⟨i,rfl⟩ := (mem_plus_iff g).mp hg
        exact mem_centralizer_singleton_iff.mpr (normalWords_centralize r hr i).symm
      · rintro _ ⟨g,hg,rfl⟩
        obtain ⟨i,rfl⟩ := (mem_plus_iff g).mp hg
        exact mem_centralizer_singleton_iff.mpr (hcomm i).symm
    have hc : r ∈ center S := mem_center_iff.mpr (fun x =>
      mem_centralizer_singleton_iff.mp (hcentral (hgen ▸ mem_top x)))
    simpa only [s6_center_eq_bot,mem_bot] using hc

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
