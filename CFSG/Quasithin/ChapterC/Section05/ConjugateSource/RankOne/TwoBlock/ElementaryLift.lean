module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.Pair

/-!
# Lifting maximum elementary families through an actual quotient

If every maximum elementary subgroup of a quotient has elementary full
preimage, then the full preimages are exactly the maximum elementary
subgroups upstairs. The kernel/image order formula proves both the rank
bound and containment of the full kernel. The two-block application proves
elementarity of all four preimages from the actual commuting modules.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G T : Type*} [Group G] [Finite G] [Group T]

omit [Finite G] in
private theorem count_image (f : G →* T) (A : Subgroup G) :
    Nat.card ↥(f.ker ⊓ A) * Nat.card (A.map f) = Nat.card A := by
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (f.ker ⊓ A) A bot_le inf_le_right
  simpa only [relIndex_bot_left,inf_relIndex_right,relIndex_ker] using hh

omit [Finite G] in
private theorem count_preimage (f : G →* T) (hf : Function.Surjective f) (B : Subgroup T) :
    Nat.card f.ker * Nat.card B = Nat.card (B.comap f) := by
  have hk : f.ker ≤ B.comap f := by
    intro g hg
    change f g ∈ B
    rw [MonoidHom.mem_ker.mp hg]
    exact B.one_mem
  have hh := count_image f (B.comap f)
  rwa [inf_eq_left.mpr hk,map_comap_eq_self_of_surjective hf] at hh

/-- A quotient whose maximum elementary subgroups all lift elementarily
has exactly their full preimages as its maximum elementary family. -/
theorem max_family_comap_iff (f : G →* T) (hf : Function.Surjective f)
    (hLift : ∀ B ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup T),
      IsElementaryAbelian 2 (B.comap f)) (A : Subgroup G) :
    A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G) ↔
      ∃ B ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup T), A = B.comap f := by
  let : Finite T := Finite.of_surjective f hf
  have hbound (C : Subgroup G) : Nat.card C ≤ Nat.card f.ker * Nat.card (C.map f) := by
    rw [← count_image f C]
    exact Nat.mul_le_mul_right _ (card_le_of_le inf_le_left)
  have hpre (B : Subgroup T) (hB : B ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup T)) :
      B.comap f ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G) := by
    refine ⟨le_top,hLift B hB,?_⟩
    intro C _ hC
    calc
      Nat.card C ≤ Nat.card f.ker * Nat.card (C.map f) := hbound C
      _ ≤ Nat.card f.ker * Nat.card B := Nat.mul_le_mul_left _ (hB.2.2 _ le_top (hC.map f))
      _ = Nat.card (B.comap f) := count_preimage f hf B
  constructor
  · intro hA
    obtain ⟨B,hB⟩ := elementaryAbelianMaxSubgroups_nonempty (⊤ : Subgroup T)
    have hb : Nat.card B ≤ Nat.card (A.map f) := by
      apply Nat.le_of_mul_le_mul_left (c := Nat.card f.ker)
      · calc
          Nat.card f.ker * Nat.card B = Nat.card (B.comap f) := count_preimage f hf B
          _ ≤ Nat.card A := hA.2.2 _ le_top (hLift B hB)
          _ ≤ Nat.card f.ker * Nat.card (A.map f) := hbound A
      · exact Nat.card_pos
    have hm : A.map f ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup T) :=
      ⟨le_top,hA.2.1.map f,fun C hC he => (hB.2.2 C hC he).trans hb⟩
    exact ⟨A.map f,hm,eq_of_le_of_card_ge (le_comap_map f A)
      (hA.2.2 _ le_top (hLift _ hm))⟩
  · rintro ⟨B,hB,rfl⟩
    exact hpre B hB
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
