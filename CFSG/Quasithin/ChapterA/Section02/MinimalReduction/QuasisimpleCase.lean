module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Cases
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# The quasisimple source case of the simultaneous induction

Once A.2.12 supplies quasisimplicity, the literal center preimage is the
center of the ambient group. The marked A.2.11 identity therefore supplies
its prime-group center. The center is nontrivial, and the original K-group
hypothesis places the actual central quotient in the complete known-simple
catalogue. The alternating quotient is then excluded by its checked odd-cover
restriction and the original A.2.14 rank obstruction.

The quasisimplicity and prime-core identity are precisely the earlier
source steps still to be supplied by the minimal-reduction owner.
Source: Aschbacher–Smith A.2.13–16, printed pp.37–38.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.center_preimage_eq_center [IsQuasisimple G]
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (f : G →* S) (hf : Function.Surjective f) :
    (center S).comap f = center G := by
  have hcard : 2 < Nat.card S := (lemma_A_2_14 h ih).trans_le
    (Theory.GroupTheory.primeRank_le_card p)
  let : Nontrivial S := by
    by_contra hn
    have hs : Subsingleton S := not_nontrivial_iff_subsingleton.mp hn
    have hc : Nat.card S = 1 := by simp
    omega
  let := h.2.2.2.1.isPerfect
  apply le_antisymm
  · rcases IsQuasisimple.normal_le_center_or_eq_top ((center S).comap f) with hc | ht
    · exact hc
    · have hz : center S = ⊤ := by
        apply Subgroup.comap_injective hf
        simpa using ht
      exact (Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp hz)).elim
  · intro x hx
    change f x ∈ center S
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y, rfl⟩ := hf y
    simpa only [map_mul] using congrArg f (mem_center_iff.mp hx y)

theorem CounterexampleToTheoremA.center_isPGroup_of_primeCore [IsQuasisimple G]
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (f : G →* S) (hf : Function.Surjective f)
    (hcore : (center S).comap f = pCore p G) : IsPGroup p (center G) := by
  rw [h.center_preimage_eq_center ih f hf] at hcore
  rw [hcore]
  exact pCore_isPGroup

theorem CounterexampleToTheoremA.center_ne_bot [IsQuasisimple G]
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G) :
    center G ≠ ⊥ := by
  obtain ⟨N, _, hn, hle, _⟩ := h.quotient_by_nontrivial_center_subgroup ih
  intro hc
  exact hn (le_bot_iff.mp (hc ▸ hle))

theorem CounterexampleToTheoremA.centralQuotient_knownSimple [IsQuasisimple G]
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p) :
    KnownSimple.IsKnownSimple (G ⧸ center G) := by
  let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
  exact (h.2.1.quotient (center G)).mem

theorem CounterexampleToTheoremA.not_alternating_centralQuotient [IsQuasisimple G]
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hP : IsPGroup p (center G)) {n : ℕ} (hn : 5 ≤ n)
    (e : G ⧸ center G ≃* alternatingGroup (Fin n)) : False := by
  obtain ⟨hp, _, hz, hr⟩ := odd_primary_alternating_cover hn h.2.2.2.2.1
    h.2.2.2.2.2.1 hP (h.center_ne_bot ih) e
  subst p
  have hh := lemma_A_2_14_center h ih hz
  omega

end CFSG.Quasithin.ChapterA.Section02
