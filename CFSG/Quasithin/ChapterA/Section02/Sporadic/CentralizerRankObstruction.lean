module

public import CFSG.Quasithin.ChapterA.Section02.Sporadic.CentralizerQuotientOperations
public import CFSG.Quasithin.ChapterA.Section02.Statements.Sections
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# Simple sections of proper involution centralizers

A surjection from a centralizing numerator exhibits a section of the literal
involution centralizer. In a centerless group that centralizer is proper, and
in a finite group it is two-local. Its section therefore has smaller order
than the ambient group. These facts connect the concrete sporadic quotient
maps to the simultaneous induction in Aschbacher--Smith A.2.15(2).

`InvolutionCentralizerRankObstruction` includes the actual involution and
section, nonabelian simplicity, and a 3-rank greater than two. The construction
from quotient data uses the subgroup equivalence for the numerator inside
the centralizer; its kernel is normal only in that numerator. The final
contradiction retains the earlier-source simple-section rank bound explicitly.
No monotonicity of prime rank under arbitrary quotients is used.

Source: *The Classification of Quasithin Groups*, A.2.15(2) and A.2.19,
`refs/quasithin.pdf`, printed pp.37--41 (PDF pp.48--52).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterA

/-- A nonabelian simple section of a proper involution centralizer violating
the bound in source A.2.15(2), with the strict order decrease for induction. -/
def InvolutionCentralizerRankObstruction (G S : Type*) [Group G] [Group S] : Prop :=
  IsSimpleGroup S ∧ ¬ IsMulCommutative S ∧ 2 < primeRank 3 S ∧
    ∃ z : G, orderOf z = 2 ∧
      Subgroup.centralizer ({z} : Set G) ≠ ⊤ ∧
      IsTwoLocal (Subgroup.centralizer ({z} : Set G)) ∧
      Section02.IsSectionOf S (Subgroup.centralizer ({z} : Set G)) ∧
      Nat.card S < Nat.card G

namespace InvolutionCentralizerQuotientData
variable {G S : Type*} [Group G] [Group S]

/-- The actual involution has a proper centralizer in a centerless group. -/
theorem proper_centralizer (d : InvolutionCentralizerQuotientData G S)
    (hcenter : Subgroup.center G = ⊥) :
    Subgroup.centralizer ({d.involution} : Set G) ≠ ⊤ := by
  intro htop
  have hz : d.involution ∈ Subgroup.center G := Subgroup.centralizer_eq_top_iff_subset.mp htop
    (Set.mem_singleton d.involution)
  rw [hcenter] at hz
  have hone : d.involution = 1 := Subgroup.mem_bot.mp hz
  have horder := d.involution_order
  rw [hone, orderOf_one] at horder
  exact (by decide : (1 : ℕ) ≠ 2) horder

/-- Realize the quotient as a section of a proper two-local subgroup. -/
theorem rankObstruction [Finite G] (d : InvolutionCentralizerQuotientData G S)
    (hcenter : Subgroup.center G = ⊥) (hsimple : IsSimpleGroup S)
    (hnonabelian : ¬ IsMulCommutative S) (hrank : 2 < primeRank 3 S) :
    InvolutionCentralizerRankObstruction G S := by
  let e := Subgroup.subgroupOfEquivOfLe d.centralizes
  refine ⟨hsimple, hnonabelian, hrank, d.involution, d.involution_order,
    d.proper_centralizer hcenter,
    Theory.GroupTheory.isTwoLocal_involution_centralizer d.involution_order,
    ?_, d.card_lt hcenter⟩
  exact ⟨d.numerator.subgroupOf _, d.quotientMap.comp e.toMonoidHom,
    d.surjective.comp e.surjective⟩

/-- The source nonabelian simple ambient group supplies centerlessness. -/
theorem rankObstruction_of_simple [Finite G] [IsSimpleGroup G]
    (d : InvolutionCentralizerQuotientData G S) (hG : ¬ IsMulCommutative G)
    (hsimple : IsSimpleGroup S) (hnonabelian : ¬ IsMulCommutative S)
    (hrank : 2 < primeRank 3 S) : InvolutionCentralizerRankObstruction G S := by
  apply d.rankObstruction _ hsimple hnonabelian hrank
  exact (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top.resolve_right
    (fun h => hG (Subgroup.center_eq_top_iff.mp h))
end InvolutionCentralizerQuotientData

/-- Apply the simple-section consequence of earlier source A.2.15(2).
The parent source assembly must supply this induction consequence. -/
theorem InvolutionCentralizerRankObstruction.false_of_section_rank_bound
    {G : Type*} {S : Type} [Group G] [Finite G] [Group S]
    (h : InvolutionCentralizerRankObstruction G S)
    (hsource : ∀ (M : Subgroup G), M ≠ ⊤ → IsTwoLocal M →
      ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T],
        ¬ IsMulCommutative T → Section02.IsSectionOf T M → primeRank 3 T ≤ 2) :
    False := by
  obtain ⟨hs, hna, hr, z, _ho, hproper, hlocal, hsection, _hcard⟩ := h
  let := hs
  let : Finite S := hsection.finite
  exact (not_le_of_gt hr) (hsource _ hproper hlocal S hna hsection)

end CFSG.Quasithin.ChapterA
