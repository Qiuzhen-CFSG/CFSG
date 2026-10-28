module

public import CFSG.Quasithin.Chapter3.Section01.Source318
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard

/-!
# The standing guard for the 3.1.8 source implication

The source assumes, after Theorem 2.1.1, that the fixed Sylow two-subgroup is
contained in at least two maximal two-locals.  The older `SourceTheorem318One`
declaration is deliberately kept as the conditional earlier-source interface.
This file records the guarded form separately: its conclusion is the same
literal quotient-ratio implication, while its hypotheses include an actual
maximal two-local outside the selected one and hence a genuine `HStar` member.

Source: Aschbacher--Smith, Theorem 3.1.8(1), printed p.576, with the standing
assumption from the paragraph following Theorem 2.1.1.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The body of Theorem 3.1.8(1), with `T` and the selected maximal local `M`
fixed.  Keeping this as a separate definition lets the guarded interface
retain the exact legacy `SourceTheorem318One` statement. -/
def SourceTheorem318OneAt (T : Sylow 2 G) (M : Subgroup G) : Prop :=
  ∀ (L : Subgroup G),
    IsPPerfect 2 L → L ≤ M → (L.subgroupOf M).Normal →
    IsMaximalTwoLocal M → L ⊔ (T : Subgroup G) ≤ M →
    (∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = M) →
    ∀ (V : Subgroup (L ⊔ (T : Subgroup G) : Subgroup G))
      (hV : IsPReduced 2 V),
      (T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)) ⊓
        centralizer (V : Set (L ⊔ (T : Subgroup G) : Subgroup G)) =
        pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) →
      letI := hV.normal
      letI := hV.elementary
      cubicRatio (Representation.NormalElementaryQuotient.representation V
        (QuotientGroup.mk' (centralizer (V : Set (L ⊔ (T : Subgroup G) : Subgroup G))))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2

omit [Finite G] in
/-- Apply the fixed-local ratio implication through its public interface.
The definition body remains hidden; every original local hypothesis is retained. -/
theorem SourceTheorem318OneAt.cubicRatio_le
    {T : Sylow 2 G} {M : Subgroup G} (h : SourceTheorem318OneAt T M)
    (L : Subgroup G) (hL : IsPPerfect 2 L) (hLM : L ≤ M)
    (hLN : (L.subgroupOf M).Normal) (hM : IsMaximalTwoLocal M)
    (hLTM : L ⊔ (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = M)
    (V : Subgroup (L ⊔ (T : Subgroup G) : Subgroup G)) (hV : IsPReduced 2 V)
    (hc : (T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)) ⊓
      centralizer (V : Set (L ⊔ (T : Subgroup G) : Subgroup G)) =
        pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) :
    letI := hV.normal
    letI := hV.elementary
    cubicRatio (Representation.NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set (L ⊔ (T : Subgroup G) : Subgroup G))))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2 :=
  h L hL hLM hLN hM hLTM hu V hV hc

omit [Finite G] in
/-- Construct the fixed-local source implication from its literal quotient
bound, without exposing the definition body across module boundaries. -/
theorem SourceTheorem318OneAt.of_cubicRatio_le
    {T : Sylow 2 G} {M : Subgroup G}
    (h : ∀ (L : Subgroup G),
      IsPPerfect 2 L → L ≤ M → (L.subgroupOf M).Normal →
      IsMaximalTwoLocal M → L ⊔ (T : Subgroup G) ≤ M →
      (∀ N : Subgroup G, IsMaximalTwoLocal N →
        L ⊔ (T : Subgroup G) ≤ N → N = M) →
      ∀ (V : Subgroup (L ⊔ (T : Subgroup G) : Subgroup G))
        (hV : IsPReduced 2 V),
        (T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)) ⊓
          centralizer (V : Set (L ⊔ (T : Subgroup G) : Subgroup G)) =
          pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) →
        letI := hV.normal
        letI := hV.elementary
        cubicRatio (Representation.NormalElementaryQuotient.representation V
          (QuotientGroup.mk' (centralizer (V : Set (L ⊔ (T : Subgroup G) : Subgroup G))))
          (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2) :
    SourceTheorem318OneAt T M := h

/-- The source implication with the post-2.1.1 standing guard made explicit.
The existential conclusion exposes the literal `HStar` witness obtained by
finite minimal descent; the ratio implication is unchanged. -/
def GuardedSourceTheorem318One (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (M : Subgroup G),
    IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
    HasMaximalOutside T M →
    ∃ H : Subgroup G, H ∈ HStar (T : Subgroup G) M ∧
      SourceTheorem318OneAt T M

/-- Construct the guarded theorem from fixed-local implications under the
same standing guard; finite descent supplies the required `HStar` witness. -/
theorem GuardedSourceTheorem318One.of_fixedLocal
    (h : ∀ (T : Sylow 2 G) (M : Subgroup G),
      IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      HasMaximalOutside T M → SourceTheorem318OneAt T M) :
    GuardedSourceTheorem318One G := by
  intro T M hM hTM hout
  obtain ⟨H, hH⟩ := exists_HStar_of_hasMaximalOutside hout
  exact ⟨H, hH, h T M hM hTM hout⟩

/-- The legacy source implication yields the guarded interface, while the
standing witness is proved from the actual two-local hypotheses.  This is an
adapter, not a proof of the earlier source theorem. -/
theorem guardedSourceTheorem318One_of_sourceTheorem318One
    (h318 : SourceTheorem318One G) : GuardedSourceTheorem318One G := by
  intro T M hM hTM houtside
  obtain ⟨H, hH⟩ := exists_HStar_of_hasMaximalOutside houtside
  refine ⟨H, hH, ?_⟩
  intro L hL hLM hLN hM' hLTM hu V hV hcore
  exact h318 T L M hL hLM hLN hM' hLTM hu V hV hcore

/-- The same adapter in the literal post-2.1.1 form: two distinct maximal
two-locals containing `T` are supplied, rather than the derived outside
witness. -/
theorem guardedSourceTheorem318One_of_two_distinct
    (h318 : SourceTheorem318One G)
    {T : Sylow 2 G} {M N : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hN : IsMaximalTwoLocal N)
    (hTM : (T : Subgroup G) ≤ M) (hTN : (T : Subgroup G) ≤ N)
    (hMN : N ≠ M) :
    ∃ H : Subgroup G, H ∈ HStar (T : Subgroup G) M ∧
      SourceTheorem318OneAt T M :=
  guardedSourceTheorem318One_of_sourceTheorem318One h318 T M hM hTM
    (hasMaximalOutside_of_two_distinct hM hN hTM hTN hMN)

/-- Extract the literal ratio implication from the guarded interface. -/
theorem sourceTheorem318OneAt_of_guarded
    (h : GuardedSourceTheorem318One G)
    {T : Sylow 2 G} {M : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (houtside : HasMaximalOutside T M) : SourceTheorem318OneAt T M := by
  obtain ⟨_, _, hAt⟩ := h T M hM hTM houtside
  exact hAt

end CFSG.Quasithin.Chapter3
