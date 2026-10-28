module

public import CFSG.Quasithin.ChapterJ.Section04To05.Span.Definitions
public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.Local

/-!
# The centralizer step in J.4.5

For the original Sylow five-subgroup of H, the five-commutator Q₅ has
ambient centralizer Z. Indeed U ≤ Q₅, and C_G(U) = HC. If an element
of HC outside U centralized Q₅, J.2.4 would put Q₅ inside HC. Coprime
splitting Q = Q₅ C_Q(B₅), with C_Q(B₅) ≤ HC, would then force Q ≤ HC,
contradicting their orders. A remaining element of U centralizing Q₅ also
centralizes C_Q(B₅), hence Q, and J.2.2 puts it in Z.

This yields the literal source equality C_G(Q₀ Q₅) = Z and its relative
HC form. Since Z has order two, a nontrivial centralizer in any K of a
subgroup containing Q₅ forces Z ≤ K. The last theorem is the implication
used for K = O₂(F) and the original T_F in the first paragraph of J.4.5.
All earlier local fusion inputs are supplied by the proved J.2 source
assembly for the same local setup.

Source: Aschbacher–Smith, J.4.5(1), printed p.442 (PDF p.453), using
J.2.2(4), J.2.4 and J.4.1(3).
-/

public section
noncomputable section

open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)
  (B5 : Sylow 5 d.toTypeRuSetup.H)

/-- The original HC is the full ambient centralizer of U. -/
theorem centralizer_U : centralizer (d.toTypeRuSetup.U : Set G) = d.toTypeRuSetup.HC := by
  apply le_antisymm
  · intro g hg
    exact ⟨centralizer_le d.ru2.natural.kernel_le hg, hg⟩
  · exact inf_le_right

private theorem not_Q₅_le_HC : ¬ Q₅ d B5 ≤ d.toTypeRuSetup.HC := by
  intro h5
  have hQ : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.HC := by
    rw [Q_eq_Q₅_sup_CQ d B5]
    exact sup_le h5 (five_centralizer_le_HC B5)
  have hc := card_le_of_le hQ
  rw [d.ru2.card_Q d.card_Z, d.card_HC] at hc
  omega

/-- J.2.4 forces every member of HC centralizing Q₅ into the original U. -/
theorem HC_inf_centralizer_Q₅_le_U :
    d.toTypeRuSetup.HC ⊓ centralizer (Q₅ d B5 : Set G) ≤ d.toTypeRuSetup.U := by
  obtain ⟨c⟩ := SourceCompletion.exists_choices d
  have h24 := (SourceCompletion.fusion c).1
  intro h hh
  by_contra hn
  apply not_Q₅_le_HC d B5
  have hC : Q₅ d B5 ≤ d.toTypeRuSetup.Q ⊓ centralizer ({h} : Set G) :=
    le_inf (Q₅_le_Q d B5) (by
      intro q hq
      exact mem_centralizer_singleton_iff.mpr (hh.2 q hq))
  rw [(h24 h hh.1 hn).2.2] at hC
  exact hC.trans (sup_le (zpowers_le.mpr hh.1) d.U_le_HC)

/-- The five-commutator has ambient centralizer exactly the original center line. -/
theorem centralizer_Q₅ : centralizer (Q₅ d B5 : Set G) = d.toTypeRuSetup.Z := by
  apply le_antisymm
  · intro h hh
    have hHC : h ∈ d.toTypeRuSetup.HC :=
      centralizer_U d ▸ centralizer_le (U_le_Q₅ d B5) hh
    have hU : h ∈ d.toTypeRuSetup.U := HC_inf_centralizer_Q₅_le_U d B5 ⟨hHC, hh⟩
    have hCQ : h ∈ centralizer (d.toTypeRuSetup.Q : Set G) := by
      have hQC : d.toTypeRuSetup.Q ≤ centralizer ({h} : Set G) := by
        rw [Q_eq_Q₅_sup_CQ d B5]
        refine sup_le (fun q hq => mem_centralizer_singleton_iff.mpr (hh q hq)) ?_
        intro q hq
        exact mem_centralizer_singleton_iff.mpr
          ((five_centralizer_le_HC B5 hq).2 h hU).symm
      intro q hq
      exact mem_centralizer_singleton_iff.mp (hQC hq)
    exact d.centralizer_Q_inf_U ▸ (show h ∈ d.toTypeRuSetup.U ⊓
      centralizer (d.toTypeRuSetup.Q : Set G) from ⟨hU, hCQ⟩)
  · exact le_centralizer_iff.mpr ((Q₅_le_Q d B5).trans (pCoreIn_le 2 _))

/-- Any subgroup between Q₅ and its original H has precisely the same
ambient centralizer. This is the source application to Q₀Q₅. -/
theorem centralizer_of_Q₅_le {A : Subgroup G} (h5A : Q₅ d B5 ≤ A)
    (hAH : A ≤ d.toTypeRuSetup.H) :
    centralizer (A : Set G) = d.toTypeRuSetup.Z :=
  le_antisymm ((centralizer_le h5A).trans_eq (centralizer_Q₅ d B5))
    (le_centralizer_iff.mpr hAH)

/-- The literal centralizer required in the first paragraph of J.4.5. -/
theorem centralizer_Q₀_sup_Q₅ :
    centralizer ((Q₀ d ⊔ Q₅ d B5 : Subgroup G) : Set G) = d.toTypeRuSetup.Z :=
  centralizer_of_Q₅_le d B5 le_sup_right
    (sup_le (Q₀_le_H d) ((Q₅_le_Q d B5).trans (pCoreIn_le 2 _)))

/-- Relative HC form of the same original centralizer calculation. -/
theorem HC_inf_centralizer_Q₀_sup_Q₅ :
    d.toTypeRuSetup.HC ⊓ centralizer ((Q₀ d ⊔ Q₅ d B5 : Subgroup G) : Set G) = d.toTypeRuSetup.Z := by
  rw [centralizer_Q₀_sup_Q₅ d B5]
  exact inf_eq_right.mpr (d.ru2.natural.kernel_le.trans d.U_le_HC)

/-- A nontrivial centralizer in any K of a subgroup containing Q₅ forces
Z into K. This is the first implication in the O₂(F) contradiction of J.4.5. -/
theorem Z_le_of_nontrivial_centralizer {K A : Subgroup G}
    (h5A : Q₅ d B5 ≤ A) (hC : K ⊓ centralizer (A : Set G) ≠ ⊥) :
    d.toTypeRuSetup.Z ≤ K := by
  have hCZ : K ⊓ centralizer (A : Set G) ≤ d.toTypeRuSetup.Z :=
    inf_le_right.trans ((centralizer_le h5A).trans_eq (centralizer_Q₅ d B5))
  have he : K ⊓ centralizer (A : Set G) = d.toTypeRuSetup.Z := by
    apply eq_of_le_of_card_ge hCZ
    rw [d.card_Z]
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hC
  exact he ▸ (inf_le_left : K ⊓ centralizer (A : Set G) ≤ K)

end CFSG.Quasithin.ChapterJ.RuSubgroup
