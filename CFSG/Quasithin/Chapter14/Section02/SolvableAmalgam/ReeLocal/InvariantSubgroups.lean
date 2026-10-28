module

public import Theory.GroupAction.FaithfulSixteen
public import Theory.GroupAction.FiveInvariantIndexTwo
public import Theory.GroupTheory.PCoreCharacteristicCentralizer
public import Theory.GroupTheory.SelfCentralizingCentralQuotient

/-!
# Ree and Tits quotient-action steps in Lemma 14.2.21

The order-five part of the action image on QH/F, of order sixteen, makes
its invariant subgroups trivial or full. This gives Q = F or Q = QH only
after proving F ≤ Q. The printed full-Ree argument for that containment
uses an incorrect quotient-center identity; the actual second center must
be used instead. Above an index-two layer E < F, the corrected alternatives
also retain an index-two supplement Q with Q ∩ F = E.

The self-centralizing quotient condition excludes Q = E. The additional
supplement can be excluded once E is proved characteristic and
self-centralizing in the actual core Q = O₂(Mc). The imported characteristic
restriction results also handle the case [C_Q(E):E] = 2. These are intrinsic
automorphism arguments, not assumptions that F is already in Q.

These intrinsic intermediate results are consumed by `CoreCandidates`.
The actual model calculations, ambient derived action and residual contradiction
are assembled in `Rigidity`, with source-subgroup applications in
`SourceApplication`. The parent `ReeLocal` module re-exports all these stages.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma 14.2.21, printed p.989, PDF p.1006. The PDF
explicitly defines F = C_H(E), where E = [QH,QH], and later also writes
F = C_Q(E). The concrete parabolic facts are attributed there to Aschbacher,
*The Tits groups as a standard subgroup*, Math. Z. 181 (1982), section 3.
-/

namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal

/-- Once the actual quotient action has an image of order divisible by five, an
invariant subgroup between F and the parabolic two-core is F or the whole core. -/
public theorem invariant_subgroup_alternatives
    {A P : Type*} [Group A] [Group P]
    (F Q : Subgroup P) [F.Normal] [Finite (P ⧸ F)]
    (ρ : A →* MulAut (P ⧸ F))
    (hQ : ∀ a : A, ∀ v : P ⧸ F,
      v ∈ Q.map (QuotientGroup.mk' F) ↔ ρ a v ∈ Q.map (QuotientGroup.mk' F))
    (hFQ : F ≤ Q) (hA : 5 ∣ Nat.card ρ.range) (hV : Nat.card (P ⧸ F) = 16) :
    Q = F ∨ Q = ⊤ := by
  rcases Theory.GroupAction.invariant_eq_bot_or_top_of_image_five ρ hA hV
    (Q.map (QuotientGroup.mk' F)) hQ with h | h
  · left
    exact le_antisymm (by simpa using (Subgroup.map_eq_bot_iff Q).mp h) hFQ
  · right
    have he := congrArg (Subgroup.comap (QuotientGroup.mk' F)) h
    rw [Subgroup.comap_map_eq_self (by simpa using hFQ), Subgroup.comap_top] at he
    exact he

/-- The corrected full-core alternatives from the quotient centralizer chain.
The last case must be treated; it cannot be discarded by irreducibility. -/
public theorem full_core_candidates
    {A P : Type*} [Group A] [Group P] [Finite P]
    (Z E F Q : Subgroup P) [Z.Normal] [F.Normal] [Q.Normal]
    (ρ : A →* MulAut (P ⧸ F))
    (hQ : ∀ a : A, ∀ v : P ⧸ F,
      v ∈ Q.map (QuotientGroup.mk' F) ↔ ρ a v ∈ Q.map (QuotientGroup.mk' F))
    (hZE : Z ≤ E) (hEQ : E ≤ Q) (hEF : E ≤ F)
    (hindex : E.relIndex F = 2) (hFC : F ≤ Subgroup.centralizer (E : Set P))
    (hself : Subgroup.centralizer (Q.map (QuotientGroup.mk' Z) : Set (P ⧸ Z)) ≤
      Q.map (QuotientGroup.mk' Z))
    (hA : 5 ∣ Nat.card ρ.range) (hV : Nat.card (P ⧸ F) = 16) :
    Q = F ∨ Q = ⊤ ∨ (Q ⊓ F = E ∧ Q ⊔ F = ⊤ ∧ Q.index = 2) := by
  rcases Theory.GroupAction.invariant_subgroup_cases_of_index_two_layer
    E F Q ρ hQ hEQ hEF hindex hA hV with h | h
  · subst Q
    have hFE := Subgroup.le_of_centralizer_quotient_le Z E F hZE hFC hself
    have he : E = F := le_antisymm hEF hFE
    simp only [he, Subgroup.relIndex_self] at hindex
    omega
  · exact h

/-- The additional supplement is impossible when its intersection E with F
is characteristic and self-centralizing in the actual ambient two-core.
The concrete model must establish these two intrinsic properties. -/
public theorem exclude_supplement_of_characteristic_selfCentralizing
    {M : Type*} [Group M] [Finite M]
    (E : Subgroup (pCore 2 M)) [E.Characteristic] (F : Subgroup M)
    (hcentral : Subgroup.centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hself : Subgroup.centralizer (E : Set (pCore 2 M)) ≤ E)
    (hFC : F ≤ Subgroup.centralizer (E.map (pCore 2 M).subtype : Set M))
    (hinter : pCore 2 M ⊓ F = E.map (pCore 2 M).subtype)
    (hindex : (E.map (pCore 2 M).subtype).relIndex F = 2) : False := by
  have hFQ : F ≤ pCore 2 M := hFC.trans
    (Subgroup.centralizer_le_pCore_of_characteristic_selfCentralizing 2 hcentral E hself)
  rw [inf_eq_right.mpr hFQ] at hinter
  rw [← hinter, Subgroup.relIndex_self] at hindex
  omega

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal
