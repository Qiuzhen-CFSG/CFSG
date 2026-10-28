module

public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import Theory.SpecificGroups.LinearCoefficientEquiv

/-!
# The catalogue reduction in 16.5.10

These output predicates use actual isomorphisms. The characteristic-two list
concerns the full component, and the sporadic list concerns L/Z(L). The input
(E2) instead uses L/O₂(L); the reduction transports through the earlier equality
Z(L) = O₂(L). In particular, excluding the full M₂₂ group only forces its
covering kernel to be nontrivial.

The larger-field rank-two exclusion is retained in every catalogue theorem.
The small-endpoint identifications, cover restrictions, and earlier exclusions
are explicit inputs. This module proves the catalogue sieve, not those inputs
or the numerical and fusion clauses of the source lemma.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
(E2), 16.1.2(1), and 16.5.10(1)–(2), printed pp.1170 and 1198–1199.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.Catalogue

open Subgroup Theory.GroupTheory ClassificationModels ChapterA.Section02
universe u v
variable {L : Type u} [Group L]

/-- The explicit exclusion in the statement of 16.5.10, using the complete
Theorem C rank-two family, including genuine triality and Ree carriers. -/
def ExcludesLargeRankTwo (L : Type u) [Group L] : Prop :=
  ∀ f : ℕ, 1 < f → ¬ IsTheoremCRankTwoModel (L ⧸ center L) f

/-- The small characteristic-two possibilities before the three exceptional
isomorphisms and exclusions are used. This is a model list, not a conclusion. -/
def SmallCharacteristicTwoModel (S : Type u) [Group S] : Prop :=
  IsTheoremCRankTwoModel S 1 ∨
    ClassicalGroup.IsPSL S 4 2 ∨ ClassicalGroup.IsPSL S 5 2

/-- Precisely the full components listed in 16.5.10(1). -/
def RestrictedLieComponent (L : Type u) [Group L] : Prop :=
  Nonempty (L ≃* Tits.ParrottGroup) ∨
    Triality.Standard.IsTrialityGroupAt 2 L ∨
    ClassicalGroup.IsPSL L 4 2 ∨ ClassicalGroup.IsPSL L 5 2

/-- Precisely the seven names in 16.5.10(2). -/
def IsRemainingSporadicName (name : SporadicName) : Prop :=
  name = .m12 ∨ name = .m22 ∨ name = .m24 ∨ name = .j2 ∨
    name = .j4 ∨ name = .hs ∨ name = .ru

/-- The sporadic clause is about the central quotient, not the full cover. -/
def RestrictedSporadicQuotient (L : Type u) [Group L] : Prop :=
  ∃ name : SporadicName, IsRemainingSporadicName name ∧
    Nonempty ((L ⧸ center L) ≃* name.Carrier)

/-- Killing a trivial central kernel gives an actual equivalence. -/
noncomputable def centralQuotientEquiv (hZ : center L = ⊥) :
    (L ⧸ center L) ≃* L :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

/-- Identify the binary matrix carrier before applying the exceptional
PSL₃(2) ≅ PSL₂(7) isomorphism. -/
theorem isPSL_binary_equiv {S : Type v} [Group S] {n : ℕ}
    (h : ClassicalGroup.IsPSL S n 2) :
    Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  let _ : Fintype F := Fintype.ofFinite F
  let eF : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact ⟨e.trans (Matrix.ProjectiveSpecialLinearGroup.ringEquiv eF.symm)⟩

/-- Source rank restrictions leave exponent one; none of the small derived
endpoints is silently replaced by an unrelated family label. -/
theorem small_characteristic_two_of_exclusions
    (hlarge : ExcludesLargeRankTwo L)
    (hLie : IsEvenTypeLieQuotient (L ⧸ center L))
    (hrankOne : ¬ IsBenderModel (L ⧸ center L)) :
    SmallCharacteristicTwoModel (L ⧸ center L) := by
  rcases hLie with h | ⟨f, h⟩ | ⟨n, hn, h⟩
  · exact (hrankOne h).elim
  · have hf : 1 ≤ f := by
      cases h <;> omega
    have hf1 : f = 1 := by
      by_contra hne
      exact hlarge f (by omega) h
    exact Or.inl (hf1 ▸ h)
  · rcases hn with rfl | rfl
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-- Sieve the full characteristic-two component. The cover input is the
specialization of 16.1.2(1) to the small models under (E2). The three
exceptional isomorphisms are actual matrix/derived-group identifications.
The component exclusions come from 16.5.3, 16.5.8 and 16.5.9. -/
theorem restricted_lie_of_exclusions
    (hlarge : ExcludesLargeRankTwo L)
    (hLie : IsEvenTypeLieQuotient (L ⧸ center L))
    (hrankOne : ¬ IsBenderModel (L ⧸ center L))
    (hcover : SmallCharacteristicTwoModel (L ⧸ center L) → center L = ⊥)
    (h32 : ClassicalGroup.IsPSL
      (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) 2 7)
    (hsp : Nonempty (commutator (ClassicalGroup.PSp 2 (ZMod 2)) ≃*
      alternatingGroup (Fin 6)))
    (hg2 : ClassicalGroup.IsPSU (commutator (Atlas.G2.Model (ZMod 2))) 3 3)
    (h27 : ¬ ClassicalGroup.IsPSL L 2 7)
    (ha6 : ¬ Nonempty (L ≃* alternatingGroup (Fin 6)))
    (hu3 : ¬ ClassicalGroup.IsPSU L 3 3) : RestrictedLieComponent L := by
  have hsmall := small_characteristic_two_of_exclusions hlarge hLie hrankOne
  let e := (centralQuotientEquiv (hcover hsmall)).symm
  rcases hsmall with h | h | h
  · cases h with
    | linear hf iso =>
      obtain ⟨a⟩ := isPSL_binary_equiv (by simpa using iso)
      exact (h27 (h32.of_mulEquiv (e.trans a))).elim
    | symplectic hf iso => omega
    | g2 hf iso => omega
    | triality hf iso =>
      exact Or.inr (Or.inl (by simpa using iso.of_mulEquiv e))
    | ree_f4 m hm hf iso => omega
    | symplectic_derived hf iso =>
      obtain ⟨a⟩ := iso
      obtain ⟨b⟩ := hsp
      exact (ha6 ⟨e.trans (a.trans b)⟩).elim
    | g2_derived hf iso =>
      obtain ⟨a⟩ := iso
      exact (hu3 (hg2.of_mulEquiv (e.trans a))).elim
    | tits hf iso => exact Or.inl (iso.map (e.trans ·))
  · exact Or.inr (Or.inr (Or.inl (h.of_mulEquiv e)))
  · exact Or.inr (Or.inr (Or.inr (h.of_mulEquiv e)))

/-- Full M₂₂ exclusion allows a central cover, and proves exactly the
nontrivial-center assertion needed by 16.5.10(2). -/
theorem m22_center_ne_bot_of_full_exclusion
    (_hlarge : ExcludesLargeRankTwo L)
    (h22 : ¬ Nonempty (L ≃* SporadicName.m22.Carrier))
    (hq : Nonempty ((L ⧸ center L) ≃* SporadicName.m22.Carrier)) :
    center L ≠ ⊥ := by
  intro hZ
  exact h22 (hq.map ((centralQuotientEquiv hZ).symm.trans ·))

/-- Remove M₁₁ and M₂₃ using their earlier covering restrictions, while
retaining M₂₂ in the quotient list. Both conclusions of source clause (2)
are retained, and the larger-field exclusion stays explicit. -/
theorem restricted_sporadic_of_exclusions
    (hlarge : ExcludesLargeRankTwo L)
    (hspor : IsEvenTypeSporadicQuotient (L ⧸ center L))
    (h11cover : Nonempty ((L ⧸ center L) ≃* SporadicName.m11.Carrier) → center L = ⊥)
    (h23cover : Nonempty ((L ⧸ center L) ≃* SporadicName.m23.Carrier) → center L = ⊥)
    (h11 : ¬ Nonempty (L ≃* SporadicName.m11.Carrier))
    (h22 : ¬ Nonempty (L ≃* SporadicName.m22.Carrier))
    (h23 : ¬ Nonempty (L ≃* SporadicName.m23.Carrier)) :
    RestrictedSporadicQuotient L ∧
      (Nonempty ((L ⧸ center L) ≃* SporadicName.m22.Carrier) → center L ≠ ⊥) := by
  refine ⟨?_, m22_center_ne_bot_of_full_exclusion hlarge h22⟩
  obtain ⟨name, hj3, hhe, iso⟩ := hspor
  have hnot11 : name ≠ .m11 := by
    intro hn
    subst name
    exact h11 (iso.map ((centralQuotientEquiv (h11cover iso)).symm.trans ·))
  have hnot23 : name ≠ .m23 := by
    intro hn
    subst name
    exact h23 (iso.map ((centralQuotientEquiv (h23cover iso)).symm.trans ·))
  refine ⟨name, ?_, iso⟩
  cases name <;> simp_all [IsRemainingSporadicName]

/-- Move the genuine (E2) alternatives from O₂(L) to Z(L), removing only
the full odd-linear cases. The equality of kernels is an earlier theorem,
not a change of quotient convention. -/
theorem lie_or_sporadic_of_evenType
    (_hlarge : ExcludesLargeRankTwo L)
    (hE2 : IsEvenTypeComponent L) (hcore : center L = pCore 2 L)
    (h33 : ¬ ClassicalGroup.IsPSL L 3 3)
    (h2p : ∀ p : ℕ, IsFermatOrMersennePrime p → ¬ ClassicalGroup.IsPSL L 2 p) :
    IsEvenTypeLieQuotient (L ⧸ center L) ∨
      IsEvenTypeSporadicQuotient (L ⧸ center L) := by
  let e := QuotientGroup.quotientMulEquivOfEq hcore
  rcases hE2 with h | h | ⟨p, hp, h⟩ | h
  · apply Or.inl
    rcases h.1 with h | ⟨f, h⟩ | ⟨n, hn, h⟩
    · exact Or.inl (h.of_mulEquiv e)
    · exact Or.inr (Or.inl ⟨f, h.of_mulEquiv e⟩)
    · exact Or.inr (Or.inr ⟨n, hn, h.of_mulEquiv e⟩)
  · exact (h33 h).elim
  · exact (h2p p hp h).elim
  · obtain ⟨name, hj3, hhe, iso⟩ := h
    exact Or.inr ⟨name, hj3, hhe, iso.map (e.trans ·)⟩

end CFSG.Quasithin.Chapter16.Intersections.Catalogue
