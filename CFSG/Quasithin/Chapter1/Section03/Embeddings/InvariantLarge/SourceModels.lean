module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.LocalPair
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.SymplecticAction
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even

/-!
# Central covers and the surviving large-prime models

The genuine A/C source assembly of A.3.6 bounds the center of a quasisimple
component with trivial two-core by three. Thus the original p-complement,
for p > 3, embeds through its central quotient. The ordinary scalar-cover
recognition lifts a PSL₃(p) quotient to the actual SL₃ or PSL₃ carrier.
The proved vanishing symplectic multiplier similarly lifts PSp₄(2ⁿ) to Sp₄.

In the symplectic Cartan case, the established diagram classification removes
the older semilinear premise. The literal normalizer action yields a cyclic
automizer, and the intrinsic Frattini commutator identity forces even field
degree. Abelianness removes the extraspecial alternative and supplies the
actual elementary-plane equivalence. Cartan placement is supplied by A.3.15;
these model calculations do not assume the final embedding alternatives.

Source: Aschbacher–Smith A.3.6, A.3.15 and I.1.3; Proposition 1.3.4,
printed pp.510–511, invariant p > 3 case.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge
universe u

private theorem center_card_of_common {Q : Type*} [Group Q] [Finite Q]
    [IsQuasisimple Q] (h : Section02.A36Common Q) :
    Nat.card (center Q) = 1 ∨ Nat.card (center Q) = 3 := by
  have hF : fittingSubgroup Q = center Q := le_antisymm
    ((le_solvableRadical _ inferInstance inferInstance).trans
      IsQuasisimple.solvableRadical_le_center) (le_sSup ⟨inferInstance, inferInstance⟩)
  have hR : solvableRadical Q = center Q := le_antisymm
    IsQuasisimple.solvableRadical_le_center
    (le_solvableRadical _ inferInstance inferInstance)
  rcases h.2.2.1 with hh | hh
  · have he := hh.2.2
    rw [hF, hR, relIndex_self] at he
    omega
  · simpa only [hF] using hh.2.2

theorem quasisimple_center_card_of_sources
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {Q : Type u} [Group Q] [Finite Q] [IsQuasisimple Q]
    (hsq : IsSQTK KnownSimple.IsKnownSimple Q) (hcore : pCore 2 Q = ⊥) :
    Nat.card (center Q) = 1 ∨ Nat.card (center Q) = 3 := by
  let : IsQuasisimple (⊤ : Subgroup Q) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have hcomp : IsComponent Q (⊤ : Subgroup Q) :=
    ⟨(inferInstance : (⊤ : Subgroup Q).Normal).isSubnormal, inferInstance⟩
  have hc := (ChapterA.SQTKStructure.a36Input_of_theoremsAC hA hC Q hsq hcore
    ⊤ (component_isCComponent hcomp)).2
  have he := Nat.card_congr (centerCongr (topEquiv : (⊤ : Subgroup Q) ≃* Q)).toEquiv
  simpa only [he] using center_card_of_common hc

theorem SylowInput.component_center_coprime
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {G : Type u} [Group G] [Finite G] {p : ℕ} {T X P H L : Subgroup G}
    (h : SylowInput KnownSimple.IsKnownSimple p T X P H L) (hp : 3 < p) :
    Nat.Coprime p (Nat.card (center (XiQuotient L))) := by
  let : IsQuasisimple (XiQuotient L) := h.component_quasisimple
  rcases quasisimple_center_card_of_sources hA hC
      (InvariantThree.component_quotient_sqtk h.sqtk h.component.1)
      (pCore_quotient_pCore_eq_bot 2) with hc | hc
  · rw [hc]
    exact Nat.coprime_one_right p
  · rw [hc]
    exact (h.prime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hp))

theorem linearThreeModel_of_central_quotient
    {Q : Type*} [Group Q] [Finite Q] [Group.IsPerfect Q]
    {p : ℕ} (hprime : p.Prime) (hp : 3 < p) (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 p) :
    LinearThreeModel p Q := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  by_cases hz : center Q = ⊥
  · exact Or.inr ⟨F, inferInstance, inferInstance, hF,
      ⟨QuotientGroup.quotientBot.symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans e)⟩⟩
  · have h2 : Nat.card F ≠ 2 := by omega
    have h4 : Nat.card F ≠ 4 := by
      intro hh
      have hp4 : p = 4 := hF.symm.trans hh
      norm_num [hp4] at hprime
    obtain ⟨_, _, _, j, _⟩ :=
      Matrix.PSL3.OrdinaryCenterRecognition.nontrivial_center_recognition h2 h4 e hz
    exact Or.inl ⟨F, inferInstance, inferInstance, hF, ⟨j.symm⟩⟩

/-- An abelian intrinsic complement is the actual elementary plane. -/
theorem plane_of_commutative {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (h : XiOddQuotient p Q) (hc : IsMulCommutative Q) :
    Nonempty (Q ≃* Plane p) := by
  let _ := hc
  rcases h with ⟨he, hcard⟩ | ⟨he, _, _⟩
  · let _ := he
    exact InvariantThree.plane_of_elementary_card hcard
  · exact ((QuotientGroup.nontrivial_iff.mp he.quotient_nontrivial)
      (center_eq_top (G := Q))).elim

/-- The literal central quotient marking lifts to the full symplectic carrier. -/
theorem symplectic_whole_model {Q : Type*} [Group Q] [Group.IsPerfect Q]
    {n : ℕ} (hn : 1 < n) (hm : ClassicalGroup.IsPSp (Q ⧸ center Q) 2 (2^n)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2^n ∧
      Nonempty (Q ≃* Matrix.symplecticGroup (Fin 2) F) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨j, _⟩ := Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.exists_whole_model
    hF hn (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)
  exact ⟨F, inferInstance, inferInstance, hF, ⟨j⟩⟩

/-- All symplectic conclusions from the actual normalized Sylow intersection;
semilinear classification and the plane computation are discharged. -/
theorem symplectic_alternative_of_normalizes
    {J F : Type*} [Group J] [Finite J] [Field F] [Finite F]
    {n p : ℕ} [Fact p.Prime] (hF : Nat.card F = 2^n) (hn : 1 < n) (hp : 3 < p)
    (D : Subgroup J) [D.Normal]
    (e : Matrix.symplecticGroup (Fin 2) F ≃* D) (S : Sylow 2 J)
    (B : Subgroup J) (hBD : B ≤ D) (hC : centralizer (D : Set J) = ⊥)
    (hBn : B ≤ normalizer ((S : Subgroup J) ⊓ D : Subgroup J))
    (hB : XiOddQuotient p B)
    (hcomm : B = ⁅B, (frattini ((S : Subgroup J) ⊓ normalizer B : Subgroup J)).map
      ((S : Subgroup J) ⊓ normalizer B).subtype⁆) :
    Nonempty (B ≃* Plane p) ∧ IsCyclic (automizer S B) ∧
      Nat.ModEq p (2^n) 1 ∧ Even n := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hne : B ≠ ⊥ := by
    intro hb
    have hc := hB.one_lt_card (Fact.out : p.Prime)
    simp only [hb, Nat.card_eq_fintype_card, Fintype.card_unique] at hc
    omega
  obtain ⟨ha, hc, hm, he⟩ := SymplecticAction.abelian_cyclic_and_parameter_restrictions
    hF hn hp Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
    D e S B hBD hC hBn hB.isPGroup hne hcomm
  exact ⟨plane_of_commutative hB ha, hc, hm, he⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge
