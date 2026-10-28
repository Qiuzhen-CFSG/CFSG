module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankTwoUnitary
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.SU3.BinaryG2Comparison
public import Theory.SpecificGroups.Tits.SylowFixerCentralizer

/-!
# Small binary rank-two exclusions on the original component

The actual derived Sp4(2) and G2(2) models are transported to A6 and
PSU3(3), respectively, where the original marked component is already
excluded. For Tits, the original faithful Sylow E9 centralizes the same
nonidentity Sylow-fixing involution, contradicting the native centralizer
order. This removes all small-derived constructors of Theorem C.

The remaining alternatives are four nonlinear even-characteristic families and
PSL5(2). The exact centralizer quotient three-core and all earlier geometry
hypotheses are retained. Rank one, the abelian point span and the universal
natural-module reduction remain source obligations.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)


include hz hTz hH a in
/-- The derived binary symplectic model is the same excluded A6 component. -/
theorem SourceHypothesis.original_selectedComponent_not_binarySymplecticDerived :
    ¬ Nonempty (Nonabelian.Setup.star H c.K ≃*
      commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  rintro ⟨e⟩
  exact S.original_selectedComponent_not_alternatingSix D hZ z hz hTz hH c a
    ⟨e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩

include hz hTV hTz hbound hH hn a in
/-- The derived binary G2 model is the same excluded ternary unitary component. -/
theorem SourceHypothesis.original_rank_two_not_binaryG2Derived
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) :
    ¬ Nonempty (Nonabelian.Setup.star H c.K ≃*
      commutator (Atlas.G2.Model (ZMod 2))) := by
  rintro ⟨e⟩
  obtain ⟨f⟩ := Atlas.G2.nonempty_commutator_binary_equiv_psu3
  apply S.original_rank_two_not_unitaryThreeThree D hZ z hz hTV hTz hbound hH hn c a hTI hns hr
  refine ⟨GaloisField 3 2,inferInstance,inferInstance,ABG.unitaryForm 3 3 1 (by decide),
    GaloisField.card 3 2 (by decide),?_,⟨e.trans f⟩⟩
  intro x
  change iterateFrobeniusEquiv (GaloisField 3 2) 3 1 x = x ^ 3
  simp only [iterateFrobeniusEquiv_def,pow_one]

include hz hTV hTz hbound hH hn a in
/-- The original Sylow E9 excludes Tits on the actual selected component. -/
theorem SourceHypothesis.original_rank_two_not_tits
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) :
    ¬ Nonempty (Nonabelian.Setup.star H c.K ≃* Tits.ParrottGroup) := by
  rintro ⟨e⟩
  obtain ⟨α,hα,⟨P,hP⟩,h9⟩ := S.original_rank_two_model_centralizer
    D hZ z hz hTV hTz hbound hH hn c a hTI hns hr e
  exact Tits.not_three_dvd_sylow_fixer_centralizer P α
    (by intro he; simp [he] at hα) hP ((by decide : 3 ∣ 9).trans h9)

include hz hTV hTz hbound hH hn a in
/-- The literal rank-two source now retains only four nonlinear families or PSL5(2). -/
theorem SourceHypothesis.original_rank_two_large_even_models
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) :
    let B := Nonabelian.Setup.star H c.K
    let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
    let C := centralizer (U : Set a.action.range)
    2 ≤ primeRank 3 (pCore 3 (C ⧸ pCore 2 C)) ∧
      ((∃ f, 2 ≤ f ∧ ClassicalGroup.IsPSp B 2 (2^f)) ∨
        (∃ f, 2 ≤ f ∧ ClassificationModels.IsG2At B (2^f)) ∨
        (∃ f, 1 ≤ f ∧ Triality.Standard.IsTrialityGroupAt (2^f) B) ∨
        (∃ m, 1 ≤ m ∧ Nonempty (B ≃* ReeF4.Model m)) ∨
        ClassicalGroup.IsPSL B 5 2) := by
  obtain ⟨hcore,hmodels⟩ := S.original_rank_two_even_models D hZ z hz hTV hTz
    hbound hH hn c a hTI hns hr
  refine ⟨hcore,?_⟩
  rcases hmodels with ⟨f,hm,hnl⟩|h
  · cases hm with
    | linear hf he => exact (hnl he).elim
    | symplectic hf he => exact Or.inl ⟨f,hf,he⟩
    | g2 hf he => exact Or.inr (Or.inl ⟨f,hf,he⟩)
    | triality hf he => exact Or.inr (Or.inr (Or.inl ⟨f,hf,he⟩))
    | ree_f4 m hm hf he => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m,hm,he⟩)))
    | symplectic_derived hf he =>
      exact (S.original_selectedComponent_not_binarySymplecticDerived D hZ z hz hTz hH c a he).elim
    | g2_derived hf he =>
      exact (S.original_rank_two_not_binaryG2Derived D hZ z hz hTV hTz hbound hH hn c a hTI hns hr he).elim
    | tits hf he =>
      exact (S.original_rank_two_not_tits D hZ z hz hTV hTz hbound hH hn c a hTI hns hr he).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
end CFSG.Quasithin.Chapter12.Section06
