module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankOneCubic
public import Theory.SpecificGroups.SU3.BinarySylowFixerCentralizer

/-!
# Excluding the Bender families in the original rank-one branch

The literal cubic line P intersection K embeds into the fixed subgroup of
the original marked involution. The binary linear-two fixed subgroup is a
two-group. In the binary unitary row, the preceding inverted-order argument
forces degree two or four; the full involution centralizer at either degree
has order prime to three. Together with the existing Suzuki exclusion this
removes every Bender row of Theorem C for the same selected component.

All earlier geometry inputs remain explicit. This is the rank-one model
inspection in Aschbacher--Smith, proof of 12.6.26, printed p.833; the odd
linear-two analysis, abelian span and natural reduction remain subsequent
source obligations.
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

include hz hTV hTz hbound hH hn a in
/-- The original binary unitary row has an impossible cubic fixed subgroup. -/
theorem SourceHypothesis.original_selectedComponent_not_binaryUnitary
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {n : ℕ} (hn2 : 2 ≤ n) :
    ¬ ClassicalGroup.IsPSU (Nonabelian.Setup.star H c.K) 3 (2^n) := by
  rintro ⟨F,hFfield,hFfinite,J,hF,hconj,⟨e⟩⟩
  let := hFfield
  let := hFfinite
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [Nat.card_eq_fintype_card,pow_mul] using hF)
  let B := Nonabelian.Setup.star H c.K
  let : IsSimpleGroup B := S.original_selectedComponent_simple D hZ z hz hTV hTz
    hbound hH hn c a hTI hns
  let := c.component.2
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    e.symm.isSimpleGroup
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv B e.toEquiv
  have hcenter : center B = ⊥ := center_eq_bot_of_simple_perfect
  let e₀ : (B ⧸ center B) ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  have heven : Even n := by
    rcases S.original_selectedComponent_binaryUnitary_quotient_degree D hZ z hz hTV hTz
      hbound hns hH hn c a hn2 ⟨F,hFfield,hFfinite,J,hF,hconj,⟨e₀.trans e⟩⟩ with he|he
    · rw [he]; decide
    · rw [he]; decide
  obtain ⟨t,_,ht,⟨Q,hQ⟩,hd⟩ := S.original_selectedComponent_model_fixed_cubic
    D hZ z hz hTV hTz hbound hH hn c a hTI hns e
  exact BenderSuzuki.MatrixGroups.HermitianForm.BinaryFixedCubic.sylow_fixer_three_free
    J hn2 hF hconj heven Q (MulAut.congr e t) ht hQ hd

include hz hTV hTz hbound hH hn a in
/-- All three Bender families are excluded on the same original component and action. -/
theorem SourceHypothesis.original_selectedComponent_not_bender
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    ¬ ClassificationModels.IsBenderModel (Nonabelian.Setup.star H c.K) := by
  intro hm
  cases hm with
  | linear n _ he =>
      exact S.original_selectedComponent_not_binaryLinearTwo_model D hZ z hz hTV hTz
        hbound hH hn c a hTI hns n he
  | unitary n hn2 he =>
      exact S.original_selectedComponent_not_binaryUnitary D hZ z hz hTV hTz
        hbound hH hn c a hTI hns hn2 he
  | suzuki m hm he =>
      exact S.original_selectedComponent_star_not_suzuki D hZ z hz hTV hTz
        hbound hns hH hn c m (by omega) he

end CFSG.Quasithin.Chapter12.Section06
