module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CoreThompsonSource
public import Theory.SpecificGroups.PSL3Even.ThompsonCentralCover.CommutatorRows
public import Theory.SpecificGroups.SymplecticFour.Sylow.CommutatorRows
/-! # Original component Sylow commutator rows
The three rank-two source branches have class-two component Sylows and
noncentral involution rows of order 2ⁿ. In the exceptional central cover the
row avoids the actual covering center. I.2.2(3b), already proved under the
original ambient hypotheses, discharges every elementary-preimage premise.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
theorem linear_simple_sylow_commutator_rows
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F)) (P:Sylow 2 L) :
    _root_.commutator P≤center P ∧ ∀a:P,a^2=1→a∉center P→
      Nat.card (⁅zpowers a,⊤⁆:Subgroup P)=2^n := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have h:=Matrix.PSL3Even.UnipotentGeometry.sylow_cover_commutator_rows e.toMonoidHom e.surjective
    (fun W hw=>by
      let :=hw
      exact IsElementaryAbelian.comap_of_injective e.toMonoidHom e.injective W)
    (by omega : 0<n) hF P
  exact ⟨h.1,fun a ha hz=>(h.2 a ha hz).1.trans hF⟩

theorem MathieuSourceSetup.linear_four_sylow_commutator_rows
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (e:L⧸center L≃*Matrix.PSL3Four.PSL) (P:Sylow 2 L) :
    _root_.commutator P≤center P ∧ ∀a:P,a^2=1→a∉center P→
      Nat.card (⁅zpowers a,⊤⁆:Subgroup P)=4 ∧
      Disjoint (⁅zpowers a,⊤⁆:Subgroup P) ((center L).subgroupOf P) := by
  let α:=Matrix.PSL3Four.ElementaryParabolic.centerProjection e
  have h:=Matrix.PSL3Even.UnipotentGeometry.sylow_cover_commutator_rows α
    (Matrix.PSL3Four.ElementaryParabolic.centerProjection_surjective e)
    (fun W hw=>by
      let :=hw
      exact MathieuSourceSetup.linear_four_elementary_preimage c hG sourceC hempty e W)
    (by decide : 0<2) (by simpa using Matrix.PSL3Four.card_F) P
  simpa only [α,Matrix.PSL3Four.ElementaryParabolic.centerProjection_ker,Matrix.PSL3Four.card_F] using h

theorem derived_symplectic_sylow_commutator_rows
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F)) (P:Sylow 2 L) :
    _root_.commutator P≤center P ∧ ∀a:P,a^2=1→a∉center P→
      Nat.card (⁅zpowers a,⊤⁆:Subgroup P)=2^n := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let eFull:=e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn)
  have h:=Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.sylow_commutator_rows eFull
    (by omega : 0<n) hF P
  exact ⟨h.1,fun a ha hz=>(h.2 a ha hz).trans hF⟩
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
