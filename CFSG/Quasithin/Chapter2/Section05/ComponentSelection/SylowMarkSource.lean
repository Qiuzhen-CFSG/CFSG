module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SylowCommutatorSource
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.C129Complete
public import Theory.SpecificGroups.PSL3Even.ThompsonCentralCover.SylowMark
/-! # Original crossing preparation and marked quotients
The three original component models supply their Sylow marks and elementary inverse images without additional geometric inputs.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
theorem linear_simple_sylow_mark
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F)) (P:Sylow 2 L) :
    ∃f:P→*Matrix.PSL3Even.UnipotentGeometry.U F, Function.Surjective f ∧ f.ker=⊥ ∧
      ∀W:Subgroup (Matrix.PSL3Even.UnipotentGeometry.U F),
        IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap f) := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨f,hf,hk,he⟩:=Matrix.PSL3Even.UnipotentGeometry.exists_sylow_cover_mark
    e.toMonoidHom e.surjective (fun W hw=>by
      let :=hw
      exact IsElementaryAbelian.comap_of_injective e.toMonoidHom e.injective W)
    (by omega : 0<n) hF P
  refine ⟨f,hf,?_,he⟩
  simpa only [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective,bot_subgroupOf] using hk

theorem MathieuSourceSetup.linear_four_sylow_mark
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (e:L⧸center L≃*Matrix.PSL3Four.PSL) (P:Sylow 2 L) :
    ∃f:P→*Matrix.PSL3Even.UnipotentGeometry.U Matrix.PSL3Four.F,
      Function.Surjective f ∧ f.ker=(center L).subgroupOf P ∧
      ∀W:Subgroup (Matrix.PSL3Even.UnipotentGeometry.U Matrix.PSL3Four.F),
        IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap f) := by
  let α:=Matrix.PSL3Four.ElementaryParabolic.centerProjection e
  have h:=Matrix.PSL3Even.UnipotentGeometry.exists_sylow_cover_mark α
    (Matrix.PSL3Four.ElementaryParabolic.centerProjection_surjective e)
    (fun W hw=>by
      let :=hw
      exact MathieuSourceSetup.linear_four_elementary_preimage c hG localC129Input_knownSimple hempty e W)
    (by decide : 0<2) (by simpa using Matrix.PSL3Four.card_F) P
  simpa only [α,Matrix.PSL3Four.ElementaryParabolic.centerProjection_ker] using h

theorem derived_symplectic_sylow_mark
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F)) (P:Sylow 2 L) :
    Nonempty (P≃*Theory.SpecificGroups.SymplecticFour.unipotent (F:=F)) := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let eFull:=e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn)
  let Q:=P.mapSurjective (f:=eFull.toMonoidHom) eFull.surjective
  exact ⟨((P:Subgroup L).equivMapOfInjective eFull.toMonoidHom eFull.injective).trans
    (Sylow.equiv Q (Theory.SpecificGroups.SymplecticFour.unipotentSylow hF (by omega)))⟩
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
