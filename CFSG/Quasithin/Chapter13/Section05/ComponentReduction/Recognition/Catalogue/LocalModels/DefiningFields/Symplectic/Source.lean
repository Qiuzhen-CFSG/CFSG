module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields.Symplectic
public import Theory.SpecificGroups.SymplecticFour.InvolutionPairs
/-!
# Unconditional larger-field symplectic exclusion in 13.5.21

The native three-type pair construction supplies the remaining matrix
obstruction to the existing source marking. Both the action-level and
literal original-configuration consumers retain their exact chief-group
comparison and quotient; no pair-construction premise remains.
Source: Aschbacher–Smith 13.5.21 and B.4.2(3), printed pp.924,86.
-/
public section
open Subgroup Theory.GroupTheory Representation
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields.Symplectic
open Configuration ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}
  (s : Selected D K) (h : D.Hypothesis) [(componentCentralizer s h).Normal]
private theorem field_large (F:BinaryField) (hlarge:1<F.degree) : 2<Nat.card F.Carrier := by
  rw [F.card_eq]
  exact (show (2:ℕ)^1<2^F.degree from Nat.pow_lt_pow_right (by decide) hlarge)

theorem source_not_symplectic_action
    (hFitting : generalizedFitting (Xhat s h) = Khat s h)
    (hSylow : ∃ S : Sylow 2 (Xhat s h), (S : Subgroup (Xhat s h)) = That s h)
    (hcentral : Vhat s h ≤ centralizer (That s h : Set (Xhat s h)))
    (hcard : Nat.card (Vhat s h) = 2) (hpair : PairCondition s h)
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L)) (F : BinaryField) (hlarge : 1 < F.degree) :
    ¬ Nonempty (ActionEquiv (ρ.comp L.subtype) (binarySymplectic F)) :=
  source_not_symplectic_action_of_native_pairs s h hFitting hSylow hcentral hcard hpair
    ρ L comparison F hlarge (InvolutionPairs.exists_bad_pair (field_large F hlarge))

theorem source_not_symplectic_of_configuration
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (config : SourceConfiguration s h Y hY)
    {E W : Type*} [Group E] [Finite E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W)
    (comparison : Khat s h ≃* ((generalizedFitting E) ⧸ center (generalizedFitting E)))
    (F : BinaryField) (hlarge : 1 < F.degree) :
    ¬ Nonempty (ActionEquiv (ρ.comp (generalizedFitting E).subtype) (binarySymplectic F)) :=
  source_not_symplectic_of_configuration_of_native_pairs s h Y hY config ρ comparison F hlarge
    (InvolutionPairs.exists_bad_pair (field_large F hlarge))
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields.Symplectic
