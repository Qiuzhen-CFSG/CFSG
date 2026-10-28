module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields.Symplectic.Marking

/-!
# The larger-field symplectic row in 13.5.21

The original Selected D K, simple K̂ = F*(X̂), Sylow-central V̂ of order two,
exact pair condition and genuine B.4.2 action are retained. All innerness,
central-quotient and marking premises are discharged by `Symplectic.Marking`.
Only the intrinsic bad-pair construction for native matrix involutions is
still explicit below. It must be proved for both root types and the mixed
central type before these conditional results give the source exclusion.

The corrected catalogue's binary alternative continues to carry its actual
marked natural action and the commutator subgroup of Sp₄(2).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.2(3), printed p.86, and 13.5.21, printed p.924 (PDF p.941).
-/

public section
open Subgroup Theory.GroupTheory Representation
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields.Symplectic
open Configuration ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}
  (s : Selected D K) (h : D.Hypothesis) [(componentCentralizer s h).Normal]

/-- Source-row assembly with only the intrinsic matrix pair obstruction left explicit. -/
theorem source_not_symplectic_action_of_native_pairs
    (hFitting : generalizedFitting (Xhat s h) = Khat s h)
    (hSylow : ∃ S : Sylow 2 (Xhat s h), (S : Subgroup (Xhat s h)) = That s h)
    (hcentral : Vhat s h ≤ centralizer (That s h : Set (Xhat s h)))
    (hcard : Nat.card (Vhat s h) = 2) (hpair : PairCondition s h)
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L)) (F : BinaryField) (hlarge : 1 < F.degree)
    (badPairs : ∀ t : Sp F.Carrier, orderOf t = 2 → ∃ x : Sp F.Carrier,
      ¬ IsPGroup 2 (zpowers t ⊔ (zpowers t).map (MulAut.conj x).toMonoidHom : Subgroup (Sp F.Carrier)) ∧
      ¬ Nonempty ((zpowers t ⊔ (zpowers t).map (MulAut.conj x).toMonoidHom : Subgroup (Sp F.Carrier)) ≃*
        Equiv.Perm (Fin 3))) :
    ¬ Nonempty (ActionEquiv (ρ.comp L.subtype) (binarySymplectic F)) := by
  rintro ⟨action⟩
  obtain ⟨t, ht, hm⟩ := source_marked_involution s h hFitting hSylow hcentral hcard
    ρ L comparison F hlarge action
  obtain ⟨x, hx, hbad⟩ := badPairs t ht
  exact hbad (source_native_pair_condition s h hpair ρ L comparison F action t hm x hx)

/-- Literal 13.5.21 application, retaining the configuration and the faithful-chief comparison.
The native obstruction is a remaining mathematical prerequisite, not a source hypothesis. -/
theorem source_not_symplectic_of_configuration_of_native_pairs
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (config : SourceConfiguration s h Y hY)
    {E W : Type*} [Group E] [Finite E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W)
    (comparison : Khat s h ≃* ((generalizedFitting E) ⧸ center (generalizedFitting E)))
    (F : BinaryField) (hlarge : 1 < F.degree)
    (badPairs : ∀ t : Sp F.Carrier, orderOf t = 2 → ∃ x : Sp F.Carrier,
      ¬ IsPGroup 2 (zpowers t ⊔ (zpowers t).map (MulAut.conj x).toMonoidHom : Subgroup (Sp F.Carrier)) ∧
      ¬ Nonempty ((zpowers t ⊔ (zpowers t).map (MulAut.conj x).toMonoidHom : Subgroup (Sp F.Carrier)) ≃*
        Equiv.Perm (Fin 3))) :
    ¬ Nonempty (ActionEquiv (ρ.comp (generalizedFitting E).subtype) (binarySymplectic F)) :=
  source_not_symplectic_action_of_native_pairs s h config.proved_prefix.khat_fitting
    config.proved_prefix.marked_sylow config.proved_prefix.actor_central
    config.proved_prefix.actor_card config.condition_iv ρ (generalizedFitting E)
    comparison F hlarge badPairs

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields.Symplectic
