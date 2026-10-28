module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.TrialityGeometry.Transport
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.TrialityGeometry.Normalization
public import Theory.SpecificGroups.Triality.SylowParabolicExtensions

/-!
# The two local extension inputs in the triality branch of E.6.8

The concrete triality geometry fixes each parabolic under every automorphism
preserving its positive Sylow subgroup. The marking of Q ∩ L transports
this to normalization by Q, provided Q normalizes L. The pulled-back full
parabolic is of characteristic two; adjoining the two-group Q preserves
this property in the literal ambient join.

Only relative normality in the join is used. There is no passage to a
faithful conjugation quotient, so any kernel of the action on L remains
in the group whose two-core is being calculated. The argument applies at
q = 2 and does not require perfectness of its central Levi quotient.

`local_extension_calculations` supplies exactly the invariance and
characteristic-two premises of `family_of_marked_model_calculations` from
the parent's original local context. Quotient construction and final family
assembly remain in the parent module.

Source: Aschbacher–Smith E.6.8, printed pp.247–248, and F.1.11–12,
printed pp.262–264 (`refs/quasithin.pdf`); GLS3 §§2.5–2.6.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.TrialityGeometry
open _root_.Triality.Standard

variable {G : Type*} [Group G] {Q L : Subgroup G} {P : Parameters}

/-- The original subgroup Q normalizes both marked component parabolics. -/
theorem componentParabolic_normalized (hp : P.prime = 2)
    (hN : Q ≤ normalizer (L : Set G)) (e : L ≃* Carrier P)
    (hmark : (Q.subgroupOf L).map e.toMonoidHom = Parabolics.unipotent P)
    (a : Parabolics.Node) :
    Q ≤ normalizer (componentParabolic e a : Set G) := by
  simpa only [componentNormalizer_eq hN] using
    componentParabolic_invariant_of_stabilizer e hmark a
      (Parabolics.parabolic_map_eq_of_unipotent_invariant P hp a)

/-- Characteristic two for the actual join with Q, keeping its conjugation
kernel and using normality only relative to that join. -/
theorem parabolicJoin_characteristicTwo_of_isPGroup (hp : P.prime = 2)
    (hN : Q ≤ normalizer (L : Set G)) (hQ : IsPGroup 2 Q)
    (e : L ≃* Carrier P)
    (hmark : (Q.subgroupOf L).map e.toMonoidHom = Parabolics.unipotent P)
    (a : Parabolics.Node) : HasCharacteristicTwo (parabolicJoin Q e a) := by
  have he : componentParabolic e a =
      (Parabolics.parabolic P a).map (L.subtype.comp e.symm.toMonoidHom) := by
    rw [componentParabolic, comap_equiv_eq_map_symm', Subgroup.map_map]
  have hn := componentParabolic_normalized hp hN e hmark a
  rw [he] at hn
  change centralizer (pCore 2 (componentParabolic e a ⊔ Q : Subgroup G) :
    Set (componentParabolic e a ⊔ Q : Subgroup G)) ≤
      pCore 2 (componentParabolic e a ⊔ Q : Subgroup G)
  rw [he]
  exact Parabolics.embedded_parabolic_sup_centralizer_twoCore_le P hp a _
    (L.subtype_injective.comp e.symm.injective) Q hQ hn

/-- The parent's actual Sylow witness supplies the two-group supplement.
The inherited quasisimplicity hypothesis is unnecessary for this local step. -/
theorem parabolicJoin_characteristicTwo_of_sylow (hp : P.prime = 2)
    (hN : Q ≤ normalizer (L : Set G))
    (S : Sylow 2 (L ⊔ Q : Subgroup G))
    (hS : (S : Subgroup (L ⊔ Q : Subgroup G)).map (L ⊔ Q).subtype = Q)
    (e : L ≃* Carrier P)
    (hmark : (Q.subgroupOf L).map e.toMonoidHom = Parabolics.unipotent P)
    (a : Parabolics.Node) : HasCharacteristicTwo (parabolicJoin Q e a) := by
  apply parabolicJoin_characteristicTwo_of_isPGroup hp hN _ e hmark a
  rw [← hS]
  exact S.isPGroup'.map _

/-- Discharge the two local model premises used by the E.6.8 family
construction, at its literal Sylow intersection and ambient joins. -/
theorem local_extension_calculations [Finite G]
    {K : GroupClass} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hN : Q ≤ normalizer (L : Set G)) (hp : P.prime = 2)
    (e : L ≃* Carrier P)
    (hmark : (Q.subgroupOf L).map e.toMonoidHom = Parabolics.unipotent P) :
    (∀ a (β : MulAut (Carrier P)),
      (Parabolics.unipotent P).map β.toMonoidHom = Parabolics.unipotent P →
      (Parabolics.parabolic P a).map β.toMonoidHom = Parabolics.parabolic P a) ∧
    (∀ a, HasCharacteristicTwo (parabolicJoin Q e a)) := by
  obtain ⟨_, S, hS⟩ := local_extension_context h hU hL hQ hN
  exact ⟨Parabolics.parabolic_map_eq_of_unipotent_invariant P hp,
    parabolicJoin_characteristicTwo_of_sylow hp hN S hS e hmark⟩

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.TrialityGeometry
