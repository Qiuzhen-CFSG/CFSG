module
public import Theory.GroupTheory.GeneralizedFitting.ComponentLayerStructure
public import Theory.GroupTheory.Fitting.Core

/-!
# A component containing the inner part of a common moving actor

Distinct ordinary components commute. If every component is moved by an
actor in K times the center, every other component would both commute with
that actor and equal its commutator with it. Thus K is the entire layer and
is normal. With trivial odd core the remaining generalized-Fitting factor
is exactly the two-core.

Source: Aschbacher–Smith, 2.3.9(6) and 2.4.32–33, printed pp.526,547–548.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- If every component is moved by an actor lying in one component times the
center, that component is the whole layer. -/
theorem IsComponent.eq_layer_of_inner_moving_actor
    {K : Subgroup G} (hK : IsComponent G K) (z a c : G)
    (ha : a ∈ K) (hc : c ∈ center G) (hz : z = a * c)
    (hm : ∀ D : Subgroup G, IsComponent G D → D = ⁅D,zpowers z⁆) :
    K = componentLayer G := by
  have hu (D : Subgroup G) (hD : IsComponent G D) : D = K := by
    by_contra hne
    have hDK : D ≤ centralizer (K : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp (hD.commutator_eq_bot_of_ne hK hne)
    have hDz : zpowers z ≤ centralizer (D : Set G) := by
      apply zpowers_le.mpr
      intro d hd
      have hda : d * a = a * d := (hDK hd a ha).symm
      have hdc : d * c = c * d := mem_center_iff.mp hc d
      rw [hz]
      calc
        d * (a*c) = a * (d*c) := by rw [←mul_assoc,hda,mul_assoc]
        _ = (a*c) * d := by rw [hdc,mul_assoc]
    have hb : D = ⊥ := (hm D hD).trans
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hDz))
    let : IsQuasisimple D := hD.2
    let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
    have hn : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot D).mp hn hb
  apply le_antisymm (show K ≤ componentLayer G from le_sSup hK)
  exact sSup_le (fun D hD => (hu D hD).le)

/-- The same marked actor forces normality, without a further orbit argument. -/
theorem IsComponent.normal_of_inner_moving_actor
    {K : Subgroup G} (hK : IsComponent G K) (z a c : G)
    (ha : a ∈ K) (hc : c ∈ center G) (hz : z = a * c)
    (hm : ∀ D : Subgroup G, IsComponent G D → D = ⁅D,zpowers z⁆) : K.Normal := by
  rw [hK.eq_layer_of_inner_moving_actor z a c ha hc hz hm]
  infer_instance

variable [Finite G]

/-- The characteristic-two failure with trivial odd core supplies an ordinary component. -/
theorem exists_component_of_oddCore_eq_bot
    (ho : pPrimeCore 2 G = ⊥) (hf : generalizedFitting G ≠ pCore 2 G) :
    ∃ K : Subgroup G, IsComponent G K := by
  by_contra! hn
  have he : componentLayer G = ⊥ := bot_unique (sSup_le (fun K hK => (hn K hK).elim))
  exact hf (by rw [generalizedFitting,he,sup_bot_eq,Fitting_eq_pcore G 2 ho])

/-- With trivial odd core, the marked component is the unique semisimple
factor of F*, and the remaining factor is the actual two-core. -/
theorem IsComponent.generalizedFitting_of_inner_moving_actor
    {K : Subgroup G} (hK : IsComponent G K) (z a c : G)
    (ha : a ∈ K) (hc : c ∈ center G) (hz : z = a * c)
    (hm : ∀ D : Subgroup G, IsComponent G D → D = ⁅D,zpowers z⁆)
    (ho : pPrimeCore 2 G = ⊥) : generalizedFitting G = K ⊔ pCore 2 G := by
  rw [generalizedFitting,←hK.eq_layer_of_inner_moving_actor z a c ha hc hz hm,
    Fitting_eq_pcore G 2 ho,sup_comm]

end Theory.GroupTheory
