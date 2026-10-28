module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.G2TwoCore.Reduction
public import Theory.AtlasPort.LinearGroups.G2.SylowOvergroupCharacteristic
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.MarkedRestriction

/-!
# The nontrivial two-core of the G₂ component intersection

The source S₃ shadow and prime-to-three residual construct a solvable
Sylow overgroup. Its small three-part supplies a nontrivial two-core,
and G₂ parabolic geometry makes it a group of characteristic two.
The residual therefore has nontrivial two-core; its characteristicity
and relative normality put this core in the two-core of the literal
component intersection J.

Both adapters discharge every model premise. The full split-octonion
group uses its positive-root Sylow of order q⁶; G₂(2)′ uses the actual
derived Sylow of order 32. Neither argument assumes recognition,
parabolic containment of J, or simplicity of an unrelated model.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.26–28, printed pp.1130–1131 (PDF pp.1147–1148).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve.G2TwoCore
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}

private theorem transport_characteristic {A B : Type*}
    [Group A] [Group B] [Finite A] [Finite B] (e : A ≃* B)
    (hchar : ∀ (Q : Sylow 2 B) (H : Subgroup B), (Q : Subgroup B) ≤ H →
      pCore 2 H ≠ ⊥ → centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (Q : Sylow 2 A) (H : Subgroup A) (hQH : (Q : Subgroup A) ≤ H)
    (hcore : pCore 2 H ≠ ⊥) :
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  let f := e.subgroupMap H
  have hm : pCore 2 (H.map e.toMonoidHom) ≠ ⊥ := by
    intro h
    exact hcore (((pCore 2 H).map_eq_bot_iff_of_injective f.injective).mp
      ((pCore_map_iso 2 f).trans h))
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 f).mpr
    (hchar (Q.mapSurjective (f := e.toMonoidHom) e.surjective) _ (map_mono hQH) hm)

/-- The source adapter for an actual equivalence with the full G₂ model. -/
theorem full_twoCore_ne_bot (a : Input d I c) (F : ClassificationField)
    (e : d.starImage I c.L ≃* Atlas.G2.Model F.Carrier) :
    pCore 2 ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)) ≠ ⊥ := by
  apply intersection_twoCore_of_sylow_overgroups a
  · intro Q
    apply Q.pow_dvd_card_of_pow_dvd_card (n := 2)
    rw [Nat.card_congr e.toEquiv]
    apply dvd_trans _ (Atlas.G2.unipotent (K := F.Carrier)).card_subgroup_dvd_card
    rw [Atlas.G2.card_unipotent]
    obtain ⟨n, hn, he⟩ := Atlas.G2.LieParabolicSetup.field_card (F := F.Carrier)
    rw [he, ← pow_mul]
    exact pow_dvd_pow 2 (by omega : 2 ≤ n * 6)
  · exact transport_characteristic e Atlas.G2.SylowOvergroupCharacteristic.full

/-- The source adapter for the proper binary commutator carrier G₂(2)′. -/
theorem binary_twoCore_ne_bot (a : Input d I c)
    (e : d.starImage I c.L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    pCore 2 ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)) ≠ ⊥ := by
  apply intersection_twoCore_of_sylow_overgroups a
  · intro Q
    apply Q.pow_dvd_card_of_pow_dvd_card (n := 2)
    rw [Nat.card_congr e.toEquiv]
    apply dvd_trans _ (Atlas.G2.BinaryParabolicPair.derivedSylow :
      Subgroup (commutator (Atlas.G2.Model (ZMod 2)))).card_subgroup_dvd_card
    rw [Atlas.G2.BinaryParabolicPair.card_derivedSylow]
    decide
  · exact transport_characteristic e Atlas.G2.SylowOvergroupCharacteristic.binary_derived

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve.G2TwoCore
