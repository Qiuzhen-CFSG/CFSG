module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledCoordinates
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesDefs
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedSetup
public import CFSG.Quasithin.ChapterE.Section06.Defs

/-!
# The actual marked doubled orbit in the non-FF source argument

The normalizer-orbit equality identifies N_G(W) with N_G(L), gives
reducedness, and supplies all of E.6.1, including its relative uniqueness
clause. Multiplication gives coordinates on the original orbit subgroup,
intertwining the original L-action with the conjugator-twisted seed pair.
The marked nonisomorphism rules out an intertwiner between the seed and
its inverse-conjugation twist, using that same conjugator.
No equality of W and its chosen seed, graph-automorphism identification,
or numerical bound is assumed or asserted.

Source: Aschbacher--Smith 3.2.5, E.6.1 and 7.0.2--7.1.1,
printed pp.580,244--245 and695--697, as used in12.2.2, p.795.
-/


public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter3.Section02.ChosenSource325

private theorem same_conjugation_of_twist_equiv
    {G : Type*} [Group G] (L V : Subgroup G) [IsElementaryAbelian 2 V]
    (hLV : L ≤ normalizer (V : Set G))
    (t : G) (htL : t ∈ normalizer (L : Set G))
    (e : (doubledSeedAction L V hLV).Equiv
      ((doubledSeedAction L V hLV).comp (doubledTwist L t htL).toMonoidHom)) :
    SameConjugationModule L V (V.map (MulAut.conj t).toMonoidHom) := by
  let a : V ≃* V := MulEquiv.toAdditive.symm e.toLinearEquiv.toAddEquiv
  let c := V.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective
  refine ⟨a.trans c, ?_⟩
  intro l v w hw
  have he := LinearMap.congr_fun (e.isIntertwining' l) (Additive.ofMul v)
  have hw' : doubledSeedAction L V hLV l (Additive.ofMul v) = Additive.ofMul w := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hw.symm
  change e (doubledSeedAction L V hLV l (Additive.ofMul v)) =
    doubledSeedAction L V hLV (doubledTwist L t htL l) (e (Additive.ofMul v)) at he
  rw [hw'] at he
  have hev := congrArg (fun x : Additive V => (x.toMul : G)) he
  change (a w : G) = (t⁻¹ * (l : G) * (t⁻¹)⁻¹) * (a v : G) *
    (t⁻¹ * (l : G) * (t⁻¹)⁻¹)⁻¹ at hev
  change t * (a w : G) * t⁻¹ = (l : G) * (t * (a v : G) * t⁻¹) * (l : G)⁻¹
  rw [hev]
  group

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

theorem sourceOrbit_normalizer_eq_of_markedDoubled
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled) :
    normalizer (D.sourceOrbit : Set G) = normalizer (L : Set G) := by
  obtain ⟨t, ht, hnt, he, _⟩ := hd.2.2
  rw [D.sourceOrbit_eq]
  exact D.doubledOrbit_normalizer_eq h he.symm

theorem sourceOrbit_reduced_of_markedDoubled
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled) :
    IsPReduced 2 (D.sourceOrbit.subgroupOf (normalizer (L : Set G))) := by
  obtain ⟨t, ht, hnt, he, _⟩ := hd.2.2
  rw [D.sourceOrbit_eq]
  exact D.doubledOrbit_reduced h he.symm

theorem sourceOrbit_hypothesisE61_of_markedDoubled
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled) :
    ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T
      (normalizer (L : Set G)) D.sourceOrbit := by
  let M := normalizer (L : Set G)
  have hn := D.sourceOrbit_normalizer_eq_of_markedDoubled h hd
  have hcore : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [D.sourceOrbit_eq]
    exact D.doubledOrbit_sylow_centralizer h
  have hjoin : L ⊔ (T : Subgroup G) ≤ M :=
    sup_le L.le_normalizer D.sylow_normalizes_component
  refine ⟨h.simpleQTKE, (D.doubledNormalizer_unique h).1,
    D.sylow_normalizes_component, D.sourceOrbit_weakClosure_setup.nontrivial,
    inferInstance, D.sourceOrbit_weakClosure_setup.le_sylow,
    normal_subgroupOf_of_le_normalizer D.sourceOrbit_weakClosure_setup.normalizes,
    ?_, ?_⟩
  · intro g hg
    exact Or.inr (mem_normalizer_iff_map_conj_eq.mp (hn.ge hg))
  · intro N hN hle
    apply (D.doubledNormalizer_unique h).2 N hN
    apply le_trans _ hle
    change L ⊔ (T : Subgroup G) ≤
      (M ⊓ normalizer (D.sourceOrbit : Set G)) ⊓ normalizer
        (((T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) : Subgroup G) : Set G)
    rw [hcore]
    refine le_inf (le_inf hjoin (hjoin.trans hn.ge)) ?_
    exact (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

omit [Finite G] in
/-- Multiplication coordinates for the literal orbit, with the original
conjugation action. The seed's elementary instance is supplied by D.elementary. -/
theorem sourceOrbit_doubled_coordinates [IsElementaryAbelian 2 V] (hd : D.MarkedDoubled) :
    ∃ t : G, ∃ ht : t ∈ (T : Subgroup G),
      t ∉ normalizer (V : Set G) ∧
      ∃ e : (Additive V × Additive V) ≃ₗ[ZMod 2] Additive D.sourceOrbit,
        (∀ v w, ((e (v,w)).toMul : G) =
          (v.toMul : G) * (t * (w.toMul : G) * t⁻¹)) ∧
        ∀ (l : L) p,
          e (doubledPairAction L V D.normalizes t (D.sylow_normalizes_component ht) l p) =
            doubledSeedAction L D.sourceOrbit D.sourceOrbit_component_normalizes l (e p) := by
  obtain ⟨t,ht,hnt,_,hW,hdj,_⟩ := hd.2.2
  obtain ⟨a,ha⟩ := exists_doubled_coordinates V D.sourceOrbit t
    (D.sourceOrbit_eq.trans hW) hdj
  exact ⟨t,ht,hnt,a,ha, doubled_coordinates_intertwine L V D.sourceOrbit D.normalizes
    D.sourceOrbit_component_normalizes t (D.sylow_normalizes_component ht) a ha⟩

omit [Finite G] in
/-- The inverse-conjugation twist is not equivalent to the original seed
for the unchanged actor L. The coordinates use this same conjugator. -/
theorem sourceOrbit_marked_doubled_coordinates [IsElementaryAbelian 2 V]
    (hd : D.MarkedDoubled) :
    ∃ t : G, ∃ ht : t ∈ (T : Subgroup G),
      t ∉ normalizer (V : Set G) ∧
      (¬ Nonempty ((doubledSeedAction L V D.normalizes).Equiv
        ((doubledSeedAction L V D.normalizes).comp
          (doubledTwist L t (D.sylow_normalizes_component ht)).toMonoidHom))) ∧
      ∃ e : (Additive V × Additive V) ≃ₗ[ZMod 2] Additive D.sourceOrbit,
        (∀ v w, ((e (v,w)).toMul : G) =
          (v.toMul : G) * (t * (w.toMul : G) * t⁻¹)) ∧
        ∀ (l : L) p,
          e (doubledPairAction L V D.normalizes t (D.sylow_normalizes_component ht) l p) =
            doubledSeedAction L D.sourceOrbit D.sourceOrbit_component_normalizes l (e p) := by
  obtain ⟨t,ht,hnt,_,hW,hdj,hne⟩ := hd.2.2
  obtain ⟨e,he⟩ := exists_doubled_coordinates V D.sourceOrbit t
    (D.sourceOrbit_eq.trans hW) hdj
  refine ⟨t,ht,hnt,?_,e,he, doubled_coordinates_intertwine L V D.sourceOrbit D.normalizes
    D.sourceOrbit_component_normalizes t (D.sylow_normalizes_component ht) e he⟩
  rintro ⟨a⟩
  exact hne (same_conjugation_of_twist_equiv L V D.normalizes t
    (D.sylow_normalizes_component ht) a)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
