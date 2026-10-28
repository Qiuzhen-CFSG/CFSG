module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.Unmarked

/-!
# Transport for the prime-five family calculation

The residual supplement is transported as an embedded solvable residual joined
with the actual Sylow subgroup. Its radical quotient is transported by the
induced quotient isomorphism. In particular the actor image, its order, and
its containment in the derived subgroup are preserved, without choosing a
permutation marking or replacing the actor by its inner intersection.

Source: Aschbacher--Smith E.1.5, E.1.8, E.1.10 and E.1.14(7), pp.210--214.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy
open PSUThreeGeneration
variable {G H : Type*} [Group G] [Group H]

/-- The intrinsic quotient position of an actual actor. -/
@[expose] def QuotientActor (K A : Subgroup G) : Prop :=
  Nat.card ((A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))) = 4 ∧
    ¬ (A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K)) ≤
      _root_.commutator (K ⧸ solvableRadical K)

/-- Isomorphisms preserve the centralizer of the specified element. -/
theorem map_elementCentralizer (e : G ≃* H) (z : G) :
    (centralizer ({z} : Set G)).map (e : G →* H) = centralizer ({e z} : Set H) := by
  apply le_antisymm
  · simpa using
      map_centralizer_le_centralizer_image ({z} : Set G) (e : G →* H)
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hy

variable [Finite G]

/-- The embedded solvable residual is functorial for an ambient isomorphism. -/
private theorem map_embeddedResidual (e : G ≃* H) (K : Subgroup G) :
    ((solvableResidual K).map K.subtype).map (e : G →* H) =
      (solvableResidual (K.map (e : G →* H))).map (K.map (e : G →* H)).subtype := by
  rw [← map_solvableResidual_eq (e.subgroupMap K).toMonoidHom (e.subgroupMap K).surjective,
    map_map, map_map]
  rfl

/-- Both terms of the literal centralizer residual supplement are preserved. -/
theorem map_residualOvergroup (e : G ≃* H) (T : Sylow 2 G) (z : G) :
    (centralizerResidualOvergroup T z).map (e : G →* H) =
      centralizerResidualOvergroup (T.mapSurjective (f := (e : G →* H)) (by simpa using e.surjective)) (e z) := by
  unfold centralizerResidualOvergroup
  rw [Subgroup.map_sup, map_embeddedResidual, map_elementCentralizer]
  rfl

variable [Finite H]

/-- Quotient actors transport with their literal restriction and quotient maps. -/
theorem QuotientActor.map (e : G ≃* H) {K A : Subgroup G} (h : QuotientActor K A) :
    QuotientActor (K.map (e : G →* H)) (A.map (e : G →* H)) := by
  let k := K.equivMapOfInjective (e : G →* H) e.injective
  let q := QuotientGroup.congr (solvableRadical K) (solvableRadical (K.map (e : G →* H)))
    k (map_solvableRadical_equiv k)
  have hi : ((A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))).map q.toMonoidHom =
      ((A.map (e : G →* H)).subgroupOf (K.map (e : G →* H))).map
        (QuotientGroup.mk' (solvableRadical (K.map (e : G →* H)))) := by
    rw [← intrinsic_subgroupOf_map (e : G →* H) e.injective A K, map_map, map_map]
    rfl
  have hd : (_root_.commutator (K ⧸ solvableRadical K)).map q.toMonoidHom =
      _root_.commutator ((K.map (e : G →* H)) ⧸ solvableRadical (K.map (e : G →* H))) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr
      (show Function.Surjective q.toMonoidHom by simpa using q.surjective)]
    rfl
  constructor
  · rw [← hi, card_map_of_injective (f := q.toMonoidHom) (by simpa using q.injective)]
    exact h.1
  · intro hle
    apply h.2
    rw [← hi, ← hd] at hle
    exact (map_le_map_iff_of_injective (f := q.toMonoidHom) (by simpa using q.injective)).mp hle

/-- The same quotient equivalence transports a separately constructed model. -/
theorem residualQuotientModel_map (e : G ≃* H) (T : Sylow 2 G) (z : G)
    {Q : Type*} [Group Q]
    (h : Nonempty ((centralizerResidualOvergroup T z ⧸
      solvableRadical (centralizerResidualOvergroup T z)) ≃* Q)) :
    Nonempty ((centralizerResidualOvergroup (T.mapSurjective (f := (e : G →* H)) (by simpa using e.surjective)) (e z) ⧸
      solvableRadical (centralizerResidualOvergroup (T.mapSurjective (f := (e : G →* H)) (by simpa using e.surjective)) (e z))) ≃* Q) := by
  let K := centralizerResidualOvergroup T z
  let k := (e.subgroupMap K).trans (MulEquiv.subgroupCongr (map_residualOvergroup e T z))
  let q := QuotientGroup.congr _ _ k (map_solvableRadical_equiv k)
  obtain ⟨a⟩ := h
  exact ⟨q.symm.trans a⟩

section Fields
open Matrix.PSL3.OddPrimeGraphExtension
variable {F E : Type*} [Field F] [Finite F] [Field E] [Finite E]

/-- Transport both alternatives, including the same original family and
its weak-closure normalizer, along an actual graph-extension isomorphism. -/
theorem unmarked_map_equiv (e : graphExtension F ≃* graphExtension E)
    (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension E)))
    (z : graphExtension F)
    (h : UnmarkedFiveGeometryAt F T {A | A.map (e : graphExtension F →* graphExtension E) ∈ Ω} z) :
    UnmarkedFiveGeometryAt E (T.mapSurjective (f := (e : graphExtension F →* graphExtension E)) (by simpa using e.surjective)) Ω (e z) := by
  rcases h with ⟨H, hTH, hs, hj⟩ | ⟨B, hB, hBT, hc, hout⟩
  · let _ := hs
    have hw := map_weakClosure_equiv e (T : Subgroup _) Ω
    simp only [MulEquiv.toMonoidHom_eq_coe] at hw
    have hn := (weakClosure (T : Subgroup _) {A | A.map (e : graphExtension F →* graphExtension E) ∈ Ω}).map_normalizer_eq_of_bijective
      (f := (e : graphExtension F →* graphExtension E)) e.bijective
    rw [hw] at hn
    refine Or.inl ⟨H.map (e : graphExtension F →* graphExtension E), map_mono hTH,
      Group.isSolvable_of_surjective ((e : graphExtension F →* graphExtension E).subgroupMap_surjective H), ?_⟩
    change H.map (e : graphExtension F →* graphExtension E) ⊔ normalizer (weakClosure ((T : Subgroup _).map (e : graphExtension F →* graphExtension E)) Ω : Set _) = ⊤
    rw [← hn, ← Subgroup.map_sup, hj, map_top_of_surjective _ e.surjective]
  · have ha := QuotientActor.map e
      (show QuotientActor (centralizerResidualOvergroup T z) B from ⟨hc, hout⟩)
    rw [map_residualOvergroup] at ha
    exact Or.inr ⟨B.map (e : graphExtension F →* graphExtension E), hB, map_mono hBT, ha⟩

end Fields
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy
