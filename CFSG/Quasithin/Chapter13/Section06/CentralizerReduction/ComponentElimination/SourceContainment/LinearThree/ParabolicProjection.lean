module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.Projection
public import Theory.SpecificGroups.PSL3Two.Parabolics.ResidualCommutator
public import Theory.GroupTheory.SylowKernelCore

/-!
# The actual Sylow marking of the projected residual

The source Sylow in KTᵥ restricts to Tᵥ ∩ K, since 13.6.14 makes K
normal in KTᵥ. Its literal plus image is consequently Sylow in K⁺.
Projection equivariance makes that image normalize the projected Lᵥ.
Transport through the given K⁺ ≃ PSL₃(2) identifies the normalizer as an
order-twenty-four parabolic, the projected subgroup as its two-residual,
and proves generation by commutators with the image of Tᵥ ∩ K.

This is a construction from the noncentral projection, not an assumed
parabolic marking or image equality. Ambient normalization of K by Lᵥ
is still required by the containment lift in `NoncentralLift`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the final
paragraph of the proof of 13.6.20, printed p.931.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree
open ComponentSelection
variable {G : Type*} [Group G] [Finite G]

/-- The literal plus map on K, with codomain restricted to its image. -/
def componentPlusMap (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    K →* plusImage K L T z v hL hz K :=
  ((plusMk K L T z v hL hz).comp (inclusion (K_le_plusActor K L T v))).codRestrict _
    (fun k => ⟨inclusion (K_le_plusActor K L T v) k, k.property, rfl⟩)

omit [Finite G] in
theorem componentPlusMap_surjective (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    Function.Surjective (componentPlusMap K L T z v hL hz) := by
  rintro ⟨_, a, ha, rfl⟩
  exact ⟨⟨a, ha⟩, rfl⟩

/-- The image of the original intersection T_v ∩ K in the component. -/
def componentSylowMap (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    ↥(Tv T v ⊓ K) →* plusImage K L T z v hL hz K :=
  (componentPlusMap K L T z v hL hz).comp (inclusion inf_le_right)

theorem exists_componentSylow (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G)) :
    ∃ S : Sylow 2 (plusImage K L T z v hL hz K),
      (S : Subgroup (plusImage K L T z v hL hz K)) = (componentSylowMap K L T z v hL hz).range := by
  obtain ⟨Q, hQ⟩ := hK.1.2.2.1
  obtain ⟨P, hP⟩ := Q.exists_map_subtype_eq_inf_of_normalizes
    (show K ≤ K ⊔ Tv T v from le_sup_left) (sup_le K.le_normalizer hn)
  have hP' : (P : Subgroup K) = (Tv T v).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hP, hQ, subgroupOf_map_subtype]
  refine ⟨P.mapSurjective (componentPlusMap_surjective K L T z v hL hz), ?_⟩
  change (P : Subgroup K).map (componentPlusMap K L T z v hL hz) = _
  rw [hP']
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk, k.property⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨⟨s, s.property.2⟩, s.property.1, rfl⟩

omit [Finite G] in
/-- The image of the component intersection acts on the constructed projection. -/
theorem componentSylow_normalizes_projection (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* Matrix.PSL3Two.PSL)
    (f : Lv L v →* plusImage K L T z v hL hz K)
    (hf : ∀ (l : Lv L v) (k : plusImage K L T z v hL hz K),
      (f l : Gplus K L T z v hL hz) * k * (f l : Gplus K L T z v hL hz)⁻¹ =
        residualPlusMap K L T z v hL hz l * k *
          (residualPlusMap K L T z v hL hz l)⁻¹) :
    (componentSylowMap K L T z v hL hz).range ≤ normalizer (f.range : Set (plusImage K L T z v hL hz K)) := by
  rintro _ ⟨s, rfl⟩
  have ha := projection_range_normalized K L T z v hL hz hK hn e f hf
  have hs : (componentSylowMap K L T z v hL hz s : Gplus K L T z v hL hz) ∈
      plusImage K L T z v hL hz (Tv T v) :=
    ⟨⟨s, (show Tv T v ≤ plusActor K L T v from le_sup_right) s.property.1⟩, s.property.1, rfl⟩
  have hh := le_normalizer_comap (H := f.range.map
      (plusImage K L T z v hL hz K).subtype)
    (plusImage K L T z v hL hz K).subtype
    (show componentSylowMap K L T z v hL hz s ∈
      (normalizer (f.range.map (plusImage K L T z v hL hz K).subtype : Set _)).comap
        (plusImage K L T z v hL hz K).subtype from ha hs)
  rwa [comap_map_eq_self_of_injective (plusImage K L T z v hL hz K).subtype_injective] at hh

/-- Recognition on the actual component, including the required commutator equality. -/
theorem projection_parabolic_and_commutator (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* Matrix.PSL3Two.PSL)
    (f : Lv L v →* plusImage K L T z v hL hz K)
    (hf : ∀ (l : Lv L v) (k : plusImage K L T z v hL hz K),
      (f l : Gplus K L T z v hL hz) * k * (f l : Gplus K L T z v hL hz)⁻¹ =
        residualPlusMap K L T z v hL hz l * k *
          (residualPlusMap K L T z v hL hz l)⁻¹)
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hne : f.range ≠ ⊥) :
    IsCoatom (normalizer (f.range : Set (plusImage K L T z v hL hz K))) ∧
      Nat.card (normalizer (f.range : Set (plusImage K L T z v hL hz K))) = 24 ∧
      f.range = (pResidual 2 (normalizer (f.range : Set (plusImage K L T z v hL hz K)))).map
        (normalizer (f.range : Set (plusImage K L T z v hL hz K))).subtype ∧
      ⁅f.range, (componentSylowMap K L T z v hL hz).range⁆ = f.range := by
  let E := e.trans Matrix.PSL3Two.equiv.symm
  let A := f.range.map E.toMonoidHom
  obtain ⟨S, hS⟩ := exists_componentSylow K L T z v hL hz hK hn
  let R := S.mapSurjective (f := E.toMonoidHom) E.surjective
  have hnS : (S : Subgroup (plusImage K L T z v hL hz K)) ≤ normalizer (f.range : Set (plusImage K L T z v hL hz K)) := by
    rw [hS]
    exact componentSylow_normalizes_projection K L T z v hL hz hK hn e f hf
  have hnR : (R : Subgroup Matrix.PSL3Two.SL) ≤ normalizer (A : Set Matrix.PSL3Two.SL) :=
    (map_mono (f := E.toMonoidHom) hnS).trans (le_normalizer_map _)
  let F := E.subgroupMap f.range
  have hpA : IsPPerfect 2 A := (projection_range_twoPerfect K L T z v hL hz f).of_surjective
    F.toMonoidHom F.surjective
  let q := QuotientGroup.congr (pCore 2 f.range) (pCore 2 A) F (pCore_map_iso 2 F)
  have hcA : Nat.card (A ⧸ pCore 2 A) = 3 :=
    (Nat.card_congr q.toEquiv).symm.trans (residual_image_core_quotient_card L v hc f hne)
  obtain ⟨hmax, hcard, _, hres, _⟩ := Matrix.PSL3Two.ResidualRecognition.recognize A R hpA hcA hnR
  have hnormalizer : (normalizer (f.range : Set (plusImage K L T z v hL hz K))).map E.toMonoidHom =
      normalizer (A : Set Matrix.PSL3Two.SL) := map_equiv_normalizer_eq f.range E
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (E.mapSubgroup.isCoatom_iff _).mp
    change IsCoatom ((normalizer (f.range : Set _)).map E.toMonoidHom)
    rwa [hnormalizer]
  · exact (Nat.card_congr (E.subgroupMap (normalizer (f.range : Set (plusImage K L T z v hL hz K)))).toEquiv).trans
      (hnormalizer.symm ▸ hcard)
  · apply map_injective (f := E.toMonoidHom) E.injective
    rw [map_embedded_pResidual, hnormalizer]
    exact hres
  · apply map_injective (f := E.toMonoidHom) E.injective
    rw [map_commutator, ← hS]
    exact Matrix.PSL3Two.ResidualRecognition.commutator_sylow_eq A R hpA hcA hnR

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree
