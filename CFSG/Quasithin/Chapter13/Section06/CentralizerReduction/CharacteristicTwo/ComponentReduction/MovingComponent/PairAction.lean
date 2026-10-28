module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.SourceReduction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.CubicAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.OmegaGeometry.Factors
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The paired coordinates in the actual ambient Borel interface

The product coordinates on the relative orbit in Gᵥ are transported through
its literal embedding in G. Both factor embeddings and their Tᵥ permutation
are identified with `SuzukiPair.PairFactors`. The same quotient coordinates
carry the first component's normalizer action on every element of the orbit:
write an element as a product from the two components and conjugate both.

Thus the cubic action constructed on K gives precisely the first-coordinate
field-action identity used by the paired Borel contradiction. No Borel
alignment or field-action compatibility is assumed. Normality of the full
component orbit and O(Gᵥ) = 1 also make its retained center a two-group;
its center is never assumed trivial.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.6.6, printed p.927, the moving Suzuki pair and its cubic field action.
The matrix parameter n has source field degree 2*n+1, including n=1.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
variable {H S : Type*} [Group H] [Group S] {K U : Subgroup H}
  {eK : NormalizerAction.componentImage K ≃* S}

noncomputable def PairCoordinates.quotientMap (c : PairCoordinates K U eK) :
    componentOrbit K U →* S × S :=
  c.equiv.toMonoidHom.comp (QuotientGroup.mk' (center (componentOrbit K U)))

theorem PairCoordinates.quotientMap_factors (c : PairCoordinates K U eK) (k l : K) :
    c.quotientMap (firstFactor K U k * secondFactor K U c.moving l) =
      (factorModel K eK k, factorModel K eK l) := c.factors k l

theorem PairCoordinates.exists_factors (c : PairCoordinates K U eK)
    (hK : IsComponent H K) (x : componentOrbit K U) :
    ∃ k l : K, x = firstFactor K U k * secondFactor K U c.moving l := by
  have hc : ⁅K, K.conjBy c.moving⁆ = ⊥ :=
    hK.commutator_eq_bot_of_ne (hK.map_conj c.moving)
      (fun he => c.moved (mem_normalizer_iff_map_conj_eq.mpr he.symm))
  have hJN : K.conjBy c.moving ≤ normalizer (K : Set H) :=
    (commutator_eq_bot_iff_le_centralizer.mp
      ((commutator_comm _ _).trans hc)).trans (Subgroup.centralizer_le_normalizer _)
  have hx : (x : H) ∈ K ⊔ K.conjBy c.moving := c.orbit_eq.le x.property
  rw [← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left K (K.conjBy c.moving) hJN] at hx
  obtain ⟨k, hk, j, hj, he⟩ := hx
  obtain ⟨l, hl, rfl⟩ := hj
  exact ⟨⟨k, hk⟩, ⟨l, hl⟩, Subtype.ext he.symm⟩

theorem moving_orbit_normal (K U : Subgroup H)
    (hi : (normalizer (K : Set H)).index = 2)
    (hm : ¬ U ≤ normalizer (K : Set H)) : (componentOrbit K U).Normal := by
  rw [moving_orbit_eq_full K U hi hm]
  apply normalizer_eq_top_iff.mp
  exact top_unique (le_normalizer_componentOrbit K ⊤)

/-- The retained central kernel is a two-group because O(H) is trivial.
No assertion that the center is trivial, including at Sz(8), is used. -/
theorem moving_orbit_center_two [Finite H] (K U : Subgroup H)
    (hodd : pPrimeCore 2 H = ⊥)
    (hi : (normalizer (K : Set H)).index = 2)
    (hm : ¬ U ≤ normalizer (K : Set H)) :
    IsPGroup 2 (center (componentOrbit K U)) := by
  let := moving_orbit_normal K U hi hm
  have hsub : (componentOrbit K U).IsSubnormal := (inferInstance : (componentOrbit K U).Normal).isSubnormal
  have ho := hsub.pPrimeCore_eq_bot hodd (componentOrbit K U)
  exact isPGroup_of_nilpotent_normal (center (componentOrbit K U))
    inferInstance inferInstance ho

/-- The first product coordinate carries precisely the literal action on K. -/
theorem PairCoordinates.first_action (c : PairCoordinates K U eK)
    (hK : IsComponent H K) (hi : (normalizer (K : Set H)).index = 2)
    (D : Subgroup H) (hn : D ≤ normalizer (K : Set H)) (d : D)
    (hd : (d : H) ∈ normalizer (componentOrbit K U : Set H))
    (x : componentOrbit K U) :
    (c.quotientMap ((componentOrbit K U).normalizerMonoidHom ⟨d, hd⟩ x)).1 =
      modelAction K D hn eK d (c.quotientMap x).1 := by
  obtain ⟨k, l, rfl⟩ := c.exists_factors hK x
  let t : H := c.moving
  have htd : t⁻¹ * (d : H) * t ∈ normalizer (K : Set H) := by
    simpa only [inv_inv] using
      (normal_of_index_eq_two hi).conj_mem (d : H) (hn d.property) t⁻¹
  let k' : K := K.normalizerMonoidHom (inclusion hn d) k
  let l' : K := K.normalizerMonoidHom ⟨t⁻¹ * d * t, htd⟩ l
  have he : (componentOrbit K U).normalizerMonoidHom ⟨d, hd⟩
      (firstFactor K U k * secondFactor K U c.moving l) =
      firstFactor K U k' * secondFactor K U c.moving l' := by
    apply Subtype.ext
    change (d : H) * ((k : H) * (t * l * t⁻¹)) * (d : H)⁻¹ =
      ((d : H) * k * (d : H)⁻¹) *
        (t * ((t⁻¹ * d * t) * l * (t⁻¹ * d * t)⁻¹) * t⁻¹)
    group
  rw [he, c.quotientMap_factors, c.quotientMap_factors]
  exact (modelAction_apply K D hn eK d k).symm

variable {G : Type*} [Group G]

/-- Identify the relative component orbit with the literal ambient orbit used
by the paired-Suzuki Borel argument. -/
theorem ambientOrbit_eq (T : Subgroup G) (v : G) (K : Subgroup (Gv v)) :
    (componentOrbit K (localT T v)).map (Gv v).subtype =
      SuzukiPair.orbit T (K.map (Gv v).subtype) v := by
  change (⨆ t : localT T v, K.map (MulAut.conj (t : Gv v)).toMonoidHom).map _ = _
  rw [← conjugateSpanBy_eq_iSup_conj, map_conjugateSpanBy]
  change conjugateSpanBy _ ((T.subgroupOf (Gv v)).map (Gv v).subtype) = _
  rw [subgroupOf_map_subtype]
  rfl

noncomputable def ambientOrbitEquiv (T : Subgroup G) (v : G) (K : Subgroup (Gv v)) :
    componentOrbit K (localT T v) ≃* SuzukiPair.orbit T (K.map (Gv v).subtype) v :=
  ((componentOrbit K (localT T v)).equivMapOfInjective
    (Gv v).subtype (Gv v).subtype_injective).trans
      (MulEquiv.subgroupCongr (ambientOrbit_eq T v K))

theorem ambientOrbitEquiv_apply (T : Subgroup G) (v : G) (K : Subgroup (Gv v))
    (x : componentOrbit K (localT T v)) :
    (ambientOrbitEquiv T v K x : G) = (x : Gv v) := rfl

open BenderSuzuki.MatrixGroups
variable {T : Subgroup G} {v : G} {K : Subgroup (Gv v)} {n : ℕ}
  {eK : NormalizerAction.componentImage K ≃* SuzukiMatrixGroup n}

noncomputable def PairCoordinates.ambientMarking
    (c : PairCoordinates K (localT T v) eK) (hn : 1 ≤ n) :
    SuzukiPair.Marking T (K.map (Gv v).subtype) v where
  parameter := n
  positive := hn
  equiv := (quotientCenterCongr (ambientOrbitEquiv T v K).symm).trans c.equiv

theorem PairCoordinates.ambientMarking_quotientMap
    (c : PairCoordinates K (localT T v) eK) (hn : 1 ≤ n)
    (x : componentOrbit K (localT T v)) :
    (c.ambientMarking hn).quotientMap (ambientOrbitEquiv T v K x) = c.quotientMap x := by
  change c.equiv (quotientCenterCongr (ambientOrbitEquiv T v K).symm
    (QuotientGroup.mk' _ (ambientOrbitEquiv T v K x))) = _
  rw [quotientCenterCongr_mk, MulEquiv.symm_apply_apply]
  rfl

theorem ambientOrbit_normalizes {x : Gv v}
    (hx : x ∈ normalizer (componentOrbit K (localT T v) : Set (Gv v))) :
    (x : G) ∈ normalizer (SuzukiPair.orbit T (K.map (Gv v).subtype) v : Set G) := by
  rw [← ambientOrbit_eq T v K]
  exact (componentOrbit K (localT T v)).le_normalizer_map (Gv v).subtype
    (mem_map_of_mem _ hx)

/-- Transport the same cubic action to the literal first-coordinate action
consumed by SuzukiPair.cubic_field_contradiction. -/
theorem PairCoordinates.ambientMarking_first_action
    (c : PairCoordinates K (localT T v) eK) (hn : 1 ≤ n)
    (hK : IsComponent (Gv v) K) (hi : (X K).index = 2)
    (D : Subgroup (Gv v)) (hD : D ≤ X K) (d : D)
    (hd : (d : Gv v) ∈ normalizer (componentOrbit K (localT T v) : Set (Gv v)))
    (x : SuzukiPair.orbit T (K.map (Gv v).subtype) v) :
    ((c.ambientMarking hn).quotientMap
      ((SuzukiPair.orbit T (K.map (Gv v).subtype) v).normalizerMonoidHom
        ⟨((d : Gv v) : G), ambientOrbit_normalizes hd⟩ x)).1 =
      modelAction K D hD eK d ((c.ambientMarking hn).quotientMap x).1 := by
  obtain ⟨y, rfl⟩ := (ambientOrbitEquiv T v K).surjective x
  have he : (SuzukiPair.orbit T (K.map (Gv v).subtype) v).normalizerMonoidHom
      ⟨((d : Gv v) : G), ambientOrbit_normalizes hd⟩ (ambientOrbitEquiv T v K y) =
      ambientOrbitEquiv T v K
        ((componentOrbit K (localT T v)).normalizerMonoidHom ⟨d, hd⟩ y) := by
    apply Subtype.ext
    rfl
  rw [he, c.ambientMarking_quotientMap, c.ambientMarking_quotientMap]
  exact c.first_action hK hi D hD d hd y

private theorem map_conj_ambient (A : Subgroup (Gv v)) (x : Gv v) :
    (A.conjBy x).map (Gv v).subtype =
      (A.map (Gv v).subtype).conjBy (x : G) := by
  rw [conjBy, conjBy, map_map, map_map]
  rfl

noncomputable def ambientFactorEquiv (K : Subgroup (Gv v))
    (eK : NormalizerAction.componentImage K ≃* SuzukiMatrixGroup n) :
    (K.map (Gv v).subtype ⧸ center (K.map (Gv v).subtype)) ≃* SuzukiMatrixGroup n :=
  (quotientCenterCongr (K.equivMapOfInjective (Gv v).subtype
    (Gv v).subtype_injective).symm).trans
      ((NormalizerAction.componentCentralQuotientEquiv K).trans eK)

/-- Both literal ambient factor embeddings and their Tᵥ permutation, on the
same coordinates as the cubic field action. -/
theorem PairCoordinates.nonempty_ambientFactors
    (c : PairCoordinates K (localT T v) eK) (hn : 1 ≤ n) :
    Nonempty (SuzukiPair.PairFactors (c.ambientMarking hn)) := by
  let t : Tv T v := ⟨((c.moving : Gv v) : G), c.moving.property, (c.moving : Gv v).property⟩
  let f := (Gv v).subtype
  let kEquiv := K.equivMapOfInjective f (Gv v).subtype_injective
  refine ⟨{ moving := t
            moved := ?_
            orbit_eq := ?_
            permutation := ?_
            firstEquiv := ambientFactorEquiv K eK
            secondEquiv := ambientFactorEquiv K eK
            first_eq := ?_
            second_eq := ?_ }⟩
  · intro ht
    apply c.moved
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply map_injective (Gv v).subtype_injective
    change (K.conjBy (c.moving : Gv v)).map (Gv v).subtype = _
    rw [map_conj_ambient]
    exact mem_normalizer_iff_map_conj_eq.mp ht
  · rw [← ambientOrbit_eq T v K, c.orbit_eq, Subgroup.map_sup, map_conj_ambient]
    rfl
  · intro u
    let u' : localT T v := ⟨⟨u, u.property.2⟩, u.property.1⟩
    rcases c.permutation u' with h | h
    · left
      have h1 := congrArg (Subgroup.map (Gv v).subtype) h.1
      have h2 := congrArg (Subgroup.map (Gv v).subtype) h.2
      simp only [map_conj_ambient] at h1 h2
      exact ⟨by simpa only [conjBy] using h1, by simpa only [conjBy] using h2⟩
    · right
      have h1 := congrArg (Subgroup.map (Gv v).subtype) h.1
      have h2 := congrArg (Subgroup.map (Gv v).subtype) h.2
      simp only [map_conj_ambient] at h1 h2
      exact ⟨by simpa only [conjBy] using h1, by simpa only [conjBy] using h2⟩
  · intro k
    obtain ⟨k, rfl⟩ := kEquiv.surjective k
    have he : SuzukiPair.firstEmbedding T (K.map f) v (kEquiv k) =
        ambientOrbitEquiv T v K (firstFactor K (localT T v) k) := rfl
    rw [he, c.ambientMarking_quotientMap]
    have hf := c.quotientMap_factors k 1
    simp only [map_one, mul_one] at hf
    change c.quotientMap _ =
      (eK (NormalizerAction.componentCentralQuotientEquiv K
        (quotientCenterCongr kEquiv.symm (QuotientGroup.mk' _ (kEquiv k)))), 1)
    rw [quotientCenterCongr_mk, MulEquiv.symm_apply_apply]
    exact hf
  · intro k
    obtain ⟨k, rfl⟩ := kEquiv.surjective k
    have he : SuzukiPair.secondEmbedding T (K.map f) v t (kEquiv k) =
        ambientOrbitEquiv T v K (secondFactor K (localT T v) c.moving k) := rfl
    rw [he, c.ambientMarking_quotientMap]
    have hf := c.quotientMap_factors 1 k
    simp only [map_one, one_mul] at hf
    change c.quotientMap _ =
      (1, eK (NormalizerAction.componentCentralQuotientEquiv K
        (quotientCenterCongr kEquiv.symm (QuotientGroup.mk' _ (kEquiv k)))))
    rw [quotientCenterCongr_mk, MulEquiv.symm_apply_apply]
    exact hf

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
