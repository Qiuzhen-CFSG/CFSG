module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.SourceBorel.Inputs
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.Geometry

/-!
# Transport of cyclic coordinate actions to the original planes

Compatibility of the natural action transports each coordinate plane by the
wreath permutation. Thus the plane stabilizer S is normal in the actual T.
A trivial actor coordinate centralizes its plane; all commutators then lie
in the other plane. For a nonidentity cubic matrix, the displacement map
v ↦ v(a v)⁻¹ is onto the four-element plane, giving both commutator equalities.
These statements use the given coordinates throughout and never replace the
planes by arbitrary isomorphic four-groups.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the natural
plane decomposition on printed pp.1121--1122 and its use on p.1136.
-/

public section

open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel
variable {G : Type*} [Group G]

private theorem coordinate_plane_mem {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (i : OrthogonalPlaneIndex) (v : V) :
    (v : G) ∈ d.plane i ↔ d.coordinates v ∈ orthogonalCoordinatePlane i := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact (Subtype.ext he : w = v) ▸ hw
  · exact fun hv => ⟨v, hv, rfl⟩

/-- Conjugation permutes the original coordinate planes by the actual wreath shift. -/
theorem cyclic_plane_map [Finite G] {M V : Subgroup G} (d : NaturalOrthogonalAction M V)
    (m : M) (i : OrthogonalPlaneIndex) :
    (d.plane i).map (MulAut.conj (m : G)).toMonoidHom =
      d.plane ((d.actor m).right * i) := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := orthogonalAction
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨v, hv, rfl⟩
    let v₀ : V := ⟨v, d.plane_le i hv⟩
    let w := V.normalizerMonoidHom ⟨m, d.normalizes m.property⟩ v₀
    change (w : G) ∈ _
    rw [coordinate_plane_mem]
    change d.coordinates (V.normalizerMonoidHom ⟨m, d.normalizes m.property⟩ v₀) ∈ _
    rw [d.compatible]
    intro j hj
    change (d.actor m).left j • d.coordinates v₀ ((d.actor m).right⁻¹ * j) = 1
    rw [(coordinate_plane_mem d i v₀).mp hv _ ?_, smul_one]
    intro he
    apply hj
    exact (inv_mul_eq_iff_eq_mul.mp he)
  · rw [d.card_plane, card_map_of_injective (MulAut.conj (m : G)).injective, d.card_plane]

/-- The base subgroup is exactly the plane stabilizer, inside M. -/
theorem cyclic_mem_plane_normalizer_iff [Finite G] {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (m : M) (i : OrthogonalPlaneIndex) :
    (m : G) ∈ normalizer (d.plane i : Set G) ↔ (d.actor m).right = 1 := by
  constructor
  · exact RankTwo.plane_actor_shift_eq_one d m i
  · intro hm
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (d.plane i).map (MulAut.conj (m : G)).toMonoidHom = d.plane i
    rw [cyclic_plane_map, hm, one_mul]

/-- Every element of T preserves S, the kernel of its permutation action on the planes. -/
theorem cyclic_sylow_preserves_stabilizer [Finite G] (d : CharacteristicTwo.LocalData G)
    (t : G) (ht : t ∈ (d.T : Subgroup G)) :
    d.S.map (MulAut.conj t).toMonoidHom = d.S := by
  apply le_antisymm
  · rintro _ ⟨s, hs, rfl⟩
    have hst : t * s * t⁻¹ ∈ (d.T : Subgroup G) :=
      (d.T : Subgroup G).mul_mem ((d.T : Subgroup G).mul_mem ht hs.1)
        ((d.T : Subgroup G).inv_mem ht)
    refine ⟨hst, ?_⟩
    apply (cyclic_mem_plane_normalizer_iff d.action ⟨_, d.sylow_le hst⟩ 1).mpr
    have hs' := (cyclic_mem_plane_normalizer_iff d.action
      ⟨s, d.sylow_le hs.1⟩ 1).mp hs.2
    change (d.action.actor (⟨t, d.sylow_le ht⟩ * ⟨s, d.sylow_le hs.1⟩ *
      (⟨t, d.sylow_le ht⟩ : d.M)⁻¹)).right = 1
    rw [map_mul, map_mul, map_inv, RegularWreathProduct.mul_right,
      RegularWreathProduct.mul_right, RegularWreathProduct.inv_right, hs']
    simp
  · intro s hs
    refine ⟨t⁻¹ * s * t, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have hst : t⁻¹ * s * t ∈ (d.T : Subgroup G) :=
      (d.T : Subgroup G).mul_mem ((d.T : Subgroup G).mul_mem
        ((d.T : Subgroup G).inv_mem ht) hs.1) ht
    refine ⟨hst, ?_⟩
    apply (cyclic_mem_plane_normalizer_iff d.action ⟨_, d.sylow_le hst⟩ 1).mpr
    have hs' := (cyclic_mem_plane_normalizer_iff d.action
      ⟨s, d.sylow_le hs.1⟩ 1).mp hs.2
    change (d.action.actor ((⟨t, d.sylow_le ht⟩ : d.M)⁻¹ *
      ⟨s, d.sylow_le hs.1⟩ * ⟨t, d.sylow_le ht⟩)).right = 1
    rw [map_mul, map_mul, map_inv, RegularWreathProduct.mul_right,
      RegularWreathProduct.mul_right, RegularWreathProduct.inv_right, hs']
    simp

/-- A trivial coordinate of every actor centralizes the corresponding original plane. -/
theorem cyclic_centralizes_plane {M V A : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hAM : A ≤ M) (i : OrthogonalPlaneIndex)
    (hs : ∀ a : A, (d.actor (inclusion hAM a)).right = 1)
    (hi : ∀ a : A, (d.actor (inclusion hAM a)).left i = 1) :
    A ≤ centralizer (d.plane i : Set G) := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := orthogonalAction
  intro a ha v hv
  let v₀ : V := ⟨v, d.plane_le i hv⟩
  let a₀ : M := inclusion hAM ⟨a, ha⟩
  have he : d.actor a₀ • d.coordinates v₀ = d.coordinates v₀ := by
    funext j
    change (d.actor a₀).left j • d.coordinates v₀ ((d.actor a₀).right⁻¹ * j) = _
    rw [hs, inv_one, one_mul]
    by_cases hj : j = i
    · rw [hj, hi, one_smul]
    · rw [(coordinate_plane_mem d i v₀).mp hv j hj, smul_one]
  have he' := congrArg V.subtype (d.coordinates.injective ((d.compatible a₀ v₀).trans he))
  change a * v * a⁻¹ = v at he'
  exact (mul_inv_eq_iff_eq_mul.mp he').symm


private theorem other_index (i j k : OrthogonalPlaneIndex) (hij : i ≠ j) (hk : k ≠ j) :
    k = i := by
  have h : ∀ i j k : OrthogonalPlaneIndex, i ≠ j → k ≠ j → k = i := by decide +kernel
  exact h i j k hij hk

private theorem displacement_surjective (a : OrthogonalPlaneActor)
    (ha : a ^ 3 = 1) (hne : a ≠ 1) :
    letI := FourGroupMatrixCoordinates.naturalAction
    ∀ w : OrthogonalPlaneVector, ∃ v, v * (a • v)⁻¹ = w := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  have h : ∀ a : OrthogonalPlaneActor, a ^ 3 = 1 → a ≠ 1 →
      ∀ w : OrthogonalPlaneVector, ∃ v, v * (a • v)⁻¹ = w := by decide +kernel
  exact h a ha hne

/-- A nontrivial cubic actor fills its coordinate plane with commutators. -/
theorem cyclic_plane_le_commutator {M V A : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hAM : A ≤ M) (i : OrthogonalPlaneIndex)
    (a : A) (hs : (d.actor (inclusion hAM a)).right = 1)
    (hc : ((d.actor (inclusion hAM a)).left i) ^ 3 = 1)
    (hn : (d.actor (inclusion hAM a)).left i ≠ 1) :
    d.plane i ≤ ⁅d.plane i, A⁆ := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := orthogonalAction
  intro w hw
  let w₀ : V := ⟨w, d.plane_le i hw⟩
  let a₀ : M := inclusion hAM a
  obtain ⟨u, hu⟩ := displacement_surjective ((d.actor a₀).left i) hc hn (d.coordinates w₀ i)
  let v : V := d.coordinates.symm (fun k => if k = i then u else 1)
  have hv : (v : G) ∈ d.plane i := by
    apply (coordinate_plane_mem d i v).mpr
    intro k hk
    simp [v, hk]
  have he : v * (V.normalizerMonoidHom ⟨a₀, d.normalizes a₀.property⟩ v)⁻¹ = w₀ := by
    apply d.coordinates.injective
    simp only [map_mul, map_inv, d.compatible]
    funext k
    change d.coordinates v k *
      ((d.actor a₀).left k • d.coordinates v ((d.actor a₀).right⁻¹ * k))⁻¹ = _
    rw [hs, inv_one, one_mul]
    by_cases hk : k = i
    · subst k
      simpa [v] using hu
    · rw [(coordinate_plane_mem d i w₀).mp hw k hk]
      simp [v, hk]
  have he' : ⁅(v : G), (a : G)⁆ = w := by
    have hval := congrArg V.subtype he
    change (v : G) * ((a : G) * (v : G) * (a : G)⁻¹)⁻¹ = w at hval
    simpa [commutatorElement_def, mul_assoc] using hval
  rw [← he']
  exact commutator_mem_commutator hv a.property

/-- Fixing one coordinate forces all module commutators into the other plane. -/
theorem cyclic_commutator_le_plane {M V A : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hAM : A ≤ M) (i j : OrthogonalPlaneIndex)
    (hij : i ≠ j) (hs : ∀ a : A, (d.actor (inclusion hAM a)).right = 1)
    (hi : ∀ a : A, (d.actor (inclusion hAM a)).left i = 1) :
    ⁅V, A⁆ ≤ d.plane j := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := orthogonalAction
  apply commutator_le.mpr
  intro v hv a ha
  let v₀ : V := ⟨v, hv⟩
  let a₀ : M := inclusion hAM ⟨a, ha⟩
  let w : V := v₀ * (V.normalizerMonoidHom ⟨a₀, d.normalizes a₀.property⟩ v₀)⁻¹
  have hw : (w : G) ∈ d.plane j := by
    apply (coordinate_plane_mem d j w).mpr
    intro k hk
    rw [other_index i j k hij hk]
    change d.coordinates (v₀ * (V.normalizerMonoidHom
      ⟨a₀, d.normalizes a₀.property⟩ v₀)⁻¹) i = 1
    simp only [map_mul, map_inv, d.compatible, Pi.mul_apply, Pi.inv_apply]
    change d.coordinates v₀ i *
      ((d.actor a₀).left i • d.coordinates v₀ ((d.actor a₀).right⁻¹ * i))⁻¹ = 1
    rw [hs, hi, inv_one, one_mul, one_smul, mul_inv_cancel]
  have he : (w : G) = ⁅v, a⁆ := by
    change v * (a * v * a⁻¹)⁻¹ = ⁅v, a⁆
    simp [commutatorElement_def, mul_assoc]
  exact he ▸ hw

/-- Nontrivial action supported on one coordinate moves that entire plane. -/
theorem cyclic_commutator_eq_plane {M V A : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hAM : A ≤ M) (i j : OrthogonalPlaneIndex)
    (hij : i ≠ j) (hs : ∀ a : A, (d.actor (inclusion hAM a)).right = 1)
    (hc : ∀ a : A, ((d.actor (inclusion hAM a)).left j) ^ 3 = 1)
    (hi : ∀ a : A, (d.actor (inclusion hAM a)).left i = 1)
    (hn : ⁅V, A⁆ ≠ ⊥) : ⁅V, A⁆ = d.plane j ∧ ⁅d.plane j, A⁆ = d.plane j := by
  classical
  have hex : ∃ a : A, (d.actor (inclusion hAM a)).left j ≠ 1 := by
    by_contra! h
    have hAV : A ≤ centralizer (V : Set G) := by
      intro a ha
      have he : d.actor (inclusion hAM ⟨a, ha⟩) = 1 := by
        apply RegularWreathProduct.ext _ (hs _)
        funext k
        change (d.actor (inclusion hAM ⟨a, ha⟩)).left k = 1
        by_cases hk : k = j
        · simpa only [hk] using h ⟨a, ha⟩
        · simpa only [other_index i j k hij hk] using hi ⟨a, ha⟩
      have hm : inclusion hAM ⟨a, ha⟩ ∈ d.actor.ker := he
      rw [d.ker_actor] at hm
      exact hm
    apply hn
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
    exact hAV
  obtain ⟨a, ha⟩ := hex
  have hlo := cyclic_plane_le_commutator d hAM j a (hs a) (hc a) ha
  have hhi := cyclic_commutator_le_plane d hAM i j hij hs hi
  have he : ⁅V, A⁆ = d.plane j :=
    le_antisymm hhi (hlo.trans (commutator_mono (d.plane_le j) le_rfl))
  exact ⟨he, le_antisymm ((commutator_mono (d.plane_le j) le_rfl).trans hhi) hlo⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel
