module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus


/-!
# Uniform Borel centralizers on the genuine triality Sylow center

The imported `RadicalCoordinates.Centers.embedded_center_unipotent` identifies
both inclusions of the full embedded unipotent center with the highest-root
subgroup in the genuine graph-field carrier. Its parametrization is faithful
through the elementary subgroup and its actual central quotient.

The highest-root coroot pairings are (0,1,0,0). Thus the split torus acts on
its parameter by the central coroot coordinate. In the graph-field fixed
torus this is the base-field unit; the independent cubic-field unit acts
trivially. The positive factor centralizes the highest root, so every Borel
element acts by one nonzero base-field scalar. Fixing any nonzero parameter
forces that scalar to be one, giving B ∩ C(r) = B ∩ C(Z(U)).

All statements hold in characteristic two, including q = 2, and hence in
`Standard.BinaryCarrier n hn` throughout the source range n > 1. The root
subgroups and Borel are the actual descended Geck subgroups. Conjugation is
on the left, with the existing n(t)n(-1) convention for coroot words.

Sources: Aschbacher–Smith, proof of 13.6.6, printed p.927
(`refs/quasithin.pdf`); GLS3 2.4.7 and §2.6
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

noncomputable section
open scoped Pointwise
namespace Triality.Standard.NormalizedRootCentralizers
open Parabolics ConcreteBruhat PositiveCoordinates RadicalCoordinates.Centers
open Theory.AlgebraicGroup.StandardRootSystem
open Parabolics.RankOneMatrices PositiveCoordinates.SumExchangeData

private theorem highest_pairing (i : Fin 4) :
    (typeDRootPairing 2).pairingIn ℤ (rootIndex 11) (typeDSimpleRootIndex 2 i) =
      (![0, 1, 0, 0] : Fin 4 → ℤ) i := by
  have hd : (∑ k : Fin 4, rootCoords (simpleIndex i) k *
      rootCoords (positiveIndex 11) k) = (![0, 1, 0, 0] : Fin 4 → ℤ) i := by
    revert i
    decide +kernel
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ) _ = ((![0, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
  rw [RootPairing.algebraMap_pairingIn, typeDRootPairing_pairing,
    ← rootEnumeration_positiveIndex, ← rootEnumeration_simpleIndex]
  change (∑ k : Fin 4, _ * _) = _
  simp only [← typeDRootPairing_root_val, rootCoords_spec]
  simpa only [Int.cast_sum, Int.cast_mul] using congrArg (fun z : ℤ => (z : ℝ)) hd

private theorem conjugate_product {G : Type*} [Group G] (g h x : G) :
    (g * h) * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ := by group

/-- Only the central coroot coordinate acts on the highest root. -/
theorem product_conjugate_highest (P : Parameters) (hp : P.prime = 2)
    (a : TorusCoordinates.Coordinates P) (t : ExtensionField P) :
    TorusCoordinates.product P a * curve P 11 t * (TorusCoordinates.product P a)⁻¹ =
      curve P 11 ((a 1).val * t) := by
  simp only [TorusCoordinates.product, conjugate_product,
    torusWord_curve_conjugate P hp, highest_pairing]
  simp

/-- The descended torus acts on the long highest-root group by its base-field
unit, retaining the independent cubic-field unit in the torus parameters. -/
theorem torus_conjugate_highestHom (P : Parameters) (hp : P.prime = 2)
    (a : TorusCoordinates.OrbitParameters P) (t : fixedField P) :
    (TorusCoordinates.torusMulEquiv P hp a).val * highestHom P hp (Multiplicative.ofAdd t) *
      (TorusCoordinates.torusMulEquiv P hp a).val⁻¹ =
        highestHom P hp (Multiplicative.ofAdd (a.2.val * t)) := by
  have he : TorusCoordinates.orbitElementary P hp a *
      elementaryHighestHom P hp (Multiplicative.ofAdd t) *
      (TorusCoordinates.orbitElementary P hp a)⁻¹ =
        elementaryHighestHom P hp (Multiplicative.ofAdd (a.2.val * t)) := by
    apply Subtype.ext
    apply Subtype.ext
    change elementaryInclusion P (TorusCoordinates.orbitElementary P hp a *
      elementaryHighestHom P hp (Multiplicative.ofAdd t) *
      (TorusCoordinates.orbitElementary P hp a)⁻¹) =
        elementaryInclusion P (elementaryHighestHom P hp (Multiplicative.ofAdd (a.2.val * t)))
    simp only [map_mul, map_inv, elementaryHighestHom_val,
      TorusCoordinates.inclusion_orbitElementary]
    simpa [TorusCoordinates.expand, TorusCoordinates.fixedUnit] using
      product_conjugate_highest P hp (TorusCoordinates.expand P a) t.val
  simpa only [map_mul, map_inv, TorusCoordinates.torusMulEquiv_val,
    highestHom, MonoidHom.comp_apply] using
    congrArg (toCarrier P) he

private theorem unipotent_commute_highestHom (P : Parameters) (hp : P.prime = 2)
    (u : Carrier P) (hu : u ∈ unipotent P) (t : fixedField P) :
    Commute u (highestHom P hp (Multiplicative.ofAdd t)) := by
  have hz : highestHom P hp (Multiplicative.ofAdd t) ∈ highestRoot P := by
    rw [← highestHom_range P hp]
    exact ⟨_, rfl⟩
  obtain ⟨z, hz, he⟩ := highestRoot_le_center_unipotent P hp hz
  rw [← he]
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz (⟨u, hu⟩ : unipotent P))

/-- Every actual Borel element acts by a single nonzero base-field scalar. -/
theorem borel_conjugate_highestHom (P : Parameters) (hp : P.prime = 2)
    (b : Carrier P) (hb : b ∈ borel P) :
    ∃ c : (fixedField P)ˣ, ∀ t : fixedField P,
      b * highestHom P hp (Multiplicative.ofAdd t) * b⁻¹ =
        highestHom P hp (Multiplicative.ofAdd (c.val * t)) := by
  have hb' : b ∈ (unipotent P : Set (Carrier P)) * (torus P : Set (Carrier P)) := by
    rw [← borel_eq_mul P hp]
    exact hb
  obtain ⟨u, hu, d, hd, rfl⟩ := hb'
  obtain ⟨a, ha⟩ := (TorusCoordinates.torusMulEquiv P hp).surjective ⟨d, hd⟩
  have had : (TorusCoordinates.torusMulEquiv P hp a).val = d := congrArg Subtype.val ha
  refine ⟨a.2, fun t => ?_⟩
  rw [conjugate_product, ← had, torus_conjugate_highestHom P hp]
  exact (mul_inv_eq_iff_eq_mul).mpr (unipotent_commute_highestHom P hp u hu _).eq

/-- Fixing one nonidentity highest-root element forces the Borel scalar to be one. -/
theorem uniform_highestRoot (P : Parameters) (hp : P.prime = 2)
    (r : Carrier P) (hr : r ∈ highestRoot P) (hne : r ≠ 1) :
    borel P ⊓ Subgroup.centralizer ({r} : Set (Carrier P)) =
      borel P ⊓ Subgroup.centralizer (highestRoot P : Set (Carrier P)) := by
  rw [← highestHom_range P hp] at hr
  obtain ⟨t, rfl⟩ := hr
  have ht : t.toAdd ≠ 0 := by
    intro h
    apply hne
    have ht1 : t = 1 := congrArg Multiplicative.ofAdd h
    rw [ht1, map_one]
  apply le_antisymm
  · intro b hb
    obtain ⟨c, hc⟩ := borel_conjugate_highestHom P hp b hb.1
    have hfix : b * highestHom P hp t * b⁻¹ = highestHom P hp t :=
      (mul_inv_eq_iff_eq_mul).mpr (Subgroup.mem_centralizer_singleton_iff.mp hb.2)
    have hscalar : c.val * t.toAdd = t.toAdd := by
      exact congrArg Multiplicative.toAdd
        (highestHom_injective P hp ((hc t.toAdd).symm.trans hfix))
    have hc1 : c.val = 1 := mul_right_cancel₀ ht (hscalar.trans (one_mul _).symm)
    refine ⟨hb.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro z hz
    rw [← highestHom_range P hp] at hz
    obtain ⟨s, rfl⟩ := hz
    have hs := hc s.toAdd
    rw [hc1, one_mul] at hs
    exact ((mul_inv_eq_iff_eq_mul).mp hs).symm
  · exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (by
      rw [← highestHom_range P hp]
      exact ⟨t, rfl⟩)))

/-- Uniform Borel centralizers on the full embedded unipotent center. -/
theorem uniform (P : Parameters) (hp : P.prime = 2)
    (r : Carrier P)
    (hr : r ∈ (Subgroup.center (unipotent P)).map (unipotent P).subtype) (hne : r ≠ 1) :
    borel P ⊓ Subgroup.centralizer ({r} : Set (Carrier P)) =
      borel P ⊓ Subgroup.centralizer
        ((Subgroup.center (unipotent P)).map (unipotent P).subtype : Set (Carrier P)) := by
  rw [embedded_center_unipotent P hp] at hr ⊢
  exact uniform_highestRoot P hp r hr hne

end Triality.Standard.NormalizedRootCentralizers
