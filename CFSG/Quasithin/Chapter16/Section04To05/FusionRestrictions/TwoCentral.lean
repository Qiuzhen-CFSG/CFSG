module
public import CFSG.Quasithin.Chapter16.Section04To05.Terminal

/-!
# Two-centrality and the product obstruction

Two-centrality means membership in the center of an actual Sylow two-subgroup,
as defined in `Terminal`. We transport those Sylow subgroups through genuine
isomorphisms. When Z(L) = 1, the commuting factors of an involution in KL
have square one, so the product calculation in `Fusion` applies.

The resulting involution lies in J ∩ N_G(K), with J in Δ₀. Transporting
its projection back to L proves that the original product is not two-central
in Lᵍ. Thus the conclusion concerns the opposite component, as in the source,
not merely L. The detector, the normalizer of X, and the exclusion of
two-central projections remain explicit prerequisites for this implication.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.5.6(5), printed p.1197. Conjugation is left conjugation.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Ambient isomorphisms transport relative Sylow subgroups. -/
theorem SylowIn.map_equiv {R L : Subgroup G} (h : SylowIn R L) (e : G ≃* G) :
    SylowIn (R.map e.toMonoidHom) (L.map e.toMonoidHom) := by
  obtain ⟨S, rfl⟩ := h
  refine ⟨S.mapSurjective (f := (L.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom) (L.equivMapOfInjective e.toMonoidHom e.injective).surjective, ?_⟩
  change ((S : Subgroup L).map (L.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom).map
      (L.map e.toMonoidHom).subtype = _
  rw [map_map, map_map]
  rfl

/-- Two-centrality transports by mapping its witnessing Sylow subgroup. -/
theorem IsTwoCentralIn.map_equiv {L : Subgroup G} {v : G}
    (h : IsTwoCentralIn L v) (e : G ≃* G) :
    IsTwoCentralIn (L.map e.toMonoidHom) (e v) := by
  obtain ⟨hv, S, hS, hvS, hSC⟩ := h
  refine ⟨(e.orderOf_eq v).trans hv, S.map e.toMonoidHom,
    hS.map_equiv e, ⟨v, hvS, rfl⟩, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  simpa using congrArg e (mem_centralizer_singleton_iff.mp (hSC hx))

/-- Conjugation preserves two-centrality in the corresponding component. -/
theorem isTwoCentralIn_conjBy_iff {L : Subgroup G} {v g : G} :
    IsTwoCentralIn (L.conjBy g) (MulAut.conj g v) ↔ IsTwoCentralIn L v := by
  constructor
  · intro h
    have hh := h.map_equiv (MulAut.conj g⁻¹)
    change IsTwoCentralIn ((L.conjBy g).conjBy g⁻¹) _ at hh
    rw [conjBy_inv] at hh
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro h
    exact h.map_equiv (MulAut.conj g)

omit [Finite G] in
/-- Centerlessness makes the component and its ambient centralizer disjoint. -/
theorem disjoint_centralizer_of_center_eq_bot {L : Subgroup G} (hZ : center L = ⊥) :
    Disjoint L (centralizer (L : Set G)) := by
  apply Subgroup.disjoint_def.mpr
  intro x hxL hxC
  have hx : (⟨x, hxL⟩ : L) ∈ center L := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp hxC y y.property)
  rw [hZ] at hx
  exact congrArg Subtype.val (show (⟨x, hxL⟩ : L) = 1 from hx)

/-- The deduction in 16.5.6(5), using the source normalizer condition on the
forbidden inner involution and testing the product in the opposite component. -/
theorem projected_product_not_twoCentral
    {L X : Subgroup G} {g l u c v : G}
    (hZ : center L = ⊥)
    (hXL : X ≤ L) (hgX : g ∈ normalizer (X : Set G))
    (hu : u ∈ (centralizer (L : Set G)).conjBy g) (hu2 : orderOf u = 2)
    (hc : c ∈ centralizer (L : Set G))
    (hv : v ∈ L) (hl : l ∈ L) (hucv : u = c * v)
    (hdetect : ∀ (J : Subgroup G),
      (∃ a : G, J = (centralizer (L : Set G)).conjBy a) →
      ∀ i : G, i ∈ J → orderOf i = 2 →
        i ∈ centralizer (L : Set G) ⊔ L → i ∉ centralizer (L : Set G) →
        J ∈ deltaZero L)
    (havoid : ∀ J ∈ deltaZero L, ∀ i k w : G,
      i ∈ J → i ∈ normalizer (centralizer (L : Set G) : Set G) →
      orderOf i = 2 → k ∈ centralizer (L : Set G) →
      w ∈ L → i = k * w → ¬ IsTwoCentralIn L w)
    (hw : v * MulAut.conj l v ∈ X) (hw2 : orderOf (v * MulAut.conj l v) = 2) :
    ¬ IsTwoCentralIn (L.conjBy g) (v * MulAut.conj l v) := by
  intro htwo
  have hdisjoint := disjoint_centralizer_of_center_eq_bot hZ
  have hu_sq : u * u = 1 := by
    simpa [pow_two] using (orderOf_eq_prime_iff.mp hu2).1
  have hsq : (c * c) * (v * v) = 1 := by
    calc
      (c * c) * (v * v) = c * (c * v) * v := by group
      _ = c * (v * c) * v := by rw [← mem_centralizer_iff.mp hc v hv]
      _ = (c * v) * (c * v) := by group
      _ = 1 := by rwa [← hucv]
  have hc2 : c * c = 1 := by
    apply Subgroup.disjoint_def.mp hdisjoint
    · rw [mul_eq_one_iff_eq_inv.mp hsq]
      exact L.inv_mem (L.mul_mem hv hv)
    · exact (centralizer (L : Set G)).mul_mem hc hc
  have hw1 : v * MulAut.conj l v ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hw2
    contradiction
  have hprod : v * MulAut.conj l v = u * MulAut.conj l u := by
    rw [hucv, product_of_projected_involutions hc hc2 hv hl]
  obtain ⟨J, i, k, hJ, hiJ, hi2, hk, hi, hqL, _⟩ :=
    exists_inner_involution_of_product hdisjoint hXL hgX hu hu2 hw hw1 hprod hdetect
  have hiN : i ∈ normalizer (centralizer (L : Set G) : Set G) := by
    rw [hi]
    apply mul_mem ((centralizer (L : Set G)).le_normalizer hk)
    apply centralizer_le_normalizer _
    intro x hx
    exact (mem_centralizer_iff.mp hx _ hqL).symm
  apply havoid J hJ i k _ hiJ hiN hi2 hk hqL hi
  have hh := htwo.map_equiv (MulAut.conj g⁻¹)
  change IsTwoCentralIn ((L.conjBy g).conjBy g⁻¹) _ at hh
  rwa [conjBy_inv] at hh

end CFSG.Quasithin.Chapter16.Intersections
