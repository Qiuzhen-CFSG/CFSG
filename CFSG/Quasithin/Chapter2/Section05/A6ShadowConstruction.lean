module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.Initial
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.CoreReduction
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.NormalizerGeometry

/-!
# Assembly of the terminal A₆ local pair

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.569–570, the completion after Lemma 2.5.27.

The core calculation constructs an embedding of `S_C` in `C₂ × D₈`, forcing
`S_C = V ≅ C₄`. The normalizer calculation chooses a four-group and a compatible
representative `xs` of `xS`, using `C_G(t) ≤ H` to establish square stability.
The assembly constructs the elementary-sixteen group, both normalizer models,
and the actual local pair with globally maximal base order.

`Setup.exists_terminal_pair_of_source` discharges both intermediate geometry
targets from the explicit source centralizer premise and four concrete A₆
model inputs. It retains `xs` as the crossing element and leaves `H`, `K`,
`S`, `T`, `M`, `t`, and `z` unchanged. The preceding shadow argument owns the
centralizer premise, the model inputs, and the final Γe₀ contradiction.
The fixed-setup helper `terminal_pair_of_geometry` remains available.
-/

namespace CFSG.Quasithin.Chapter2.A6ShadowConstruction

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- Assemble the precise inputs to
`normalizer_mem_gammaStar_of_crossing_element` from the two intermediate
geometric calculations. The local-pair property is transported from the
incoming 2.5.23 correspondence; it is not assumed for the new product. -/
public theorem terminal_pair_of_geometry (d : Setup G)
    (reduction : CoreReduction d) (geometry : NormalizerGeometry d) :
    let A := geometry.E ⊔ conjugate d.x geometry.E
    let U := d.S ⊓ normalizer (A : Set G)
    let L := d.H ⊓ normalizer (A : Set G)
    let I := L ⊔ zpowers d.x
    Nonempty (A ≃* geometry.E × geometry.E) ∧
      IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧ A ≠ ⊥ ∧ IsPGroup 2 A ∧
      d.z ∈ A ∧
      Nonempty (L ≃* DihedralGroup 4 × Equiv.Perm (Fin 4)) ∧
      Nonempty ((conjugate d.x d.H ⊓ normalizer (A : Set G) : Subgroup G) ≃*
        DihedralGroup 4 × Equiv.Perm (Fin 4)) ∧
      I ≤ normalizer (A : Set G) ∧
      (U, L) ∈ localPairs (Chapter1.He G) d.M ∧
      (∀ W ∈ localBases (Chapter1.He G) d.M, Nat.card W ≤ Nat.card U) ∧
      U ≤ d.T ∧ d.x ∈ d.T ⊓ normalizer (A : Set G) ∧ d.x ∉ U ∧
      Nat.card d.S = 128 ∧ Nat.card U = 64 ∧
      Nat.card (d.sylow : Subgroup d.H) ≤ 2 * Nat.card U := by
  dsimp only
  let E := geometry.E
  let A := E ⊔ conjugate d.x E
  let U := d.S ⊓ normalizer (A : Set G)
  let L := d.H ⊓ normalizer (A : Set G)
  let I := L ⊔ zpowers d.x
  let : IsKleinFour E := geometry.four
  obtain ⟨hAmodel, hAelem, hAcard⟩ := d.elementarySixteen E geometry.le_sk
  let : IsElementaryAbelian 2 A := hAelem
  have hAne : A ≠ ⊥ := by
    intro he
    change Nat.card A = 16 at hAcard
    rw [he] at hAcard
    simp at hAcard
  have hxN : d.x ∈ normalizer (A : Set G) :=
    normalizes_join_conjugate_of_square_normalizes E geometry.square_normalizes
  have hSH : d.S ≤ d.H := by
    rw [d.generated]
    exact le_sup_right
  have hUE : U = d.S ⊓ normalizer (E : Set G) := by
    apply le_antisymm
    · rintro s ⟨hsS, hsN⟩
      have hsH : s ∈ d.H ⊓ normalizer (A : Set G) := ⟨hSH hsS, hsN⟩
      rw [geometry.same_normalizer] at hsH
      exact ⟨hsS, hsH.2⟩
    · rintro s ⟨hsS, hsN⟩
      have hsH : s ∈ d.H ⊓ normalizer (E : Set G) := ⟨hSH hsS, hsN⟩
      rw [← geometry.same_normalizer] at hsH
      exact ⟨hsS, hsH.2⟩
  have hpair : (U, L) ∈ localPairs (Chapter1.He G) d.M := by
    change (U, d.H ⊓ normalizer (A : Set G)) ∈ _
    rw [hUE, geometry.same_normalizer]
    exact (d.largestPairs E geometry.le_sk geometry.four).1
  have hmax : ∀ W ∈ localBases (Chapter1.He G) d.M, Nat.card W ≤ Nat.card U := by
    rw [hUE]
    exact (d.largestPairs E geometry.le_sk geometry.four).2
  obtain ⟨eD⟩ := geometry.dihedral
  obtain ⟨eN⟩ := geometry.symmetric
  obtain ⟨m, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (zpowers (d.x⁻¹ * geometry.e * d.x) ⊔ d.core)
    (d.K ⊓ normalizer (E : Set G)) geometry.factors_disjoint geometry.factors_commute
  let eL : L ≃* DihedralGroup 4 × Equiv.Perm (Fin 4) :=
    (MulEquiv.subgroupCongr geometry.product_normalizer).trans
      (m.symm.trans (eD.prodCongr eN))
  have hAconj : conjugate d.x A = A :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (A : Set G)).inv_mem hxN)
  have hLconj : conjugate d.x L =
      conjugate d.x d.H ⊓ normalizer (A : Set G) := by
    change (d.H ⊓ normalizer (A : Set G)).map (MulAut.conj d.x⁻¹).toMonoidHom = _
    rw [Subgroup.map_inf _ _ _ (MulAut.conj d.x⁻¹).injective,
      map_normalizer_eq_of_bijective A (MulAut.conj d.x⁻¹).bijective]
    change conjugate d.x d.H ⊓ normalizer (conjugate d.x A : Set G) = _
    rw [hAconj]
  let eLX : L ≃* (conjugate d.x d.H ⊓ normalizer (A : Set G) : Subgroup G) :=
    ((MulAut.conj d.x⁻¹).subgroupMap L).trans (MulEquiv.subgroupCongr hLconj)
  have hI : I ≤ normalizer (A : Set G) :=
    sup_le inf_le_right (zpowers_le.mpr hxN)
  have hUcard : Nat.card U = 64 := by rw [hUE]; exact geometry.card_base
  have hSylow : Nat.card (d.sylow : Subgroup d.H) = Nat.card d.S := by
    rw [Nat.card_congr ((d.sylow : Subgroup d.H).equivMapOfInjective
      d.H.subtype d.H.subtype_injective).toEquiv, d.sylow_eq]
  refine ⟨hAmodel, hAelem, hAcard, hAne, IsElementaryAbelian.isPGroup 2 A,
    d.z_mem_product E geometry.zK_mem, ⟨eL⟩, ⟨eLX.symm.trans eL⟩, hI, hpair,
    hmax, inf_le_left.trans d.s_le_t, ⟨d.x_mem, hxN⟩,
    (fun hxU => d.x_outside hxU.1), reduction.card_s, hUcard, ?_⟩
  rw [hSylow, reduction.card_s, hUcard]

/-- The complete conditional construction on pp.569–570. The only extra inputs
are `C_G(t) ≤ H` from 2.5.22(2) and the four specified calculations in the actual
automorphism group of A₆. The cyclic core, its embedding, inversion, the chosen
four-group, all normalizer factors, the local pair, and the orders are derived.

The crossing element is `y = d.x * s`. Every other source group and distinguished
element is the original one. In particular this does not assert square
stability, or the terminal construction, for the originally chosen `d.x`. -/
public theorem Setup.exists_terminal_pair_of_source (d : Setup G)
    (c : CoreReduction.ModelGeometry (CoreReduction.imageSylow d))
    (m : SquareMembership.Fusion.ModelFacts)
    (n : ActionNormalizer.ModelFacts)
    (o : FourGroupChoice.ReflectionOrbit (CoreReduction.imageSylow d))
    (hC : centralizer ({d.t} : Set G) ≤ d.H) :
    ∃ (V : Subgroup G) (s : d.S) (E : Subgroup G) (e : G),
      let y := d.x * (s : G)
      let A := E ⊔ conjugate y E
      let U := d.S ⊓ normalizer (A : Set G)
      let L := d.H ⊓ normalizer (A : Set G)
      let I := L ⊔ zpowers y
      let D := zpowers (y⁻¹ * e * y) ⊔ V
      let J := d.K ⊓ normalizer (E : Set G)
      V = d.core ∧ (V.subgroupOf d.S).Normal ∧
      Nonempty (V ≃* Multiplicative (ZMod 4)) ∧
      (∃ j : d.core →* Multiplicative (ZMod 2) × DihedralGroup 4,
        Function.Injective j) ∧
      IsKleinFour E ∧ E ≤ d.sk ∧ d.zK ∈ E ∧ e ∈ E ∧ e ∉ zpowers d.zK ∧
      Disjoint d.sk (conjugate y d.sk) ∧
      d.sk ≤ centralizer (conjugate y d.sk : Set G) ∧
      y ^ 2 ∈ normalizer (E : Set G) ∧
      (∀ v ∈ V, (y⁻¹ * e * y)⁻¹ * v * (y⁻¹ * e * y) = v⁻¹) ∧
      L = d.H ⊓ normalizer (E : Set G) ∧ L = D ⊔ J ∧
      Disjoint D J ∧ D ≤ centralizer (J : Set G) ∧
      Nonempty (D ≃* DihedralGroup 4) ∧ Nonempty (J ≃* Equiv.Perm (Fin 4)) ∧
      Nonempty (A ≃* E × E) ∧
      IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧ A ≠ ⊥ ∧ IsPGroup 2 A ∧
      d.z ∈ A ∧
      Nonempty (L ≃* DihedralGroup 4 × Equiv.Perm (Fin 4)) ∧
      Nonempty ((conjugate y d.H ⊓ normalizer (A : Set G) : Subgroup G) ≃*
        DihedralGroup 4 × Equiv.Perm (Fin 4)) ∧
      I ≤ normalizer (A : Set G) ∧
      (U, L) ∈ localPairs (Chapter1.He G) d.M ∧
      (∀ W ∈ localBases (Chapter1.He G) d.M, Nat.card W ≤ Nat.card U) ∧
      U ≤ d.T ∧ y ∈ d.T ⊓ normalizer (A : Set G) ∧ y ∉ U ∧
      Nat.card d.S = 128 ∧ Nat.card U = 64 ∧
      Nat.card (d.sylow : Subgroup d.H) ≤ 2 * Nat.card U := by
  have r := d.coreReduction_of_model c
  obtain ⟨s, ⟨geometry⟩⟩ := d.exists_normalizer_geometry_of_source r m n o hC
  have r' := CoreReduction.replaceX d r s
  obtain ⟨V, hVC, hVN, hfour⟩ := d.exists_normal_cyclicFour
  have hCV := d.core_eq_cyclicFour_of_model c V hVC hfour
  subst V
  refine ⟨d.core, s, geometry.E, geometry.e, ?_⟩
  dsimp only
  refine ⟨rfl, hVN, hfour, CoreReduction.exists_core_embedding d c,
    geometry.four, geometry.le_sk, geometry.zK_mem, geometry.e_mem,
    geometry.e_outside, (d.replaceX s).disjoint_sk_conjugate,
    (d.replaceX s).sk_centralizes_conjugate, geometry.square_normalizes,
    r'.inverts geometry.E geometry.le_sk geometry.four geometry.e
      geometry.e_mem geometry.e_outside,
    geometry.same_normalizer, geometry.product_normalizer,
    geometry.factors_disjoint, geometry.factors_commute,
    geometry.dihedral, geometry.symmetric, ?_⟩
  exact terminal_pair_of_geometry (d.replaceX s) r' geometry

end CFSG.Quasithin.Chapter2.A6ShadowConstruction
