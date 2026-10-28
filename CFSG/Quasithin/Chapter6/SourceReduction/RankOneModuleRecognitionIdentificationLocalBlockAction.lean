module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFourSpace

/-!
# Centralizers in the original sixteen

In the contrary four-plane branch of source 6.2.11, the marked quotient has
its actual natural three-dimensional action. Its radical is the image of the
original layer. Fixed-space detection then identifies the common fixed
subgroups in the actual closure; the same radical centralizer theorem gives
the Sylow-centralizer supplement and its local-core displacement bound.

Source: Aschbacher--Smith, 6.2.11, printed p.686. These statements retain the
original layer and closure and do not assert the remaining block or A₇ argument.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryLinear BinaryTransvectionGroups
open Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
variable {G : Type*} [Group G] [Finite G] {L R : Subgroup G} {z : G}
  {P : Sylow 2 G} {M : Subgroup G} {n : ℕ}

theorem four_closure_centralizer_layer (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    sourceClosure (P : Subgroup G) L R z ⊓ centralizer (layer L R : Set G) =
      ZS (P : Subgroup G) L R := by
  let := (reduced_space h hnatural hz ho hP).elementary
  let U := sourceClosure (P : Subgroup G) L R z
  let S := ZS (P : Subgroup G) L R
  let f := linearAction (P : Subgroup G) L R z
  have hrad := (four_image_three_space h hnatural hz ho hP hplane hcard).2.2
  have hSn : seedSubspace (P : Subgroup G) L R z ≠ ⊥ := by
    intro he
    have hd := seedSubspace_finrank h hnatural hz ho hP
    rw [he, finrank_bot] at hd
    contradiction
  apply le_antisymm
  · intro u hu
    let uH : Centralizer z := ⟨u, map_subtype_le _ hu.1⟩
    let w : space (P : Subgroup G) L R z := ⟨projection z uH, by
      rw [← closure_image]
      exact mem_map_of_mem _ hu.1⟩
    have hw : Additive.ofMul w ∈ seedSubspace (P : Subgroup G) L R z := by
      apply (mem_iff_fixed_radical hSn _).mpr
      intro g hg
      rw [← hrad] at hg
      obtain ⟨a, ha, rfl⟩ := hg
      obtain ⟨v, hv, rfl⟩ := ha
      have he : v * uH * v⁻¹ = uH := by
        apply Subtype.ext
        change (v : G) * u * (v : G)⁻¹ = u
        rw [mem_centralizer_iff.mp hu.2 (v : G) hv, mul_inv_cancel_right]
      apply Additive.toMul.injective
      apply Subtype.ext
      change projection z v * projection z uH * (projection z v)⁻¹ = projection z uH
      rw [← map_inv, ← map_mul, ← map_mul, he]
    obtain ⟨s, hs, he⟩ := hw
    have he' : projection z s = projection z uH := he
    have hc : uH / s ∈ line z := QuotientGroup.eq_iff_div_mem.mp he'.symm
    have hh := S.mul_mem ((zpowers_le.mpr hz) hc) hs
    change (u / (s : G)) * (s : G) ∈ S at hh
    simpa only [div_mul_cancel] using hh
  · exact le_inf ((ZS_le_sourceClosure_intersection h hz).trans inf_le_left)
      (le_centralizer_iff.mp h.layer_centralizes_ZS)


/-- The common centralizer supplements the original layer in its Sylow
centralizer. The quotient action is the literal action on U/⟨z⟩. -/
theorem four_sylow_centralizer_supplement
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    (P : Subgroup G) ⊓ centralizer (layer L R : Set G) =
      layer L R ⊔ ((P : Subgroup G) ⊓
        centralizer ((sourceClosure (P : Subgroup G) L R z ⊔ layer L R : Subgroup G) : Set G)) := by
  let := (reduced_space h hnatural hz ho hP).elementary
  let := h.layer_elementary
  let U := sourceClosure (P : Subgroup G) L R z
  let B := layer L R
  let f := linearAction (P : Subgroup G) L R z
  let S := seedSubspace (P : Subgroup G) L R z
  have hthree := four_image_three_space h hnatural hz ho hP hplane hcard
  have hSn : S ≠ ⊥ := by
    intro he
    have hd := seedSubspace_finrank h hnatural hz ho hP
    change Module.finrank (ZMod 2) S = 1 at hd
    rw [he, finrank_bot] at hd
    contradiction
  have hSt : S ≠ ⊤ := by
    intro he
    have hd := seedSubspace_finrank h hnatural hz ho hP
    change Module.finrank (ZMod 2) S = 1 at hd
    rw [he, finrank_top, hthree.2.1] at hd
    contradiction
  apply le_antisymm
  · intro t ht
    let tH : Centralizer z := ⟨t, hP ht.1⟩
    have hfC : f tH ∈ centralizer (radical S : Set (BinaryLinear.GL
        (Additive (space (P : Subgroup G) L R z)))) := by
      apply mem_centralizer_iff.mpr
      intro a ha
      rw [← hthree.2.2] at ha
      obtain ⟨a, ha, rfl⟩ := ha
      obtain ⟨v, hv, rfl⟩ := ha
      change f v * f tH = f tH * f v
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_iff.mp ht.2 (v : G) hv)
    have hfB := centralizer_radical_le hSn hSt hfC
    rw [← hthree.2.2] at hfB
    obtain ⟨a, ha, he⟩ := hfB
    obtain ⟨v, hv, rfl⟩ := ha
    change f v = f tH at he
    let c : Centralizer z := v⁻¹ * tH
    have hcF : f c = 1 := by simp only [c, map_mul, map_inv, he, inv_mul_cancel]
    have hcK : (c : G) ∈ kernel (P : Subgroup G) L R z := by
      have hcA : action (P : Subgroup G) L R z c = 1 := by
        apply (linearize (P : Subgroup G) L R z).injective
        exact hcF.trans (map_one _).symm
      have hh : c ∈ (action (P : Subgroup G) L R z).ker := hcA
      rw [action_ker] at hh
      exact hh
    have hcU : (c : G) ∈ centralizer (U : Set G) := by
      rw [four_kernel_eq_centralizer h hnatural hz ho hP hplane hcard] at hcK
      exact hcK.2
    have hcT : (c : G) ∈ (P : Subgroup G) :=
      (P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem (h.layer_le_T hv)) ht.1
    have hcB : (c : G) ∈ centralizer (B : Set G) :=
      (centralizer (B : Set G)).mul_mem ((centralizer (B : Set G)).inv_mem (B.le_centralizer hv)) ht.2
    have hcUB : (c : G) ∈ centralizer ((U ⊔ B : Subgroup G) : Set G) := by
      have hh : U ⊔ B ≤ centralizer ({(c : G)} : Set G) :=
        sup_le (fun u hu => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hcU u hu))
          (fun b hb => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hcB b hb))
      exact mem_centralizer_iff.mpr (fun x hx => mem_centralizer_singleton_iff.mp (hh hx))
    have hh := (B ⊔ ((P : Subgroup G) ⊓ centralizer ((U ⊔ B : Subgroup G) : Set G))).mul_mem
      (mem_sup_left hv) (mem_sup_right ⟨hcT, hcUB⟩)
    change (v : G) * ((v : G)⁻¹ * t) ∈ _ at hh
    simpa only [mul_inv_cancel_left] using hh
  · exact sup_le (le_inf h.layer_le_T B.le_centralizer)
      (inf_le_inf_left _ (centralizer_le (show B ≤ U ⊔ B from le_sup_right)))

/-- The reciprocal fixed subgroup is the same original four-plane. -/
theorem four_layer_centralizer_closure
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    layer L R ⊓ centralizer (sourceClosure (P : Subgroup G) L R z : Set G) =
      ZS (P : Subgroup G) L R := by
  have he := (four_intersection_geometry h hnatural hz ho hP hplane hcard).2.1
  rw [four_kernel_eq_centralizer h hnatural hz ho hP hplane hcard, ← inf_assoc,
    inf_eq_left.mpr (layer_le_involution_centralizer h hz)] at he
  exact he

/-- The actual closure acts with image of order four on V; equivalently
its literal centralizer has index four in U. -/
theorem four_closure_action_index
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    (sourceClosure (P : Subgroup G) L R z ⊓ centralizer (layer L R : Set G)).relIndex
      (sourceClosure (P : Subgroup G) L R z) = 4 := by
  let U := sourceClosure (P : Subgroup G) L R z
  let S := ZS (P : Subgroup G) L R
  have hSU : S ≤ U := (ZS_le_sourceClosure_intersection h hz).trans inf_le_left
  have hc := (S.subgroupOf U).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hSU).toEquiv,
    (h.natural_ZS_geometry hnatural).2.1, four_closure_card h hnatural hz ho hP hplane hcard] at hc
  rw [four_closure_centralizer_layer h hnatural hz ho hP hplane hcard]
  change 4 * S.relIndex U = 16 at hc
  change S.relIndex U = 4
  omega

/-- The block's acting closure moves the original local core only inside
Z_S. Both normalities used here are relative to T or C_G(z). -/
theorem four_closure_local_core_commutator
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    ⁅sourceClosure (P : Subgroup G) L R z, (L ⊔ (P : Subgroup G)).pCoreIn 2⁆ ≤
      ZS (P : Subgroup G) L R := by
  let U := sourceClosure (P : Subgroup G) L R z
  let Q := (L ⊔ (P : Subgroup G)).pCoreIn 2
  have hQT : Q ≤ (P : Subgroup G) := by
    change (L ⊔ (P : Subgroup G)).pCoreIn 2 ≤ (P : Subgroup G)
    rw [← sylow_layer_centralizer_eq_core h (hnatural.1 ▸ hnatural.2.1)]
    exact inf_le_left
  have hUT : U ≤ (P : Subgroup G) := by
    have hc := pCoreIn_le_sylow (Centralizer z) (P.subtype hP)
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hP] at hc
    exact (local_closure_core h hnatural hz ho hP).1.trans hc
  have hQN : (P : Subgroup G) ≤ normalizer (Q : Set G) :=
    (show (P : Subgroup G) ≤ L ⊔ (P : Subgroup G) from le_sup_right).trans
      ((L ⊔ (P : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hcomm : ⁅U, Q⁆ ≤ U ⊓ centralizer (layer L R : Set G) := le_inf
    (le_normalizer_iff_commutator_le_left.mp
      ((hQT.trans hP).trans (closure_normalized _ _ _ _)))
    ((le_normalizer_iff_commutator_le_right.mp (hUT.trans hQN)).trans
      (local_core_centralizes_layer h))
  exact hcomm.trans_eq (four_closure_centralizer_layer h hnatural hz ho hP hplane hcard)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
