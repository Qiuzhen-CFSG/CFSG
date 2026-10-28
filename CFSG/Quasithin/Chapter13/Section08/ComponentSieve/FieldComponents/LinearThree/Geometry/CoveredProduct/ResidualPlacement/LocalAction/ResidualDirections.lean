module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.QuotientMarks
public import Theory.GroupTheory.CubicAutomorphismLines
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The marked order-nine quotient and its two residual directions

Assume the intrinsic cubic orders from the local model calculation and the
factorization in 13.2.2(3). If every element of T∩L fixed the X quotient,
both generating marks of L₁/O₂(L₁) would be fixed. The commutator defining
X would then lie in O₂(L₁), contradicting injectivity of the X mark.
A nontrivial cubic automorphism is inversion. Since the L₀ mark is central
and fixed by that same element, the marks are disjoint. Their literal
multiplication map is the direct-product equivalence. Thus this particular
quotient is elementary abelian of order nine, and its T-invariant cubic
subgroups are exactly the two source marks.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 and Lemma 13.2.2(3), printed p.877; 13.8.16, pp.952–953,
and 13.8.21(1), p.957. The two intrinsic cubic orders remain explicit here;
this module does not claim their construction from the natural setup.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
variable {G : Type*} [Group G] [Finite G]

/-- The earlier factorization generates the quotient with the actual two marks. -/
theorem marks_generate (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hTV : T ≤ normalizer (V₁ : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) :
    (zeroCoreMap L T V₁ hTL hfactor).range ⊔ (plusCoreMap L T V₁ hTV).range = ⊤ := by
  rw [zeroCoreMap, plusCoreMap, localCoreMap_range, localCoreMap_range]
  unfold Source.starImage
  rw [← Subgroup.map_sup, ← subgroupOf_sup (zero_le_one_of_factorization L T V₁ hfactor)
    (plus_le_one L T V₁ hTV)]
  have he : zero L ⊔ plus L T V₁ = one L T V₁ := (sup_comm _ _).trans hfactor.symm
  rw [he, subgroupOf_self, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]

/-- The line calculation for the actual two residual marks. Cubic orders and
 the inverter remain explicit until their local construction is assembled. -/
theorem invariant_marked_line (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hTV : T ≤ normalizer (V₁ : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    [IsMulCommutative (one L T V₁ ⧸ pCore 2 (one L T V₁))]
    (hzero : Nat.card (zero L ⧸ pCore 2 (zero L)) = 3)
    (hplus : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3)
    (t : (T ⊓ L : Subgroup G))
    (hinv : ∀ x : plus L T V₁ ⧸ pCore 2 (plus L T V₁),
      coreAction (plus L T V₁)
        ⟨t.val, T_normalizes_plus L T V₁ hTL hTV t.property.1⟩ x = x⁻¹)
    (C : Subgroup (one L T V₁ ⧸ pCore 2 (one L T V₁)))
    (hC : Nat.card C = 3)
    (hstable : ∀ s : T, ∀ x ∈ C,
      coreAction (one L T V₁) ⟨s.val, T_normalizes_one L T V₁ hTV s.property⟩ x ∈ C) :
    C = (zeroCoreMap L T V₁ hTL hfactor).range ∨
      C = (plusCoreMap L T V₁ hTV).range := by
  have hZ : Nat.card (zeroCoreMap L T V₁ hTL hfactor).range = 3 :=
    (Nat.card_congr (MonoidHom.ofInjective
      (zeroCoreMap_injective L T V₁ hTL hfactor)).toEquiv).symm.trans hzero
  have hX : Nat.card (plusCoreMap L T V₁ hTV).range = 3 :=
    (Nat.card_congr (MonoidHom.ofInjective
      (plusCoreMap_injective L T V₁ hTV)).toEquiv).symm.trans hplus
  apply Theory.GroupTheory.CubicAutomorphismLines.invariant_line_eq
    (zeroCoreMap L T V₁ hTL hfactor).range (plusCoreMap L T V₁ hTV).range C
    hZ hX hC (marks_generate L T V₁ hTL hTV hfactor)
    (coreAction (one L T V₁) ⟨t.val, T_normalizes_one L T V₁ hTV t.property.1⟩)
  · rintro _ ⟨z, rfl⟩
    exact zeroCoreMap_fixed L T V₁ hTL hTV hfactor t z
  · rintro _ ⟨x, rfl⟩
    change coreAction (one L T V₁) _ (localCoreMap _ _ _ _ x) = _
    rw [← localCoreMap_equivariant _ _ _ _ t.val
      (T_normalizes_plus L T V₁ hTL hTV t.property.1), hinv]
    exact map_inv _ _
  · exact hstable ⟨t.val, t.property.1⟩



/-- The commutator definition of X forces a nontrivial action of T∩L on its
 cubic quotient: otherwise both generating marks of L₁/O₂(L₁) would be fixed. -/
theorem exists_nontrivial_plus_action (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hTV : T ≤ normalizer (V₁ : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hplus : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3) :
    ∃ t : (T ⊓ L : Subgroup G), coreAction (plus L T V₁)
      ⟨t.val, T_normalizes_plus L T V₁ hTL hTV t.property.1⟩ ≠ 1 := by
  classical
  by_contra! hall
  have hfix (t : (T ⊓ L : Subgroup G)) :
      coreAction (one L T V₁) ⟨t.val, T_normalizes_one L T V₁ hTV t.property.1⟩ = 1 := by
    let a := coreAction (one L T V₁)
      ⟨t.val, T_normalizes_one L T V₁ hTV t.property.1⟩
    have he : (zeroCoreMap L T V₁ hTL hfactor).range ⊔
        (plusCoreMap L T V₁ hTV).range ≤ a.toMonoidHom.eqLocus (MonoidHom.id _) := by
      apply sup_le
      · rintro _ ⟨z, rfl⟩
        exact zeroCoreMap_fixed L T V₁ hTL hTV hfactor t z
      · rintro _ ⟨x, rfl⟩
        change a (plusCoreMap L T V₁ hTV x) = plusCoreMap L T V₁ hTV x
        dsimp only [a, plusCoreMap]
        rw [← localCoreMap_equivariant _ _ _ _ t.val
          (T_normalizes_plus L T V₁ hTL hTV t.property.1), hall]
        rfl
    rw [marks_generate L T V₁ hTL hTV hfactor] at he
    ext x
    exact he (mem_top x)
  have hc : ⁅one L T V₁, T ⊓ L⁆ ≤ (one L T V₁).pCoreIn 2 := by
    apply commutator_le.mpr
    intro b hb t ht
    have h := (coreAction_eq_one_iff _ _).mp (hfix ⟨t, ht⟩) ⟨b, hb⟩
    have hm : t * b * t⁻¹ * b⁻¹ ∈ (one L T V₁).pCoreIn 2 :=
      ⟨_, h, rfl⟩
    have hi := ((one L T V₁).pCoreIn 2).inv_mem hm
    simpa only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc] using hi
  have hx : plus L T V₁ ≤ (one L T V₁).pCoreIn 2 := (residual_le _).trans hc
  have hmap (x : plus L T V₁ ⧸ pCore 2 (plus L T V₁)) :
      plusCoreMap L T V₁ hTV x = 1 := by
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (plus L T V₁)) x
    rw [plusCoreMap, localCoreMap_mk]
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨b, hb, he⟩ := hx u.property
    have he' : b = inclusion (plus_le_one L T V₁ hTV) u := Subtype.ext he
    exact he' ▸ hb
  have htrivial (x : plus L T V₁ ⧸ pCore 2 (plus L T V₁)) : x = 1 :=
    plusCoreMap_injective L T V₁ hTV ((hmap x).trans (map_one _).symm)
  have hone : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 1 :=
    Nat.card_eq_one_iff_exists.mpr ⟨1, htrivial⟩
  omega

/-- Construction of the source inverter from the cubic order and the earlier
 factorization; no inversion premise is assumed. -/
theorem exists_plus_inverter (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hTV : T ≤ normalizer (V₁ : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hplus : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3) :
    ∃ t : (T ⊓ L : Subgroup G),
      (∀ x : plus L T V₁ ⧸ pCore 2 (plus L T V₁), coreAction (plus L T V₁)
        ⟨t.val, T_normalizes_plus L T V₁ hTL hTV t.property.1⟩ x = x⁻¹) ∧
      coreAction (zero L) ⟨t.val, L_normalizes_zero L t.property.2⟩ = 1 := by
  obtain ⟨t, ht⟩ := exists_nontrivial_plus_action L T V₁ hTL hTV hfactor hplus
  refine ⟨t, ?_, L_centralizes_zero_quotient L ⟨t.val, t.property.2⟩⟩
  exact (Theory.GroupTheory.CubicAutomorphismLines.automorphism_eq_one_or_inv hplus _).resolve_left ht



omit [Finite G] in
private theorem coreAction_inner (B : Subgroup G) (b : B) (x : B ⧸ pCore 2 B) :
    coreAction B ⟨b.val, B.le_normalizer b.property⟩ x =
      QuotientGroup.mk' (pCore 2 B) b * x * (QuotientGroup.mk' (pCore 2 B) b)⁻¹ := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) x
  rw [coreAction_mk, ← map_inv, ← map_mul, ← map_mul]
  rfl

/-- The L₀ mark commutes with the whole quotient, not only with the X mark. -/
theorem zeroCoreMap_commute (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (z : zero L ⧸ pCore 2 (zero L))
    (q : one L T V₁ ⧸ pCore 2 (one L T V₁)) :
    Commute (zeroCoreMap L T V₁ hTL hfactor z) q := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (one L T V₁)) q
  have hbL : b.val ∈ L := one_le_L_of_factorization L T V₁ hTL hfactor b.property
  have he := localCoreMap_equivariant (one L T V₁) (zero L)
    (zero_le_one_of_factorization L T V₁ hfactor) (one_normalizes_zero L T V₁ hTL)
    b.val (L_normalizes_zero L hbL) ((one L T V₁).le_normalizer b.property) z
  rw [L_centralizes_zero_quotient L ⟨b.val, hbL⟩] at he
  change zeroCoreMap L T V₁ hTL hfactor z =
    coreAction (one L T V₁) ⟨b.val, (one L T V₁).le_normalizer b.property⟩
      (zeroCoreMap L T V₁ hTL hfactor z) at he
  rw [coreAction_inner] at he
  exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm

/-- The two actual marks are disjoint because one is fixed and the other
 inverted by the constructed source element. -/
theorem marks_disjoint (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hTV : T ≤ normalizer (V₁ : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hplus : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3) :
    Disjoint (zeroCoreMap L T V₁ hTL hfactor).range (plusCoreMap L T V₁ hTV).range := by
  obtain ⟨t, hinv, _⟩ := exists_plus_inverter L T V₁ hTL hTV hfactor hplus
  apply disjoint_iff_inf_le.mpr
  rintro q ⟨⟨z, hz⟩, ⟨x, hx⟩⟩
  apply mem_bot.mpr
  have hzfix := zeroCoreMap_fixed L T V₁ hTL hTV hfactor t z
  rw [hz] at hzfix
  have hxinv : coreAction (one L T V₁)
      ⟨t.val, T_normalizes_one L T V₁ hTV t.property.1⟩ q = q⁻¹ := by
    rw [← hx]
    change coreAction _ _ (localCoreMap _ _ _ _ x) = _
    rw [← localCoreMap_equivariant _ _ _ _ t.val
      (T_normalizes_plus L T V₁ hTL hTV t.property.1), hinv]
    exact map_inv _ _
  have hqi : q = q⁻¹ := hzfix.symm.trans hxinv
  have hq2 : q ^ 2 = 1 := by
    calc
      q ^ 2 = q * q := pow_two _
      _ = q * q⁻¹ := congrArg (q * ·) hqi
      _ = 1 := mul_inv_cancel _
  have hx3 : x ^ 3 = 1 := by simpa only [hplus] using pow_card_eq_one' (x := x)
  have hq3 : q ^ 3 = 1 := by
    rw [← hx, ← map_pow, hx3, map_one]
  have he : q ^ 3 = q := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hq2, one_mul]
  exact he.symm.trans hq3

/-- Multiplication of the two marked inclusions is the actual direct-product
 equivalence. This retains the positions of both residuals in L₁/O₂(L₁). -/
noncomputable def markedProductEquiv (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hTV : T ≤ normalizer (V₁ : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hplus : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3) :
    ((zero L ⧸ pCore 2 (zero L)) ×
      (plus L T V₁ ⧸ pCore 2 (plus L T V₁))) ≃*
        (one L T V₁ ⧸ pCore 2 (one L T V₁)) := by
  let f := zeroCoreMap L T V₁ hTL hfactor
  let g := plusCoreMap L T V₁ hTV
  let hc := fun z x => zeroCoreMap_commute L T V₁ hTL hfactor z (g x)
  apply MulEquiv.ofBijective (f.noncommCoprod g hc)
  constructor
  · exact (MonoidHom.noncommCoprod_injective f g hc).mpr
      ⟨zeroCoreMap_injective L T V₁ hTL hfactor, plusCoreMap_injective L T V₁ hTV,
        marks_disjoint L T V₁ hTL hTV hfactor hplus⟩
  · apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.noncommCoprod_range]
    exact marks_generate L T V₁ hTL hTV hfactor

theorem markedProductEquiv_apply (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hTV : T ≤ normalizer (V₁ : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hplus : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3)
    (z : zero L ⧸ pCore 2 (zero L)) (x : plus L T V₁ ⧸ pCore 2 (plus L T V₁)) :
    markedProductEquiv L T V₁ hTL hTV hfactor hplus (z, x) =
      zeroCoreMap L T V₁ hTL hfactor z * plusCoreMap L T V₁ hTV x := rfl

/-- The marked quotient has order nine once the two intrinsic cubic orders
 have been proved. -/
theorem one_quotient_card (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hTV : T ≤ normalizer (V₁ : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hzero : Nat.card (zero L ⧸ pCore 2 (zero L)) = 3)
    (hplus : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3) :
    Nat.card (one L T V₁ ⧸ pCore 2 (one L T V₁)) = 9 := by
  rw [← Nat.card_congr (markedProductEquiv L T V₁ hTL hTV hfactor hplus).toEquiv,
    Nat.card_prod, hzero, hplus]

/-- Commutativity of the same quotient follows from its marked cubic factors. -/
theorem one_quotient_commutative (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hTV : T ≤ normalizer (V₁ : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hzero : Nat.card (zero L ⧸ pCore 2 (zero L)) = 3)
    (hplus : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3) :
    IsMulCommutative (one L T V₁ ⧸ pCore 2 (one L T V₁)) := by
  let : IsMulCommutative (zero L ⧸ pCore 2 (zero L)) :=
    (isCyclic_of_prime_card hzero).isMulCommutative
  let : IsMulCommutative (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) :=
    (isCyclic_of_prime_card hplus).isMulCommutative
  let e := markedProductEquiv L T V₁ hTL hTV hfactor hplus
  refine ⟨⟨fun a b => e.symm.injective ?_⟩⟩
  simp only [map_mul, mul_comm]

/-- Its exponent is three, so the quotient of order nine is elementary abelian. -/
theorem one_quotient_cube (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hTV : T ≤ normalizer (V₁ : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hzero : Nat.card (zero L ⧸ pCore 2 (zero L)) = 3)
    (hplus : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3)
    (q : one L T V₁ ⧸ pCore 2 (one L T V₁)) : q ^ 3 = 1 := by
  let e := markedProductEquiv L T V₁ hTL hTV hfactor hplus
  obtain ⟨⟨z, x⟩, rfl⟩ := e.surjective q
  have hz : z ^ 3 = 1 := by simpa only [hzero] using pow_card_eq_one' (x := z)
  have hx : x ^ 3 = 1 := by simpa only [hplus] using pow_card_eq_one' (x := x)
  rw [← map_pow, Prod.pow_mk, hz, hx]
  exact map_one e



/-- The literal two subgroup images are cubic, with no replacement of their marks. -/
theorem marks_card_three (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hTV : T ≤ normalizer (V₁ : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hzero : Nat.card (zero L ⧸ pCore 2 (zero L)) = 3)
    (hplus : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3) :
    Nat.card (zeroCoreMap L T V₁ hTL hfactor).range = 3 ∧
      Nat.card (plusCoreMap L T V₁ hTV).range = 3 := by
  exact ⟨(Nat.card_congr (MonoidHom.ofInjective
      (zeroCoreMap_injective L T V₁ hTL hfactor)).toEquiv).symm.trans hzero,
    (Nat.card_congr (MonoidHom.ofInjective
      (plusCoreMap_injective L T V₁ hTV)).toEquiv).symm.trans hplus⟩

/-- Final invariant-line deduction: both the inverter and quotient
 commutativity are derived, leaving only the earlier factorization and
 the two intrinsic cubic orders as inputs. -/
theorem invariant_marked_line_of_cubic_orders (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hTV : T ≤ normalizer (V₁ : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hzero : Nat.card (zero L ⧸ pCore 2 (zero L)) = 3)
    (hplus : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3)
    (C : Subgroup (one L T V₁ ⧸ pCore 2 (one L T V₁)))
    (hC : Nat.card C = 3)
    (hstable : ∀ s : T, ∀ x ∈ C,
      coreAction (one L T V₁) ⟨s.val, T_normalizes_one L T V₁ hTV s.property⟩ x ∈ C) :
    C = (zeroCoreMap L T V₁ hTL hfactor).range ∨
      C = (plusCoreMap L T V₁ hTV).range := by
  let := one_quotient_commutative L T V₁ hTL hTV hfactor hzero hplus
  obtain ⟨t, ht, _⟩ := exists_plus_inverter L T V₁ hTL hTV hfactor hplus
  exact invariant_marked_line L T V₁ hTL hTV hfactor hzero hplus t ht C hC hstable

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
