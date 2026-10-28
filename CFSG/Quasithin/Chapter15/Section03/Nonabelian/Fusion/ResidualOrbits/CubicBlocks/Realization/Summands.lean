module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models.Actions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.LocalProduct
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Action
public import Theory.GroupAction.CoprimeCentralizerLift
public import Theory.GroupTheory.PrimeOrderLift

/-!
# Cubics from the actual two natural summands

The earlier `LayerActions` supplies one common actor on V and the literal
quotient P/V. For each invariant natural summand, Cauchy's theorem in the
inverse image of the complementary cubic constructs an actual subgroup D of
order three. Its image is faithful because the action kernel is a two-group.
No conjugacy between the two summands is used.

Coprime lifting identifies C_P(D)V with the full inverse image of that
summand. The tensor action has no nontrivial D-fixed vector on V, so the
actual quotient projection identifies C_P(D) with the summand. These results
use only the genuine earlier module actions; they do not yet identify the
lifted action on the block. `PairingFormula` is the explicit output contract
for the remaining square and commutator calculation, not a source input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.53–55,
15.3.58(2), and 15.3.61(2), printed pp.1146–1148 and 1150–1151.
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization

/-- The rotation in the factor complementary to the chosen summand. -/
def complementaryRotation (i : Fin 2) : Actor :=
  if i = 0 then (1, rotation) else (rotation, 1)

def complementaryCubic (i : Fin 2) : Subgroup Actor := zpowers (complementaryRotation i)

/-- The two invariant natural summands, with their original factor labels. -/
def naturalSummand (i : Fin 2) : Subgroup SumVector :=
  if i = 0 then (MonoidHom.snd Plane Plane).ker else (MonoidHom.fst Plane Plane).ker

theorem complementaryRotation_order (i : Fin 2) : orderOf (complementaryRotation i) = 3 := by
  fin_cases i <;> exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem complementaryCubic_card (i : Fin 2) : Nat.card (complementaryCubic i) = 3 := by
  rw [complementaryCubic, Nat.card_zpowers, complementaryRotation_order]

theorem mem_naturalSummand_iff (i : Fin 2) (x : SumVector) :
    x ∈ naturalSummand i ↔ if i = 0 then x.2 = 1 else x.1 = 1 := by
  fin_cases i <;> rfl

theorem rotation_fixed_iff (i : Fin 2) (x : SumVector) :
    sumAction (complementaryRotation i) x = x ↔ x ∈ naturalSummand i := by
  have h : ∀ (j : Fin 2) (v : SumVector),
      sumAction (complementaryRotation j) v = v ↔ v ∈ naturalSummand j := by
    simp_rw [mem_naturalSummand_iff]
    decide +kernel
  exact h i x

theorem cubic_fixes_summand (i : Fin 2) (a : Actor) (ha : a ∈ complementaryCubic i)
    (x : SumVector) (hx : x ∈ naturalSummand i) : sumAction a x = x := by
  let _ : MulDistribMulAction Actor SumVector :=
    MulDistribMulAction.compHom SumVector sumAction
  have hs : complementaryCubic i ≤ MulAction.stabilizer Actor x :=
    zpowers_le.mpr ((rotation_fixed_iff i x).mpr hx)
  exact hs ha

theorem summand_invariant (i : Fin 2) (a : Actor) (x : SumVector)
    (hx : x ∈ naturalSummand i) : sumAction a x ∈ naturalSummand i := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  fin_cases i <;> simp [mem_naturalSummand_iff] at hx ⊢
  · change (MulDistribMulAction.toMulEquiv Plane a.2) x.2 = 1
    rw [hx, map_one]
  · change (MulDistribMulAction.toMulEquiv Plane a.1) x.1 = 1
    rw [hx, map_one]

theorem cubic_tensor_fixed (i : Fin 2) (x : TensorVector)
    (hx : tensorAction (complementaryRotation i) x = x) : x = 1 := by
  have h : ∀ (j : Fin 2) (v : TensorVector),
      tensorAction (complementaryRotation j) v = v → v = 1 := by decide +kernel
  exact h i x hx

variable {G : Type*} [Group G] {I Y P V : Subgroup G}
  {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
  [(V.subgroupOf P).Normal]

/-- The earlier source actions, followed by the literal quotient map P → P/V. -/
noncomputable def upperMap (d : LayerActions I Y P V hIP hIV) : P →* SumVector :=
  d.upperCoordinates.toMonoidHom.comp (QuotientGroup.mk' (V.subgroupOf P))

/-- The inverse images of the two natural summands, in the actual ambient P. -/
noncomputable def summandPreimage (d : LayerActions I Y P V hIP hIV) (i : Fin 2) :
    Subgroup G := ((naturalSummand i).comap (upperMap d)).map P.subtype

theorem mem_summandPreimage (d : LayerActions I Y P V hIP hIV) (i : Fin 2)
    (x : P) : (x : G) ∈ summandPreimage d i ↔ upperMap d x ∈ naturalSummand i := by
  constructor
  · rintro ⟨y, hy, he⟩
    have h : y = x := Subtype.ext he
    exact h ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem summandPreimage_le (d : LayerActions I Y P V hIP hIV) (i : Fin 2) :
    summandPreimage d i ≤ P := map_subtype_le _

theorem lower_le_summandPreimage (d : LayerActions I Y P V hIP hIV) (hVP : V ≤ P)
    (i : Fin 2) : V ≤ summandPreimage d i := by
  intro x hx
  apply (mem_summandPreimage d i ⟨x, hVP hx⟩).mpr
  have he : QuotientGroup.mk' (V.subgroupOf P) (⟨x, hVP hx⟩ : P) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hx
  change d.upperCoordinates (QuotientGroup.mk' _ _) ∈ _
  rw [he, map_one]
  exact (naturalSummand i).one_mem

theorem upperMap_conj (d : LayerActions I Y P V hIP hIV) (g : I) (x : P) :
    upperMap d ⟨(g : G) * (x : G) * (g : G)⁻¹,
      (mem_normalizer_iff.mp (hIP g.property) x).mp x.property⟩ =
      sumAction (d.actor g) (upperMap d x) := by
  simpa only [upperMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    upperAction_mk] using d.upper_compatible g (QuotientGroup.mk' _ x)

/-- The actual quotient summands are normalized by all of I. -/
theorem normalizes_summandPreimage (d : LayerActions I Y P V hIP hIV) (i : Fin 2) :
    I ≤ normalizer (summandPreimage d i : Set G) := by
  have hf (g : I) (x : G) (hx : x ∈ summandPreimage d i) :
      (g : G) * x * (g : G)⁻¹ ∈ summandPreimage d i := by
    let xP : P := ⟨x, summandPreimage_le d i hx⟩
    apply (mem_summandPreimage d i
      ⟨(g : G) * x * (g : G)⁻¹, (mem_normalizer_iff.mp (hIP g.property) x).mp xP.property⟩).mpr
    rw [upperMap_conj d g xP]
    exact summand_invariant i (d.actor g) _ ((mem_summandPreimage d i xP).mp hx)
  intro g hg
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hf ⟨g, hg⟩ x
  · intro hx
    simpa only [Subgroup.coe_inv, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using
      hf (⟨g, hg⟩ : I)⁻¹ (g * x * g⁻¹) hx

variable [Finite G]

/-- Lift the cubic in either individual factor. Cauchy's theorem is applied
inside its full inverse image; the two-group kernel makes its image faithful. -/
theorem exists_complementary_cubic (d : LayerActions I Y P V hIP hIV)
    (hVP : V ≤ P) (i : Fin 2) :
    ∃ D : Subgroup G, D ≤ I ∧ Nat.card D = 3 ∧
      (D.subgroupOf I).map d.actor = complementaryCubic i := by
  let R := (complementaryCubic i).comap d.actor
  let f : R →* complementaryCubic i :=
    (d.actor.comp R.subtype).codRestrict _ (fun r => r.property)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨x, hx⟩ := d.onto a
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change d.actor x ∈ complementaryCubic i
    rw [hx]
    exact a.property
  have hd : 3 ∣ Nat.card R := by
    rw [← complementaryCubic_card i]
    exact card_dvd_of_surjective f hf
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' 3 hd
  let b : I := r
  have hb : orderOf b = 3 := (Subgroup.orderOf_coe r).trans hr
  have hk : IsPGroup 2 d.actor.ker := by
    rw [d.kernel]
    exact (IsPGroup.of_card (p := 2) (n := 8) (d.card_core hVP)).comap_subtype
  have ha : orderOf (d.actor b) = 3 :=
    (d.actor.orderOf_map_eq_of_coprime_of_isPGroup_ker hk b (by rw [hb]; decide)).trans hb
  let D := zpowers (b : G)
  have hDI : D ≤ I := zpowers_le.mpr b.property
  have hD : Nat.card D = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hb]
  refine ⟨D, hDI, hD, ?_⟩
  have he : D.subgroupOf I = zpowers b := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le hDI, MonoidHom.map_zpowers]
    rfl
  rw [he, MonoidHom.map_zpowers]
  apply eq_of_le_of_card_ge (zpowers_le.mpr
    (show d.actor b ∈ complementaryCubic i from r.property))
  rw [Nat.card_zpowers, ha, complementaryCubic_card]

omit [Finite G] in
/-- A faithful image description of the cubic gives the exact fixed-quotient
criterion, keeping the actual conjugation and the original quotient map. -/
theorem fixed_quotient_iff (d : LayerActions I Y P V hIP hIV)
    (i : Fin 2) (D : Subgroup G) (hDI : D ≤ I)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic i) (x : P) :
    (∀ a ∈ D, MulAut.conj a (x : G) / (x : G) ∈ V) ↔
      upperMap d x ∈ naturalSummand i := by
  have he (a : I) :
      MulAut.conj (a : G) (x : G) / (x : G) ∈ V ↔
        sumAction (d.actor a) (upperMap d x) = upperMap d x := by
    let y : P := ⟨(a : G) * (x : G) * (a : G)⁻¹,
      (mem_normalizer_iff.mp (hIP a.property) x).mp x.property⟩
    have hq : MulAut.conj (a : G) (x : G) / (x : G) ∈ V ↔
        QuotientGroup.mk' (V.subgroupOf P) y = QuotientGroup.mk' _ x :=
      by
        change y / x ∈ V.subgroupOf P ↔ _
        exact QuotientGroup.eq_iff_div_mem.symm
    rw [hq, ← d.upperCoordinates.injective.eq_iff]
    change upperMap d y = upperMap d x ↔ _
    rw [upperMap_conj]
  constructor
  · intro hx
    have hm : complementaryRotation i ∈ (D.subgroupOf I).map d.actor := by
      rw [himage]
      exact mem_zpowers _
    obtain ⟨a, ha, hea⟩ := hm
    apply (rotation_fixed_iff i _).mp
    rw [← hea]
    exact (he a).mp (hx a ha)
  · intro hx a ha
    apply (he ⟨a, hDI ha⟩).mpr
    apply cubic_fixes_summand i _ _ _ hx
    rw [← himage]
    exact mem_map_of_mem d.actor ha

/-- Coprime lifting identifies the actual cubic block with the inverse image
of its natural quotient summand, rather than merely matching their orders. -/
theorem fusionBlock_eq_summandPreimage (d : LayerActions I Y P V hIP hIV)
    (hVP : V ≤ P) (i : Fin 2) (D : Subgroup G) (hDI : D ≤ I)
    (hD : Nat.card D = 3)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic i) :
    fusionBlock P V D = summandPreimage d i := by
  let _ := d.elementary_lower.toIsMulCommutative
  let _ : IsMulCommutative (V.subgroupOf P) :=
    V.comap_injective_isMulCommutative P.subtype_injective
  apply le_antisymm
  · apply sup_le _ (lower_le_summandPreimage d hVP i)
    intro x hx
    apply (mem_summandPreimage d i ⟨x, hx.1⟩).mpr
    apply (fixed_quotient_iff d i D hDI himage ⟨x, hx.1⟩).mp
    intro a ha
    have hc := mem_centralizer_iff.mp hx.2 a ha
    have he : MulAut.conj a x = x := by
      change a * x * a⁻¹ = x
      rw [hc, mul_inv_cancel_right]
    change MulAut.conj a x / x ∈ V
    rw [he, div_self']
    exact V.one_mem
  · intro x hx
    exact mem_centralizer_sup_of_coprime_fixed_coset P V D hVP
      (hDI.trans hIP) (hDI.trans hIV) (by rw [hD, d.card_lower]; decide)
      x (summandPreimage_le d i hx)
      ((fixed_quotient_iff d i D hDI himage ⟨x, summandPreimage_le d i hx⟩).mpr
        ((mem_summandPreimage d i ⟨x, summandPreimage_le d i hx⟩).mp hx))


omit [Finite G] in
/-- The cubic has no nontrivial fixed vector on the actual tensor group V. -/
theorem centralizer_disjoint_lower (d : LayerActions I Y P V hIP hIV)
    (i : Fin 2) (D : Subgroup G)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic i) :
    Disjoint (centralizer (D : Set G)) V := by
  apply disjoint_def.mpr
  intro x hxC hxV
  have hm : complementaryRotation i ∈ (D.subgroupOf I).map d.actor := by
    rw [himage]
    exact mem_zpowers _
  obtain ⟨a, ha, hea⟩ := hm
  have he : lowerAction I V hIV a ⟨x, hxV⟩ = ⟨x, hxV⟩ := by
    apply Subtype.ext
    rw [lowerAction_apply, mem_centralizer_iff.mp hxC a ha, mul_inv_cancel_right]
  have h := d.lower_compatible a ⟨x, hxV⟩
  rw [he, hea] at h
  have h1 := cubic_tensor_fixed i _ h.symm
  have hv : (⟨x, hxV⟩ : V) = 1 := by
    apply d.lowerCoordinates.injective
    simpa only [map_one] using h1
  exact congrArg V.subtype hv

/-- Projection of the cubic centralizer to its natural quotient summand. -/
noncomputable def centralizerProjection (d : LayerActions I Y P V hIP hIV)
    (hVP : V ≤ P) (i : Fin 2) (D : Subgroup G) (hDI : D ≤ I)
    (hD : Nat.card D = 3)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic i) :
    (P ⊓ centralizer (D : Set G) : Subgroup G) →* naturalSummand i :=
  ((upperMap d).comp (inclusion inf_le_left)).codRestrict _ (fun x => by
    apply (mem_summandPreimage d i (inclusion inf_le_left x)).mp
    rw [← fusionBlock_eq_summandPreimage d hVP i D hDI hD himage]
    exact (show P ⊓ centralizer (D : Set G) ≤ fusionBlock P V D from le_sup_left) x.property)

/-- No arbitrary group equivalence is used: the centralizer is identified
with its summand by the actual quotient projection. -/
noncomputable def centralizerEquiv (d : LayerActions I Y P V hIP hIV)
    (hVP : V ≤ P) (hcentral : V ≤ centralizer (P : Set G))
    (i : Fin 2) (D : Subgroup G) (hDI : D ≤ I) (hD : Nat.card D = 3)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic i) :
    (P ⊓ centralizer (D : Set G) : Subgroup G) ≃* naturalSummand i := by
  let f := centralizerProjection d hVP i D hDI hD himage
  apply MulEquiv.ofBijective f
  constructor
  · apply (injective_iff_map_eq_one f).mpr
    intro x hx
    have hxq : QuotientGroup.mk' (V.subgroupOf P) (inclusion inf_le_left x) = 1 := by
      apply d.upperCoordinates.injective
      have he := congrArg Subtype.val hx
      change upperMap d (inclusion inf_le_left x) = 1 at he
      change d.upperCoordinates (QuotientGroup.mk' _ (inclusion inf_le_left x)) = 1 at he
      rwa [map_one]
    have hxV : (x : G) ∈ V := by
      have h : inclusion inf_le_left x ∈ V.subgroupOf P :=
        (QuotientGroup.eq_one_iff _).mp hxq
      exact h
    exact Subtype.ext ((disjoint_def.mp (centralizer_disjoint_lower d i D himage))
      x.property.2 hxV)
  · intro w
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (V.subgroupOf P)
      (d.upperCoordinates.symm w)
    have hxw : upperMap d x = w := by
      change d.upperCoordinates (QuotientGroup.mk' _ x) = w
      rw [hx, d.upperCoordinates.apply_symm_apply]
    have hxB : (x : G) ∈ fusionBlock P V D := by
      rw [fusionBlock_eq_summandPreimage d hVP i D hDI hD himage]
      apply (mem_summandPreimage d i x).mpr
      rw [hxw]
      exact w.property
    change (x : G) ∈ (fusionBlock P V D : Set G) at hxB
    rw [fusionBlock_eq_product P V D hcentral] at hxB
    obtain ⟨c, hc, v, hv, hcv⟩ := hxB
    let cP : P := ⟨c, hc.1⟩
    let vP : P := ⟨v, hVP hv⟩
    have hv1 : upperMap d vP = 1 := by
      change d.upperCoordinates (QuotientGroup.mk' _ vP) = 1
      have hvq : QuotientGroup.mk' (V.subgroupOf P) vP = 1 :=
        (QuotientGroup.eq_one_iff vP).mpr hv
      rw [hvq, map_one]
    have hp : cP * vP = x := Subtype.ext hcv
    refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
    change upperMap d cP = w
    rw [← hxw, ← hp, map_mul, hv1, mul_one]

/-- Identify the chosen summand with its own natural binary plane. -/
def naturalSummandEquiv (i : Fin 2) : naturalSummand i ≃* Plane where
  toFun x := if i = 0 then (x : SumVector).1 else (x : SumVector).2
  invFun x := ⟨if i = 0 then (x, 1) else (1, x), by
    fin_cases i <;> simp [mem_naturalSummand_iff]⟩
  left_inv x := by
    apply Subtype.ext
    have hx := (mem_naturalSummand_iff i (x : SumVector)).mp x.property
    fin_cases i <;> apply Prod.ext <;> simp_all
  right_inv x := by fin_cases i <;> rfl
  map_mul' x y := by fin_cases i <;> rfl

/-- These are the pairing identities still to be derived from the earlier
actions and V = Z(P). They are an output contract, not earlier source data. -/
structure PairingFormula (d : LayerActions I Y P V hIP hIV) : Prop where
  square : ∀ x : P, ∃ hx : (x : G) ^ 2 ∈ V,
    d.lowerCoordinates ⟨(x : G) ^ 2, hx⟩ = Multiplicative.ofAdd
      (Matrix.vecMulVec (upperMap d x).1.toAdd (upperMap d x).2.toAdd)
  commutator : ∀ x y : P, ∃ hxy : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ V,
    d.lowerCoordinates ⟨(x : G) * y * (x : G)⁻¹ * (y : G)⁻¹, hxy⟩ =
      Multiplicative.ofAdd
        (Matrix.vecMulVec (upperMap d x).1.toAdd (upperMap d y).2.toAdd +
          Matrix.vecMulVec (upperMap d y).1.toAdd (upperMap d x).2.toAdd)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization
