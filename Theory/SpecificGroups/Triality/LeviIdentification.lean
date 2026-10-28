module
public import Theory.SpecificGroups.Triality.ParabolicLocalDefinitions
public import Theory.SpecificGroups.Triality.LeviFields
public import Theory.SpecificGroups.Triality.LeviTwistedDescent
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices
public import Theory.SpecificGroups.Triality.LeviArmCommutation
public import Theory.SpecificGroups.SL2.PrimeToResidual
public import Theory.SpecificGroups.SL2.TwoCore
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.IsPerfect

/-!
# Descent of rank-one subgroups in genuine triality

A homomorphism from characteristic-two SL₂ into the graph-field fixed points
lands in the elementary subgroup: transvection induction proves this directly,
including the binary field. A faithful such homomorphism remains faithful after
quotienting the elementary group by its center, because SL₂ has trivial center
in characteristic two. This identifies a descended root Levi once the image of
the split-matrix homomorphism has been proved to be the fixed part of `splitLevi`.
The two-core vanishes, and perfectness holds when the coefficient field has
more than two elements.

The final identifications instantiate `PinnedRankOneMaps` and
`ArmRootCommutation` with their proved Geck-matrix constructions. The exact
fixed-part ranges come from `LeviTwistedDescent`: the three arms descend to
SL₂ over the q³-element `ExtensionField`, and the central vertex descends to
SL₂ over the q-element base field. These are the root-generated subsystem
groups (the groups M_J in GLS3 §2.6), before adjoining the full Cartan torus.
Both descended groups have trivial two-core, including q = 2. The arm Levi
is perfect for every q; central perfectness requires q > 2.

Sources: GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`); the local quotients
in Aschbacher--Smith F.1.12(I)(4), printed pp. 263--264 (`refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.Parabolics

variable {F : Type*} [Field F]

/-- SL₂ maps into the actual elementary fixed-point subgroup because its
transvections are killed by the characteristic. Perfectness is unnecessary. -/
theorem sl2_mem_elementary (P : Parameters) (hp : P.prime = 2) [CharP F 2]
    (f : SL(2, F) →* fixedSubgroup P) (g : SL(2, F)) :
    f g ∈ elementarySubgroup P := by
  apply Matrix.SL2.transvection_induction (fun g => f g ∈ elementarySubgroup P) ?_ ?_ g
  · intro i j hij c
    have hpow (n : ℕ) : SpecialLinearGroup.transvection hij c ^ n =
        SpecialLinearGroup.transvection hij (n • c) := by
      induction n with
      | zero => simp [SpecialLinearGroup.transvection_coeff_zero]
      | succ n ih =>
        rw [pow_succ, ih, ← SpecialLinearGroup.transvection_add, succ_nsmul]
    apply mem_elementarySubgroup_of_pow P _ 1
    have h := congrArg f (hpow 2)
    simpa [nsmul_eq_mul, hp, CharTwo.two_eq_zero,
      SpecialLinearGroup.transvection_coeff_zero] using h
  · intro A B hA hB
    simpa only [map_mul] using (elementarySubgroup P).mul_mem hA hB

/-- Restrict a fixed-point SL₂ homomorphism to the elementary group. -/
def sl2ElementaryLift (P : Parameters) (hp : P.prime = 2) [CharP F 2]
    (f : SL(2, F) →* fixedSubgroup P) : SL(2, F) →* ElementaryGroup P :=
  f.codRestrict (elementarySubgroup P) (sl2_mem_elementary P hp f)

@[simp] theorem sl2ElementaryLift_coe (P : Parameters) (hp : P.prime = 2) [CharP F 2]
    (f : SL(2, F) →* fixedSubgroup P) (g : SL(2, F)) :
    (sl2ElementaryLift P hp f g : fixedSubgroup P) = f g := rfl

private theorem centralQuotient_comp_injective {A G : Type*} [Group A] [Group G]
    (f : A →* G) (hf : Function.Injective f) (hA : Subgroup.center A = ⊥) :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center G)).comp f) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro a ha
  have hc : f a ∈ Subgroup.center G := (QuotientGroup.eq_one_iff _).mp ha
  have haC : a ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro b
    apply hf
    simpa only [map_mul] using Subgroup.mem_center_iff.mp hc (f b)
  simpa only [hA, Subgroup.mem_bot] using haC

/-- A faithful characteristic-two SL₂ in the fixed points remains faithful
in the quotient by the center of the elementary group. -/
theorem sl2_toCarrier_injective (P : Parameters) (hp : P.prime = 2) [CharP F 2]
    (f : SL(2, F) →* fixedSubgroup P) (hf : Function.Injective f) :
    Function.Injective ((toCarrier P).comp (sl2ElementaryLift P hp f)) := by
  apply centralQuotient_comp_injective _ ?_ (Theory.PSL2.sl2_center_eq_bot F)
  intro a b h
  exact hf (congrArg (fun x : ElementaryGroup P => (x : fixedSubgroup P)) h)

/-- Identify the exact descended Levi from a faithful split-matrix embedding
whose image is the fixed part of the root-defined split Levi. The elementary
restriction and central-quotient kernel are conclusions, not hypotheses. -/
def leviEquivPSL2OfFixedEmbedding (P : Parameters) (a : Node)
    (hp : P.prime = 2) [CharP F 2]
    (f : SL(2, F) →* SplitGroup P) (hf : Function.Injective f)
    (hrange : f.range = splitLevi P a ⊓ fixedSubgroup P) :
    levi P a ≃* PSL(2, F) := by
  have hmem (g : SL(2, F)) : f g ∈ splitLevi P a ⊓ fixedSubgroup P :=
    hrange.le ⟨g, rfl⟩
  let f₀ : SL(2, F) →* fixedSubgroup P :=
    f.codRestrict (fixedSubgroup P) (fun g => (hmem g).2)
  let f₁ := sl2ElementaryLift P hp f₀
  let f₂ := (toCarrier P).comp f₁
  have hle (g : SL(2, F)) : f₂ g ∈ levi P a :=
    ⟨f₁ g, (hmem g).1, rfl⟩
  let e : SL(2, F) →* levi P a := f₂.codRestrict (levi P a) hle
  have he_inj : Function.Injective e := by
    intro g h he
    apply sl2_toCarrier_injective P hp f₀ (fun g h he => hf (congrArg Subtype.val he))
    exact congrArg Subtype.val he
  have he_surj : Function.Surjective e := by
    intro x
    obtain ⟨y, hy, hyx⟩ := x.property
    have hyf : elementaryInclusion P y ∈ f.range :=
      hrange.ge ⟨hy, (y : fixedSubgroup P).property⟩
    obtain ⟨g, hg⟩ := hyf
    refine ⟨g, Subtype.ext ?_⟩
    change toCarrier P (f₁ g) = x.val
    exact (congrArg (toCarrier P) (Subtype.ext (Subtype.ext hg))).trans hyx
  exact (MulEquiv.ofBijective e ⟨he_inj, he_surj⟩).symm.trans (Theory.PSL2.sl2QuotientEquiv F)

/-- The two-core conclusion, including the central binary-field case, once
the split fixed-point matrix embedding has been constructed. -/
theorem levi_twoCore_eq_bot_of_fixedEmbedding (P : Parameters) (a : Node)
    (hp : P.prime = 2) [CharP F 2] [Finite F]
    (f : SL(2, F) →* SplitGroup P) (hf : Function.Injective f)
    (hrange : f.range = splitLevi P a ⊓ fixedSubgroup P) :
    pCore 2 (levi P a) = ⊥ := by
  let e := (Theory.PSL2.sl2QuotientEquiv F).trans
    (leviEquivPSL2OfFixedEmbedding P a hp f hf hrange).symm
  rw [← pCore_map_iso 2 e, Matrix.SL2.twoCore_eq_bot F, Subgroup.map_bot]

private theorem sl2_isPerfect_of_two_lt_card [CharP F 2] [Finite F]
    (hcard : 2 < Nat.card F) : Group.IsPerfect SL(2, F) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have h3 : 3 ≤ Fintype.card F := by
    exact Nat.succ_le_of_lt (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨t, ht0, ht1⟩ := ENat.exists_ne_ne_of_three_le (α := F)
    (by rw [ENat.card_eq_coe_fintype_card]; exact_mod_cast h3) 0 1
  refine ⟨Matrix.SL2.commutator_eq_top ht0 ?_⟩
  intro h
  rcases sq_eq_one_iff.mp h with h | h
  · exact ht1 h
  · exact ht1 (by simpa only [CharTwo.neg_eq] using h)

/-- Perfectness requires more than two field elements. This does not assert
perfectness for the central Levi at q = 2. -/
theorem levi_isPerfect_of_fixedEmbedding (P : Parameters) (a : Node)
    (hp : P.prime = 2) [CharP F 2] [Finite F] (hcard : 2 < Nat.card F)
    (f : SL(2, F) →* SplitGroup P) (hf : Function.Injective f)
    (hrange : f.range = splitLevi P a ⊓ fixedSubgroup P) :
    Group.IsPerfect (levi P a) := by
  let : Group.IsPerfect SL(2, F) := sl2_isPerfect_of_two_lt_card hcard
  let e := (Theory.PSL2.sl2QuotientEquiv F).trans
    (leviEquivPSL2OfFixedEmbedding P a hp f hf hrange).symm
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective


/-- The arm Levi identification, conditional only on the two Geck matrix inputs. -/
def leviArmsEquivPSL2OfPinnedMaps (P : Parameters) (hp : P.prime = 2)
    (D : PinnedRankOneMaps P) (C : ArmRootCommutation P) :
    levi P .arms ≃* PSL(2, ExtensionField P) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  exact leviEquivPSL2OfFixedEmbedding P .arms hp (D.armsFixedEmbedding C)
    (D.armsFixedEmbedding_injective C) (D.range_armsFixedEmbedding C)

/-- The central Levi uses the base field, including the binary endpoint. -/
def leviCentralEquivPSL2OfPinnedMaps (P : Parameters) (hp : P.prime = 2)
    (D : PinnedRankOneMaps P) :
    levi P .central ≃* PSL(2, GaloisField P.prime P.exponent) := by
  let : CharP (GaloisField P.prime P.exponent) 2 :=
    hp ▸ inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
  exact leviEquivPSL2OfFixedEmbedding P .central hp D.centralFixedEmbedding
    D.centralFixedEmbedding_injective D.range_centralFixedEmbedding

theorem levi_arms_twoCore_eq_bot_of_pinnedMaps (P : Parameters) (hp : P.prime = 2)
    (D : PinnedRankOneMaps P) (C : ArmRootCommutation P) :
    pCore 2 (levi P .arms) = ⊥ := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  exact levi_twoCore_eq_bot_of_fixedEmbedding P .arms hp (D.armsFixedEmbedding C)
    (D.armsFixedEmbedding_injective C) (D.range_armsFixedEmbedding C)

theorem levi_central_twoCore_eq_bot_of_pinnedMaps (P : Parameters) (hp : P.prime = 2)
    (D : PinnedRankOneMaps P) : pCore 2 (levi P .central) = ⊥ := by
  let : CharP (GaloisField P.prime P.exponent) 2 :=
    hp ▸ inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
  exact levi_twoCore_eq_bot_of_fixedEmbedding P .central hp D.centralFixedEmbedding
    D.centralFixedEmbedding_injective D.range_centralFixedEmbedding

/-- The arm Levi is perfect even for q = 2, since its field has q³ ≥ 8 elements. -/
theorem levi_arms_isPerfect_of_pinnedMaps (P : Parameters) (hp : P.prime = 2)
    (D : PinnedRankOneMaps P) (C : ArmRootCommutation P) :
    Group.IsPerfect (levi P .arms) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  apply levi_isPerfect_of_fixedEmbedding P .arms hp ?_ (D.armsFixedEmbedding C)
    (D.armsFixedEmbedding_injective C) (D.range_armsFixedEmbedding C)
  rw [card_extensionField]
  exact lt_of_lt_of_le (by decide : 2 < 2 ^ 3) (Nat.pow_le_pow_left P.q_ge_two 3)

/-- Central perfectness has the necessary q > 2 restriction. -/
theorem levi_central_isPerfect_of_pinnedMaps (P : Parameters) (hp : P.prime = 2)
    (hq : 2 < P.q) (D : PinnedRankOneMaps P) :
    Group.IsPerfect (levi P .central) := by
  let : CharP (GaloisField P.prime P.exponent) 2 :=
    hp ▸ inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
  apply levi_isPerfect_of_fixedEmbedding P .central hp ?_ D.centralFixedEmbedding
    D.centralFixedEmbedding_injective D.range_centralFixedEmbedding
  simpa only [card_baseField] using hq

/-- The actual three-arm subsystem descends to PSL₂ over the q³-element field.
The rank-one maps, commuting factors, fixed-part range, and quotient kernel
are all proved from the specified Geck curves and graph-field action. -/
def leviArmsEquivPSL2 (P : Parameters) (hp : P.prime = 2) :
    levi P .arms ≃* PSL(2, ExtensionField P) :=
  leviArmsEquivPSL2OfPinnedMaps P hp (pinnedRankOneMaps P hp) (armRootCommutation P hp)

/-- The actual central-vertex subsystem descends to PSL₂ over the q-element
base field, using the proved identification with the q-Frobenius fixed field. -/
def leviCentralEquivPSL2 (P : Parameters) (hp : P.prime = 2) :
    levi P .central ≃* PSL(2, GaloisField P.prime P.exponent) :=
  leviCentralEquivPSL2OfPinnedMaps P hp (pinnedRankOneMaps P hp)

/-- The three-arm Levi has trivial two-core, including q = 2. -/
theorem levi_arms_twoCore_eq_bot (P : Parameters) (hp : P.prime = 2) :
    pCore 2 (levi P .arms) = ⊥ :=
  levi_arms_twoCore_eq_bot_of_pinnedMaps P hp
    (pinnedRankOneMaps P hp) (armRootCommutation P hp)

/-- The central Levi has trivial two-core even at the binary endpoint. -/
theorem levi_central_twoCore_eq_bot (P : Parameters) (hp : P.prime = 2) :
    pCore 2 (levi P .central) = ⊥ :=
  levi_central_twoCore_eq_bot_of_pinnedMaps P hp (pinnedRankOneMaps P hp)

/-- Both exact root-defined Levi subgroups have trivial two-core. -/
theorem levi_twoCore_eq_bot (P : Parameters) (a : Node) (hp : P.prime = 2) :
    pCore 2 (levi P a) = ⊥ := by
  cases a with
  | arms => exact levi_arms_twoCore_eq_bot P hp
  | central => exact levi_central_twoCore_eq_bot P hp

/-- The arm Levi is perfect for every characteristic-two parameter, since
its coefficient field has q³ ≥ 8 elements. -/
theorem levi_arms_isPerfect (P : Parameters) (hp : P.prime = 2) :
    Group.IsPerfect (levi P .arms) :=
  levi_arms_isPerfect_of_pinnedMaps P hp
    (pinnedRankOneMaps P hp) (armRootCommutation P hp)

/-- Central perfectness retains the necessary exclusion of PSL₂(2). -/
theorem levi_central_isPerfect (P : Parameters) (hp : P.prime = 2)
    (hq : 2 < P.q) : Group.IsPerfect (levi P .central) :=
  levi_central_isPerfect_of_pinnedMaps P hp hq (pinnedRankOneMaps P hp)

/-- For q > 2, both actual Levi subgroups are perfect. -/
theorem levi_isPerfect (P : Parameters) (a : Node) (hp : P.prime = 2)
    (hq : 2 < P.q) : Group.IsPerfect (levi P a) := by
  cases a with
  | arms => exact levi_arms_isPerfect P hp
  | central => exact levi_central_isPerfect P hp hq

end Triality.Standard.Parabolics
