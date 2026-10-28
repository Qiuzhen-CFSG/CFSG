module

public import Theory.SpecificGroups.FifteenPointSubgroups.Orders
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.GroupAction.CosetTransport
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.GraphDuality
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# The fifteen-point coset action in PSL₄(2)

An index-fifteen subgroup with two-core of order eight is the stabilizer of
an endpoint subspace of the natural binary four-space. Transport the actual
intrinsic core through the matrix-model equivalence; its common fixed space
is nonzero, proper, and invariant under the subgroup. The subgroup has order
1344, so it contains an element of order seven. Fixed-point counting for this
element excludes every invariant two-plane, leaving a line or a hyperplane.

A line stabilizer acts on the fifteen projective points, where the linear
group is two-transitive. The proved inverse-transpose formula carries a
hyperplane stabilizer to a line stabilizer. Both parabolics therefore have
index fifteen, and the subgroup containment is equality by orders. Finally
transport the literal left-coset action back to PSL₄(2).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.4.12(2), printed p.97 / PDF p.108 of `refs/quasithin.pdf`. The group-order
input comes from the attributed ATLAS comparison imported by `Orders`.
-/

@[expose] public section

open scoped MatrixGroups
open BinaryLinear BinaryLinear.OuterCyclic Subgroup
namespace FifteenPointSubgroups.LinearFour
abbrev V := Space 4
abbrev L := LinearGroup 4
/-- The actual binary matrix action of the central quotient PSL₄(2). -/
noncomputable def modelEquiv : PSL(4, ZMod 2) ≃* L := projectiveEquivLinear (by decide)
private instance : Finite L := Finite.of_equiv PSL(4, ZMod 2) modelEquiv.toEquiv

private theorem fixedSpace_seven_card (Q : Subgroup L) (hQ : IsPGroup 7 Q)
    (hQ0 : Q ≠ ⊥) : Nat.card (fixedSpace Q) = 2 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have he : MulAction.fixedPoints Q V = (fixedSpace Q : Set V) := by
    ext v
    rw [MulAction.mem_fixedPoints]
    change (∀ q : Q, q.val v = v) ↔ ∀ q ∈ Q, q v = v
    exact ⟨fun h q hq => h ⟨q, hq⟩, fun h q => h q.val q.property⟩
  have hc := hQ.card_modEq_card_fixedPoints V
  rw [he] at hc
  change Nat.card V ≡ Nat.card (fixedSpace Q) [MOD 7] at hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace Q)] at hc
  norm_num [V, Space] at hc
  have hd := Submodule.finrank_lt (fixedSpace_ne_top hQ0)
  norm_num [V, Space] at hd
  have hd1 : Module.finrank (ZMod 2) (fixedSpace Q) = 1 := by
    interval_cases hh : Module.finrank (ZMod 2) (fixedSpace Q) <;>
      first | rfl | norm_num [Nat.ModEq, hh] at hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hd1]
  norm_num

private abbrev invariantAction (Q : Subgroup L)
    (W : Submodule (ZMod 2) V) (hW : Q ≤ parabolic W) : MulAction Q W where
  smul q w := ⟨q.val w.val, (hW q.property w.val).mpr w.property⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl

private theorem invariant_plane_impossible (Q : Subgroup L) (hQ : IsPGroup 7 Q)
    (hc : Nat.card (fixedSpace Q) = 2) (W : Submodule (ZMod 2) V)
    (hW : Q ≤ parabolic W) : Module.finrank (ZMod 2) W ≠ 2 := by
  intro hd
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : MulAction Q W := invariantAction Q W hW
  let toFixed : MulAction.fixedPoints Q W → fixedSpace Q := fun x =>
    ⟨x.val.val, fun q hq => congrArg Subtype.val
      ((MulAction.mem_fixedPoints.mp x.property) ⟨q, hq⟩)⟩
  have hinj : Function.Injective toFixed := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun x : fixedSpace Q => x.val) he))
  have hle := Nat.card_le_card_of_injective toFixed hinj
  rw [hc] at hle
  have hWcard : Nat.card W = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hd]
    norm_num
  have hr := hQ.card_modEq_card_fixedPoints W
  change Nat.card W ≡ Nat.card (MulAction.fixedPoints Q W) [MOD 7] at hr
  rw [hWcard] at hr
  change 4 % 7 = Nat.card (MulAction.fixedPoints Q W) % 7 at hr
  omega

/-- A subgroup with order divisible by seven has no invariant two-plane. -/
theorem invariant_finrank_endpoints (K : Subgroup L) (hseven : 7 ∣ Nat.card K)
    (W : Submodule (ZMod 2) V) (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
    (hKW : K ≤ parabolic W) :
    Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 3 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 7 hseven
  let Q : Subgroup L := zpowers g.val
  have hQc : Nat.card Q = 7 := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective K.subtype K.subtype_injective g).trans hg
  have hQ : IsPGroup 7 Q := IsPGroup.of_card (n := 1) (by simpa using hQc)
  have hQ0 : Q ≠ ⊥ := by
    intro he
    rw [he, Subgroup.card_bot] at hQc
    omega
  have hQK : Q ≤ K := zpowers_le.mpr g.property
  have hne := invariant_plane_impossible Q hQ (fixedSpace_seven_card Q hQ hQ0) W
    (hQK.trans hKW)
  have hlo : 0 < Module.finrank (ZMod 2) W := Nat.pos_of_ne_zero (fun h => hW0 (Submodule.finrank_eq_zero.mp h))
  have hhi := Submodule.finrank_lt hWt
  norm_num [V, Space] at hhi
  omega

/-- The fixed space of the intrinsic two-core supplies an invariant endpoint. -/
theorem exists_invariant_endpoint (K : Subgroup L) (hseven : 7 ∣ Nat.card K)
    (hcore : Nat.card (pCore 2 K) = 8) :
    ∃ W : Submodule (ZMod 2) V, K ≤ parabolic W ∧
      (Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 3) := by
  let Q : Subgroup L := (pCore 2 K).map K.subtype
  have hQ : IsPGroup 2 Q := pCore_isPGroup.map K.subtype
  have hc : Nat.card Q = 8 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hcore
  have hQ0 : Q ≠ ⊥ := by
    intro he
    rw [he, Subgroup.card_bot] at hc
    omega
  have hnorm : K ≤ Subgroup.normalizer (Q : Set L) := by
    have hh := (pCore 2 K).le_normalizer_map K.subtype
    simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, K.range_subtype]
      using hh
  have hW0 : fixedSpace Q ≠ ⊥ := fixedSpace_ne_bot (by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
    norm_num [V, Space]) hQ
  have hWt : fixedSpace Q ≠ ⊤ := fixedSpace_ne_top hQ0
  have hKW := hnorm.trans (normalizer_le_parabolic_fixedSpace Q)
  exact ⟨fixedSpace Q, hKW, invariant_finrank_endpoints K hseven _ hW0 hWt hKW⟩

/-- The original index and core hypotheses force endpoint containment. -/
theorem psl4_exists_invariant_endpoint (H : Subgroup PSL(4, ZMod 2))
    (hi : H.index = 15) (hc : Nat.card (pCore 2 H) = 8) :
    ∃ W : Submodule (ZMod 2) V,
      H.map modelEquiv.toMonoidHom ≤ parabolic W ∧
      (Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 3) := by
  let K := H.map modelEquiv.toMonoidHom
  have horder : Nat.card H = 1344 := by
    have hh := H.card_mul_index
    rw [hi, Atlas.Order20160A8.psl4Two_card] at hh
    omega
  have hseven : 7 ∣ Nat.card K := by
    rw [Subgroup.card_map_of_injective modelEquiv.injective, horder]
    decide
  have hcore : Nat.card (pCore 2 K) = 8 := by
    let e : H ≃* K := modelEquiv.subgroupMap H
    have he : (pCore 2 H).map e.toMonoidHom = pCore 2 K := pCore_map_iso 2 e
    rw [← he, Subgroup.card_map_of_injective e.injective]
    exact hc
  exact exists_invariant_endpoint K hseven hcore

open scoped LinearAlgebra.Projectivization
open BinaryLinear.InvariantNodeActions

private theorem projective_smul_submodule (g : L) (D : ℙ (ZMod 2) V) :
    (g • D).submodule = D.submodule.map g.toLinearMap := by
  rw [← Projectivization.mk_rep D, Projectivization.smul_mk,
    Projectivization.submodule_mk, Projectivization.submodule_mk,
    Submodule.map_span, Set.image_singleton]
  rfl

private theorem parabolic_eq_projective_stabilizer (D : ℙ (ZMod 2) V) :
    parabolic D.submodule = MulAction.stabilizer L D := by
  ext g
  change (∀ v, g v ∈ D.submodule ↔ v ∈ D.submodule) ↔ g • D = D
  constructor
  · intro hg
    apply Projectivization.submodule_injective
    rw [projective_smul_submodule]
    ext v
    rw [Submodule.mem_map_equiv]
    simpa only [LinearEquiv.apply_symm_apply] using (hg (g.symm v)).symm
  · intro hg v
    have he := congrArg Projectivization.submodule hg
    rw [projective_smul_submodule] at he
    calc
      g v ∈ D.submodule ↔ g v ∈ D.submodule.map g.toLinearMap := by rw [he]
      _ ↔ v ∈ D.submodule := by
        simp only [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

private theorem projective_stabilizer_action (D : ℙ (ZMod 2) V) :
    (MulAction.stabilizer L D).index = 15 ∧
    MulAction.IsMultiplyPretransitive L (L ⧸ MulAction.stabilizer L D) 2 := by
  let f := MulAction.ofQuotientStabilizer L D
  have hf : Function.Injective f := MulAction.injective_ofQuotientStabilizer L D
  have htwo : MulAction.IsMultiplyPretransitive L (ℙ (ZMod 2) V) 2 := inferInstance
  have : MulAction.IsPretransitive L (ℙ (ZMod 2) V) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L D x
    exact ⟨QuotientGroup.mk g, hg⟩
  constructor
  · change Nat.card (L ⧸ MulAction.stabilizer L D) = 15
    rw [Nat.card_congr (Equiv.ofBijective f ⟨hf, hsurj⟩), Projectivization.card'']
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
    norm_num [V, Space]
  · apply MulAction.is_two_pretransitive_iff.mpr
    intro a b c d hab hcd
    obtain ⟨g, hga, hgb⟩ := MulAction.is_two_pretransitive_iff.mp htwo
      (hf.ne hab) (hf.ne hcd)
    exact ⟨g, hf (by simpa only [f, MulAction.ofQuotientStabilizer_smul] using hga),
      hf (by simpa only [f, MulAction.ofQuotientStabilizer_smul] using hgb)⟩

private theorem line_parabolic_action (W : Submodule (ZMod 2) V)
    (hd : Module.finrank (ZMod 2) W = 1) :
    (parabolic W).index = 15 ∧
    MulAction.IsMultiplyPretransitive L (L ⧸ parabolic W) 2 := by
  rw [← Projectivization.submodule_mk'' W hd, parabolic_eq_projective_stabilizer]
  exact projective_stabilizer_action _

/-- Each endpoint parabolic has index fifteen and a two-transitive coset action. -/
theorem endpoint_parabolic_action (W : Submodule (ZMod 2) V)
    (hd : Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 3) :
    (parabolic W).index = 15 ∧
    MulAction.IsMultiplyPretransitive L (L ⧸ parabolic W) 2 := by
  rcases hd with hd | hd
  · exact line_parabolic_action W hd
  · have hline : Module.finrank (ZMod 2) (flagOrthogonal W) = 1 := by
      rw [flagOrthogonal_finrank, hd]
    obtain ⟨hi, ht⟩ := line_parabolic_action (flagOrthogonal W) hline
    have hm := graph_map_parabolic W
    constructor
    · have he := Nat.card_congr (Subgroup.cosetEquivMap (graphLinear 4) (parabolic W))
      change (parabolic W).index = ((parabolic W).map (graphLinear 4).toMonoidHom).index at he
      rw [hm] at he
      exact he.trans hi
    · apply Subgroup.two_pretransitive_of_map (graphLinear 4)
      rwa [hm]

/-- Under the actual model equivalence, the original subgroup is a full endpoint parabolic. -/
theorem psl4_eq_endpoint_parabolic (H : Subgroup PSL(4, ZMod 2))
    (hi : H.index = 15) (hc : Nat.card (pCore 2 H) = 8) :
    ∃ W : Submodule (ZMod 2) V,
      H.map modelEquiv.toMonoidHom = parabolic W ∧
      (Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 3) := by
  obtain ⟨W, hle, hd⟩ := psl4_exists_invariant_endpoint H hi hc
  refine ⟨W, Subgroup.eq_of_le_of_card_ge hle ?_, hd⟩
  have hH := (H.map modelEquiv.toMonoidHom).card_mul_index
  have hP := (parabolic W).card_mul_index
  rw [Subgroup.index_map_of_bijective modelEquiv.bijective, hi] at hH
  rw [(endpoint_parabolic_action W hd).1] at hP
  have he : Nat.card (parabolic W) = Nat.card (H.map modelEquiv.toMonoidHom) :=
    Nat.eq_of_mul_eq_mul_right (by decide : 0 < 15) (hP.trans hH.symm)
  exact he.le
end FifteenPointSubgroups.LinearFour

namespace FifteenPointSubgroups
open LinearFour

/-- The literal degree-fifteen left-coset action required in B.4.12(2). -/
theorem psl4_two_pretransitive (H : Subgroup PSL(4, ZMod 2))
    (hi : H.index = 15) (hc : Nat.card (pCore 2 H) = 8) :
    MulAction.IsMultiplyPretransitive PSL(4, ZMod 2) (PSL(4, ZMod 2) ⧸ H) 2 := by
  obtain ⟨W, hH, hd⟩ := psl4_eq_endpoint_parabolic H hi hc
  apply Subgroup.two_pretransitive_of_map modelEquiv H
  rw [hH]
  exact (endpoint_parabolic_action W hd).2
end FifteenPointSubgroups
