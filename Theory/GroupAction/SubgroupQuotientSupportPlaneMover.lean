module
public import Theory.GroupAction.SubgroupQuotientLineNormalizer
public import Theory.GroupTheory.CardFourAutomorphismStabilizer

/-!
# Lift a faithful order-three support action to a plane mover

For a supplied literal conjugation action on U/Z, suppose a subgroup of its
actual action range has order three and acts faithfully on an invariant
support of order four. For any order-two line in that support, some actual
mover in P normalizes the ambient lift of the support but not the lift of
the line. The original quotient and action instances are retained.

Restricting to the support gives an automorphism image of order three.
It cannot fix the nonidentity line point, since its stabilizer in the
automorphism group of a four-element group has order at most two. Lift
such an actor through the actual range. The support-conjugation identity
and lifted-line normalizer formula give the two ambient conclusions.

This source-neutral action transfer is used for the extraspecial-order27
obstruction in Stellmacher (10.1), printed p.63, before equation (14), in
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Subgroup

public theorem exists_normalizer_support_not_line_of_faithful_three
    {G : Type*} [Group G] (P U Z : Subgroup G)
    (hPU : P ≤ normalizer (U : Set G))
    [hN : (Z.subgroupOf U).Normal]
    (action : P →* MulAut (U ⧸ Z.subgroupOf U))
    (hact : ∀ mover : P, ∀ point : U,
      action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
        QuotientGroup.mk' (Z.subgroupOf U)
          ⟨(mover:G)*(point:G)*(mover:G)⁻¹,
            (mem_normalizer_iff.mp (hPU mover.property) point).mp point.property⟩)
    (B : Subgroup (U ⧸ Z.subgroupOf U)) (hB : Nat.card B = 4)
    (C : Subgroup (MulAut (U ⧸ Z.subgroupOf U))) (hC : Nat.card C = 3)
    (hCR : C ≤ action.range)
    (hstable : ∀ c : C, B.map (c : MulAut (U ⧸ Z.subgroupOf U)).toMonoidHom = B)
    (hfaith : ∀ c : C, (∀ v ∈ B, (c : MulAut (U ⧸ Z.subgroupOf U)) v = v) → c = 1)
    (line : Subgroup (U ⧸ Z.subgroupOf U)) (hline : Nat.card line = 2)
    (hlineB : line ≤ B) :
    let q := QuotientGroup.mk' (Z.subgroupOf U)
    ∃ mover : P, (mover:G) ∈ normalizer (((B.comap q).map U.subtype : Subgroup G) : Set G) ∧
      (mover:G) ∉ normalizer (((line.comap q).map U.subtype : Subgroup G) : Set G) := by
  classical
  let W := U ⧸ Z.subgroupOf U
  let _ : Finite B := Nat.finite_of_card_ne_zero (by omega)
  let rho : C →* MulAut B := {
    toFun c := ((c:MulAut W).subgroupMap B).trans (MulEquiv.subgroupCongr (hstable c))
    map_one' := by ext v; rfl
    map_mul' := by intro a b; ext v; rfl }
  have hrho (c : C) (v : B) : (rho c v : W) = (c:MulAut W) v := rfl
  have hinj : Function.Injective rho := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro c hc
    apply hfaith
    intro v hv
    have hh := congrArg Subtype.val (MulEquiv.congr_fun (MonoidHom.mem_ker.mp hc) (⟨v,hv⟩:B))
    exact hh
  obtain ⟨r,hr,_⟩ := (Nat.card_eq_two_iff' (1:line)).mp hline
  let rB : B := ⟨r,hlineB r.property⟩
  have hrB : rB ≠ 1 := by
    intro hh
    exact hr (Subtype.ext (congrArg (fun v : B => (v:W)) hh))
  have hmove : ∃ c : C, (c:MulAut W) r ≠ r := by
    by_contra! hfixed
    have hbound := card_mulAut_subgroup_le_two_of_fixed_point hB rB hrB rho.range (by
      rintro f ⟨c,rfl⟩
      apply Subtype.ext
      exact hfixed c)
    have hcard : Nat.card rho.range = 3 := by
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hC
    omega
  obtain ⟨c,hc⟩ := hmove
  obtain ⟨mover,hmover⟩ := hCR c.property
  have hnormal : (mover:G) ∈ normalizer
      (((B.comap (QuotientGroup.mk' (Z.subgroupOf U))).map U.subtype : Subgroup G) : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hh := lift_support_conjugate P U Z hPU action hact B mover
    dsimp only at hh
    rw [hmover,hstable c] at hh
    exact hh
  refine ⟨mover,hnormal,?_⟩
  intro hnormalLine
  have heq := lift_line_normalizer_eq_comap_stabilizer P U Z hPU hN action hact
    line hline r r.property (fun hh => hr (Subtype.ext hh))
  have hmem : mover ∈ (normalizer
      (((line.comap (QuotientGroup.mk' (Z.subgroupOf U))).map U.subtype : Subgroup G) : Set G)).subgroupOf P :=
    hnormalLine
  rw [heq] at hmem
  have hfixed := MulAction.mem_stabilizer_iff.mp hmem
  change action mover r = r at hfixed
  exact hc (hmover ▸ hfixed)

end Subgroup
