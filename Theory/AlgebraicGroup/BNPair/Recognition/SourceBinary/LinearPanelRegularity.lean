module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PanelKernel
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal

/-!
# Regularity of a normal two-group on a punctured linear panel

A normal p-group in a faithful primitive action is semiregular: its
nontrivial characteristic center is transitive, and every point stabilizer
centralizes that transitive center. Passing to the permutation image gives
the corresponding kernel statement without faithfulness. The result is
transported through explicit equivariant panel bijections.

For the actual marked parabolic, the canonical simple remainder fixes both
the base Borel coset and the inverse-simple-lift coset. If the Borel is
doubly transitive off its base point, regularity puts the entire remainder
in the full panel kernel. No perfectness or Weyl-order restriction is used.
The linear model and original source applications discharge double
transitivity in the companion modules.

Source: Fong--Seitz I (2A)--(2B), printed pp.7--9. This is the linear
local-action route, and does not assert the regularity of the type VI
exception or of arbitrary local models.
-/

public noncomputable section
open Subgroup MulAction
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelKernel

/-- A normal finite p-group in a faithful primitive action has no nonidentity
point stabilizers. Its characteristic center is transitive. -/
theorem normal_pGroup_semiregular {A Ω : Type*} [Group A] [Finite A]
    [MulAction A Ω] [FaithfulSMul A Ω] [IsPreprimitive A Ω]
    {p : ℕ} [Fact p.Prime] (U : Subgroup A) [U.Normal] (hp : IsPGroup p U)
    (u : U) (x : Ω) (hx : (u : A) • x = x) : u = 1 := by
  by_cases hU : U = ⊥
  · exact Subtype.ext (mem_bot.mp (hU ▸ u.property))
  let : Nontrivial U := (nontrivial_iff_ne_bot U).mpr hU
  let : Nontrivial (center U) := hp.center_nontrivial
  let Z := (center U).map U.subtype
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZ : Z ≠ ⊥ := by
    intro hz
    have he : center U = ⊥ := (map_eq_bot_iff_of_injective _ U.subtype_injective).mp hz
    exact (nontrivial_iff_ne_bot (center U)).mp inferInstance he
  let : IsPretransitive Z Ω := Atlas.GroupTheory.normal_pretransitive Z hZ
  apply Subtype.ext
  apply eq_of_smul_eq_smul (α := Ω)
  intro y
  obtain ⟨z,hz⟩ := exists_smul_eq Z x y
  obtain ⟨z',hz',he⟩ := z.property
  have hc : (u : A) * (z : A) = (z : A) * u := by
    rw [← he]
    exact congrArg Subtype.val ((mem_center_iff.mp hz') u)
  rw [← hz]
  change (u : A) • ((z : A) • x) = (1 : A) • ((z : A) • x)
  rw [← mul_smul, hc, mul_smul, hx, one_smul]

/-- Without faithfulness, a normal finite p-group element fixing one point
fixes every point of a doubly transitive action. -/
theorem normal_pGroup_fixed_all {A Ω : Type*} [Group A] [Finite A]
    [MulAction A Ω] (htwo : IsMultiplyPretransitive A Ω 2)
    {p : ℕ} [Fact p.Prime] (U : Subgroup A) [U.Normal] (hp : IsPGroup p U)
    (u : U) (x : Ω) (hx : (u : A) • x = x) (y : Ω) : (u : A) • y = y := by
  let f := MulAction.toPermHom A Ω
  let E := f.range
  let g : A →* E := f.rangeRestrict
  let : Finite E := Finite.of_surjective g f.rangeRestrict_surjective
  let R := U.map g
  let : R.Normal := (inferInstance : U.Normal).map g f.rangeRestrict_surjective
  have ht : IsMultiplyPretransitive E Ω 2 := is_two_pretransitive_iff.mpr (by
    intro a b c d hab hcd
    obtain ⟨s,hs,hs'⟩ := is_two_pretransitive_iff.mp htwo hab hcd
    exact ⟨g s,hs,hs'⟩)
  let : IsPreprimitive E Ω := isPreprimitive_of_is_two_pretransitive ht
  have he := normal_pGroup_semiregular R (hp.map g)
    ⟨g u,mem_map_of_mem g u.property⟩ x hx
  have he' : g u = 1 := congrArg Subtype.val he
  exact congrArg (fun a : E => a • y) he'

variable {A Ω : Type*} [Group A] [MulAction A Ω]

/-- The full ordered-pair action away from the specified point. -/
@[expose] def TwoTransitiveOff (B : Subgroup A) (o : Ω) : Prop :=
  ∀ a b c d : Ω, a ≠ o → b ≠ o → c ≠ o → d ≠ o → a ≠ b → c ≠ d →
    ∃ g ∈ B, g • a = c ∧ g • b = d

/-- Transport ordered pairs through the same action and subgroup image. -/
theorem TwoTransitiveOff.pullback {H Δ : Type*} [Group H] [MulAction H Δ]
    {B : Subgroup A} {C : Subgroup H} {o : Ω} {t : Δ}
    (f : A →* H) (e : Ω ≃ Δ) (hmap : B.map f = C)
    (he : ∀ a x, e (a • x) = f a • e x) (ho : e o = t)
    (ht : TwoTransitiveOff C t) : TwoTransitiveOff B o := by
  intro a b c d hao hbo hco hdo hab hcd
  have hne (x : Ω) (hx : x ≠ o) : e x ≠ t := fun h => hx (e.injective (h.trans ho.symm))
  obtain ⟨g,hg,hga,hgb⟩ := ht (e a) (e b) (e c) (e d)
    (hne a hao) (hne b hbo) (hne c hco) (hne d hdo)
    (fun h => hab (e.injective h)) (fun h => hcd (e.injective h))
  have hg' : g ∈ B.map f := hmap.symm ▸ hg
  obtain ⟨b,hb,hbg⟩ := hg'
  refine ⟨b,hb,?_,?_⟩
  · apply e.injective
    rw [he,hbg,hga]
  · apply e.injective
    rw [he,hbg,hgb]

/-- Push forward an ordered-pair action through an equivariant bijection. -/
theorem TwoTransitiveOff.pushforward {H Δ : Type*} [Group H] [MulAction H Δ]
    {B : Subgroup A} {C : Subgroup H} {o : Ω} {t : Δ}
    (f : A →* H) (e : Ω ≃ Δ) (hmap : B.map f ≤ C)
    (he : ∀ a x, e (a • x) = f a • e x) (ho : e o = t)
    (ht : TwoTransitiveOff B o) : TwoTransitiveOff C t := by
  intro a b c d hao hbo hco hdo hab hcd
  obtain ⟨a,rfl⟩ := e.surjective a
  obtain ⟨b,rfl⟩ := e.surjective b
  obtain ⟨c,rfl⟩ := e.surjective c
  obtain ⟨d,rfl⟩ := e.surjective d
  have hne (x : Ω) (hx : e x ≠ t) : x ≠ o := fun h => hx (h ▸ ho)
  obtain ⟨g,hg,hga,hgb⟩ := ht a b c d (hne a hao) (hne b hbo)
    (hne c hco) (hne d hdo) (fun h => hab (congrArg e h)) (fun h => hcd (congrArg e h))
  refine ⟨f g,hmap (mem_map_of_mem f hg),?_,?_⟩
  · rw [← he,hga]
  · rw [← he,hgb]

@[instance_reducible] private def offAction (B : Subgroup A) (o : Ω) (hfix : ∀ b ∈ B, b • o = o) :
    MulAction B {x : Ω // x ≠ o} where
  smul b x := ⟨(b : A) • x, fun he => x.property
    ((MulAction.injective _ : Function.Injective (fun x : Ω => (b : A) • x))
      (he.trans (hfix b b.property).symm))⟩
  one_smul x := Subtype.ext (one_smul A x.val)
  mul_smul b c x := Subtype.ext (mul_smul (b : A) (c : A) x.val)

/-- A two-element stabilizer in the normal p-group is already in the full
permutation kernel when the Borel is doubly transitive off its fixed point. -/
theorem normal_pGroup_fixed_off [Finite A]
    {p : ℕ} [Fact p.Prime] (B U : Subgroup A) (hUB : U ≤ B)
    (hn : B ≤ normalizer (U : Set A)) (hp : IsPGroup p U)
    (o : Ω) (hfix : ∀ b ∈ B, b • o = o) (htwo : TwoTransitiveOff B o)
    (u : A) (hu : u ∈ U) (x : Ω) (hxo : x ≠ o) (hx : u • x = x)
    (y : Ω) : u • y = y := by
  by_cases hy : y = o
  · subst y; exact hfix u (hUB hu)
  let := offAction B o hfix
  have ht : IsMultiplyPretransitive B {x : Ω // x ≠ o} 2 :=
    is_two_pretransitive_iff.mpr (by
      intro a b c d hab hcd
      obtain ⟨g,hg,hga,hgb⟩ := htwo a b c d a.property b.property c.property d.property
        (fun he => hab (Subtype.ext he)) (fun he => hcd (Subtype.ext he))
      exact ⟨⟨g,hg⟩,Subtype.ext hga,Subtype.ext hgb⟩)
  let V := U.subgroupOf B
  let : V.Normal := normal_subgroupOf_of_le_normalizer hn
  have he := normal_pGroup_fixed_all ht V hp.comap_subtype
    ⟨⟨u,hUB hu⟩,hu⟩ ⟨x,hxo⟩ (Subtype.ext hx) ⟨y,hy⟩
  exact congrArg Subtype.val he

open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Fong--Seitz (2B) for an endpoint whose full Borel is doubly transitive
on the punctured panel. The local kernel and simple lift remain literal. -/
theorem remainder_le_kernel_of_two_transitive_off (i : Fin 2)
    (htwo : TwoTransitiveOff
      (Q.tits.B.subgroupOf (Q.tits.standardParabolic {Q.simple i})) (QuotientGroup.mk 1 : Panel Q i)) :
    simpleRemainder Q split i ≤ localKernel Q i := by
  let M := Q.tits.standardParabolic {Q.simple i}
  let B := Q.tits.B.subgroupOf M
  let U := split.U.subgroupOf M
  have hUM : split.U ≤ M := split.U_le.trans (Q.tits.B_le_standardParabolic _)
  have hnU : B ≤ normalizer (U : Set M) := fun b hb =>
    split.U.le_normalizer_comap M.subtype (split.normalizes hb)
  have hfix : ∀ b ∈ B, b • (QuotientGroup.mk 1 : Panel Q i) = QuotientGroup.mk 1 := by
    intro b hb
    change QuotientGroup.mk (b*1) = (QuotientGroup.mk 1 : M ⧸ B)
    apply QuotientGroup.eq.mpr
    simpa only [mul_one] using B.inv_mem hb
  let n := representative (Q.simple i)
  have hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n⁻¹ = Q.simple i := by
    rw [map_inv,representative_spec]
    exact inv_eq_of_mul_eq_one_right
      (by simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2)
  let β := simplePanelMap Q split i n⁻¹ hn 1
  have hnM : ((n : X ⧸ Q.D)⁻¹) ∈ M :=
    Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
      (Q.tits.representative_mem_bruhatCell _ n⁻¹ hn)
  have hβ : β.val = QuotientGroup.mk (⟨(n : X ⧸ Q.D)⁻¹,hnM⟩ : M) := by
    rw [simplePanelMap_apply Q split i n⁻¹ hn 1 (by simpa only [Subgroup.coe_one, one_mul, Subgroup.coe_inv] using hnM)]
    congr 1
    apply Subtype.ext
    exact one_mul _
  have hβne : β.val ≠ (QuotientGroup.mk 1 : Panel Q i) := by
    intro he
    rw [hβ] at he
    have hb : ((n : X ⧸ Q.D)⁻¹) ∈ Q.tits.B := by
      have hb' : (⟨(n : X ⧸ Q.D)⁻¹,hnM⟩ : M) ∈ B := by
        simpa only [inv_one,one_mul] using (QuotientGroup.eq.mp he.symm)
      exact hb'
    have he' : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n⁻¹ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨hb,(n⁻¹).property⟩
    exact (Q.tits.involutions _ (Q.simple_mem i)).1 (hn.symm.trans he')
  intro v hv
  let vM : M := ⟨v,hUM hv.1⟩
  have hvβ : vM • β.val = β.val := by
    rw [hβ]
    symm
    apply QuotientGroup.eq.mpr
    change ((n : X ⧸ Q.D)⁻¹)⁻¹ * (v * (n : X ⧸ Q.D)⁻¹) ∈ Q.tits.B
    rw [inv_inv, ← mul_assoc]
    exact split.U_le hv.2
  refine ⟨vM, ?_, rfl⟩
  rw [normalCore_eq_ker]
  change MulAction.toPermHom M (Panel Q i) vM = 1
  apply Equiv.ext
  intro c
  exact normal_pGroup_fixed_off B U (subgroupOf_mono _ split.U_le) hnU
    split.isTwo.comap_subtype (QuotientGroup.mk 1 : Panel Q i) hfix htwo vM hv.1 β.val hβne hvβ c

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelKernel
