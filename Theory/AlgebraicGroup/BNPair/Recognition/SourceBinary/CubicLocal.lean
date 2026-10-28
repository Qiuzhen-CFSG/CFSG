module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PanelKernel
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorPanels
public import Theory.GroupTheory.CentralCoprimeCardLift
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Recognition of the actual cubic root group

If the canonical simple root has order two, the full local remainder
lies in the panel kernel by index-two normality. The two-root actor is
doubly transitive on the literal three-element panel, hence its image
is its whole symmetric group. The odd central kernel of its local cover
is trivial: its two involutory generators lift the two transpositions,
the cube of their product is central and inverted, and oddness kills it.
The dihedral relations therefore bound the root group by six elements;
its full symmetric image has six elements, proving faithfulness.

The resulting equivalence is the original permutation action, not an
unmarked order-six tag. The two-part of the panel kernel is also proved
to equal the embedded parabolic two-core, distinguishing it from the
full kernel. No perfectness is used.

Source: Fong--Seitz I (2B), p.9, and the binary linear case of (5C)(b),
pp.25--26. The elementary dihedral calculation replaces a general Schur
multiplier argument for this one local cover. The type VI alternative
and noncubic local groups remain outside this theorem.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelKernel
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The two-part of the full panel kernel is the embedded parabolic two-core. -/
theorem radical_eq_parabolic_twoCore (i : Fin 2) :
    LocalCover.radical Q split i =
      (pCore 2 (Q.tits.standardParabolic {Q.simple i})).map
        (Q.tits.standardParabolic {Q.simple i}).subtype := by
  let M := Q.tits.standardParabolic {Q.simple i}
  have hUM : split.U ≤ M := split.U_le.trans (Q.tits.B_le_standardParabolic _)
  have hcoreU : pCore 2 M ≤ split.U.subgroupOf M :=
    pCore_isPGroup.le_sylow_of_normal (split.sylow.subtype hUM)
  have hcoreK : pCore 2 M ≤ (Q.tits.B.subgroupOf M).normalCore :=
    normal_le_normalCore.mpr (hcoreU.trans (subgroupOf_mono _ split.U_le))
  apply le_antisymm
  · let V := (LocalCover.radical Q split i).subgroupOf M
    let : V.Normal := normal_subgroupOf_of_le_normalizer
      (LocalCover.radical_parabolic_normalizes Q split i)
    have hV : V ≤ pCore 2 M := le_sSup ⟨inferInstance,
      (split.isTwo.of_injective (inclusion
        (show LocalCover.radical Q split i ≤ split.U from inf_le_left))
          (inclusion_injective _)).comap_subtype⟩
    intro x hx
    exact ⟨⟨x,hUM hx.1⟩,hV hx,rfl⟩
  · rintro x ⟨y,hy,rfl⟩
    exact ⟨hcoreU hy,⟨y,hcoreK hy,rfl⟩⟩

theorem panel_card_three (i : Fin 2) (hc : Nat.card (simpleRoot Q split i) = 2) :
    Nat.card (Panel Q i) = 3 := by
  change (Q.tits.B.subgroupOf (Q.tits.standardParabolic {Q.simple i})).index = 3
  rw [singleton_parabolic_root_index, hc]

theorem cubic_localGroup_eq_top (i : Fin 2)
    (hc : Nat.card (simpleRoot Q split i) = 2) :
    localGroup Q split i = ⊤ := by
  apply Equiv.Perm.eq_top_of_isMultiplyPretransitive
  rw [panel_card_three Q split i hc]
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  have ht := UnitarySource.panelActor_two_pretransitive Q split i
  obtain ⟨r,hr,hs⟩ := MulAction.is_two_pretransitive_iff.mp ht hab hcd
  let r' : localClosure Q split i :=
    ⟨r.val.val,rankOne_le_localClosure Q split i r.property⟩
  refine ⟨⟨localAction Q split i r',⟨r',rfl⟩⟩, ?_, ?_⟩
  · change localAction Q split i r' a = c
    rw [localAction_eq_panelAction]
    exact hr
  · change localAction Q split i r' b = d
    rw [localAction_eq_panelAction]
    exact hs

private theorem involution_generators {E : Type*} [Group E]
    (A B : Subgroup E) (hA : Nat.card A = 2) (hB : Nat.card B = 2)
    (hgen : A ⊔ B = ⊤) :
    ∃ a b : E, a ∈ A ∧ a ≠ 1 ∧ a^2 = 1 ∧ b ∈ B ∧ b ≠ 1 ∧ b^2 = 1 ∧
      closure ({a,b} : Set E) = ⊤ := by
  obtain ⟨a,ha,_⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  obtain ⟨b,hb,_⟩ := (Nat.card_eq_two_iff' (1 : B)).mp hB
  have hzA : zpowers (a : E) = A := by
    have hh := congrArg (Subgroup.map A.subtype) (zpowers_eq_top_of_prime_card hA ha)
    simpa only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype, Subgroup.coe_subtype] using hh
  have hzB : zpowers (b : E) = B := by
    have hh := congrArg (Subgroup.map B.subtype) (zpowers_eq_top_of_prime_card hB hb)
    simpa only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype, Subgroup.coe_subtype] using hh
  refine ⟨a,b,a.property,fun he => ha (Subtype.ext he), ?_,
    b.property,fun he => hb (Subtype.ext he), ?_, ?_⟩
  · exact congrArg Subtype.val (hA ▸ (pow_card_eq_one' (x := a)))
  · exact congrArg Subtype.val (hB ▸ (pow_card_eq_one' (x := b)))
  · rw [show ({(a:E),(b:E)} : Set E) = {(a:E)} ∪ {(b:E)} from rfl,
      closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure, hzA, hzB, hgen]

private theorem involution_product_cube (a b : Equiv.Perm (Fin 3))
    (ha : a ≠ 1) (hb : b ≠ 1) (ha2 : a^2 = 1) (hb2 : b^2 = 1) :
    (b*a)^3 = 1 := by
  revert a b
  decide +kernel

private theorem central_odd_lift_cube {E : Type*} [Group E]
    (f : E →* Equiv.Perm (Fin 3))
    (hz : f.ker ≤ center E) (ho : Nat.Coprime 2 (Nat.card f.ker))
    (a b : E) (ha : a^2 = 1) (hb : b^2 = 1)
    (hfa : f a ≠ 1) (hfb : f b ≠ 1) : (b*a)^3 = 1 := by
  have hk : (b*a)^3 ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, map_mul]
    exact involution_product_cube _ _ hfa hfb
      (by rw [← map_pow,ha,map_one]) (by rw [← map_pow,hb,map_one])
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hb)
  have hi : a*(b*a)*a⁻¹ = (b*a)⁻¹ := by
    simp only [hai,hbi,mul_inv_rev,mul_assoc,← pow_two,ha,mul_one]
  have he : (b*a)^3 = ((b*a)^3)⁻¹ := by
    calc
      (b*a)^3 = a*((b*a)^3)*a⁻¹ := by
        rw [mem_center_iff.mp (hz hk) a, mul_inv_cancel_right]
      _ = (a*(b*a)*a⁻¹)^3 := conj_pow.symm
      _ = ((b*a)^3)⁻¹ := by rw [hi,inv_pow]
  have hp : (⟨(b*a)^3,hk⟩ : f.ker)^2 = 1 := by
    apply Subtype.ext
    change ((b*a)^3)^2 = 1
    rw [pow_two]
    calc
      (b*a)^3 * (b*a)^3 = ((b*a)^3)⁻¹ * (b*a)^3 := congrArg (· * (b*a)^3) he
      _ = 1 := inv_mul_cancel _
  have hz' := (powCoprime ho.symm).injective
    (show (⟨(b*a)^3,hk⟩ : f.ker)^2 = 1^2 by simpa only [one_pow] using hp)
  exact congrArg Subtype.val hz'

/-- The literal root-generated action, with no quotient of the domain. -/
def rootPanelAction (i : Fin 2) : rankOne Q split i →* Equiv.Perm (Panel Q i) :=
  (localGroup Q split i).subtype.comp (RootLocalCover.projection Q split i)

@[simp] theorem rootPanelAction_apply (i : Fin 2) (r : rankOne Q split i) :
    rootPanelAction Q split i r =
      localAction Q split i (inclusion (rankOne_le_localClosure Q split i) r) :=
  RootLocalCover.projection_apply Q split i r

theorem rootPanelAction_ker (i : Fin 2) :
    (rootPanelAction Q split i).ker = (localKernel Q i).subgroupOf (rankOne Q split i) := by
  rw [rootPanelAction, MonoidHom.ker_comp_of_injective _ _
    (localGroup Q split i).subtype_injective, RootLocalCover.projection_ker]

theorem cubic_rootPanelAction_surjective (i : Fin 2)
    (hc : Nat.card (simpleRoot Q split i) = 2) :
    Function.Surjective (rootPanelAction Q split i) := by
  intro σ
  have hσ : σ ∈ localGroup Q split i := cubic_localGroup_eq_top Q split i hc ▸ mem_top σ
  obtain ⟨r,hr⟩ := (RootLocalCover.central_odd_cover Q split i
    (remainder_le_kernel_of_root_card_two Q split i hc)).1 ⟨σ,hσ⟩
  exact ⟨r,congrArg Subtype.val hr⟩

theorem cubic_rootPanelAction_injective (i : Fin 2)
    (hc : Nat.card (simpleRoot Q split i) = 2) :
    Function.Injective (rootPanelAction Q split i) := by
  classical
  let R := rankOne Q split i
  let A := (simpleRoot Q split i).subgroupOf R
  let C := (rootAt Q split i (Q.simple i)).subgroupOf R
  have hA : Nat.card A = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show simpleRoot Q split i ≤ R from le_sup_left)).toEquiv).trans hc
  have hC : Nat.card C = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (show rootAt Q split i (Q.simple i) ≤ R from le_sup_right)).toEquiv]
    rw [rootAt, rightConjugate, comap_equiv_eq_map_symm',
      card_map_of_injective (MulAut.conj (representative (Q.simple i) : X ⧸ Q.D)).symm.injective]
    exact hc
  have hgen : A ⊔ C = ⊤ := by
    rw [← subgroupOf_sup (show simpleRoot Q split i ≤ R from le_sup_left)
      (show rootAt Q split i (Q.simple i) ≤ R from le_sup_right)]
    exact subgroupOf_self _
  obtain ⟨a,b,ha,hane,ha2,hb,hbne,hb2,hab⟩ := involution_generators A C hA hC hgen
  let ep : Panel Q i ≃ Fin 3 := Classical.choice (Finite.card_eq.mp
    ((panel_card_three Q split i hc).trans (Nat.card_fin 3).symm))
  let f := ep.permCongrHom.toMonoidHom.comp (rootPanelAction Q split i)
  have hk : f.ker = (RootLocalCover.projection Q split i).ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ ep.permCongrHom.injective,
      rootPanelAction, MonoidHom.ker_comp_of_injective _ _ (localGroup Q split i).subtype_injective]
  have hfa : f a ≠ 1 := by
    intro he
    have haK : (a : X ⧸ Q.D) ∈ localKernel Q i := by
      have hm : a ∈ f.ker := he
      rw [hk,RootLocalCover.projection_ker] at hm
      exact hm
    exact hane (Subtype.ext ((disjoint_def.mp (simpleRoot_disjoint_localKernel Q split i)) ha haK))
  have hfb : f b ≠ 1 := by
    intro he
    have hbK : (b : X ⧸ Q.D) ∈ localKernel Q i := by
      have hm : b ∈ f.ker := he
      rw [hk,RootLocalCover.projection_ker] at hm
      exact hm
    exact hbne (Subtype.ext ((disjoint_def.mp
      (UnitarySource.oppositeRoot_disjoint_borel Q split i)) hb (localKernel_le_borel Q i hbK)))
  have hcube := central_odd_lift_cube f
    (hk.symm ▸ RootLocalCover.projection_ker_central Q split i)
    (hk.symm ▸ RootLocalCover.projection_ker_odd Q split i) a b ha2 hb2 hfa hfb
  have hbound := (closure_pair_finite_card_le_of_involutions (by decide : 0 < 3)
    a b ha2 hb2 hcube).2
  rw [hab, Nat.card_congr (topEquiv : (⊤ : Subgroup R) ≃* R).toEquiv] at hbound
  have hf : Function.Surjective f := ep.permCongrHom.surjective.comp
    (cubic_rootPanelAction_surjective Q split i hc)
  have hcard : Nat.card R = Nat.card (Equiv.Perm (Fin 3)) := by
    have htarget : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
      decide
    apply le_antisymm
    · simpa only [htarget] using hbound
    · exact Nat.card_le_card_of_surjective f hf
  have hfi := ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hf,hcard⟩).1
  intro x y he
  exact hfi (congrArg ep.permCongrHom he)

/-- A cubic endpoint's canonical root-generated group is the full permutation
 group of its SAME panel, including its original action on every point. -/
def cubicRootEquiv (i : Fin 2) (hc : Nat.card (simpleRoot Q split i) = 2) :
    rankOne Q split i ≃* Equiv.Perm (Panel Q i) :=
  MulEquiv.ofBijective (rootPanelAction Q split i)
    ⟨cubic_rootPanelAction_injective Q split i hc,
      cubic_rootPanelAction_surjective Q split i hc⟩

@[simp] theorem cubicRootEquiv_apply (i : Fin 2)
    (hc : Nat.card (simpleRoot Q split i) = 2) (r : rankOne Q split i) :
    cubicRootEquiv Q split i hc r =
      localAction Q split i (inclusion (rankOne_le_localClosure Q split i) r) :=
  rootPanelAction_apply Q split i r

/-- The central odd cover has no kernel on a cubic panel. -/
theorem cubic_root_kernel_eq_bot (i : Fin 2)
    (hc : Nat.card (simpleRoot Q split i) = 2) :
    (localKernel Q i).subgroupOf (rankOne Q split i) = ⊥ := by
  rw [← rootPanelAction_ker]
  exact (MonoidHom.ker_eq_bot_iff _).mpr (cubic_rootPanelAction_injective Q split i hc)

/-- This is the full order-six root group, including the nonperfect binary case. -/
theorem cubic_rankOne_card (i : Fin 2)
    (hc : Nat.card (simpleRoot Q split i) = 2) : Nat.card (rankOne Q split i) = 6 := by
  classical
  let : Fintype (Panel Q i) := Fintype.ofFinite _
  rw [Nat.card_congr (cubicRootEquiv Q split i hc).toEquiv,
    Nat.card_eq_fintype_card,Fintype.card_perm,← Nat.card_eq_fintype_card,
    panel_card_three Q split i hc]
  decide

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelKernel
