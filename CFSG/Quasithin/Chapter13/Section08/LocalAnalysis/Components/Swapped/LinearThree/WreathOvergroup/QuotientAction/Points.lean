module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.ParabolicPair
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.ModelAction
public import Theory.GroupTheory.SylowKernelCore

/-!
# Literal conjugation on the six parabolic core points

A marked commuting S₄ pair in H/O₂(H) has two disjoint two-cores of
order four. The generated overgroup preserves their unordered pair,
hence acts by actual conjugation on their six nonidentity elements.
The explicit block decomposition retains the embedded core carriers.

The full lift maps onto the generated subgroup with a two-group kernel.
Pulling back the point action through this map leaves its image unchanged.
The kernel identification and the image order of 72 remain separate
calculations; neither is included in this interface as an assumption.

Source: the wreath-overgroup construction in Aschbacher–Smith 13.8.16(1),
printed p.952. The source assembly still selects the parabolic pair.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup.ParabolicPair
variable {G : Type*} [Group G] {H L₁ T : Subgroup G} (d : ParabolicPair H L₁ T)

/-- The unordered pair of the actual parabolic factors. -/
def factorStabilizer : Subgroup (Source.Hstar H) :=
  (MulAction.stabilizer (MulAut (Source.Hstar H)) ({d.left, d.right} : Set (Subgroup (Source.Hstar H)))).comap MulAut.conj

private theorem mem_factorStabilizer (g : Source.Hstar H)
    (hg : (d.left.map (MulAut.conj g).toMonoidHom = d.left ∧
      d.right.map (MulAut.conj g).toMonoidHom = d.right) ∨
      (d.left.map (MulAut.conj g).toMonoidHom = d.right ∧
      d.right.map (MulAut.conj g).toMonoidHom = d.left)) : g ∈ d.factorStabilizer := by
  change MulAut.conj g • ({d.left, d.right} : Set (Subgroup (Source.Hstar H))) = _
  rw [Set.smul_set_insert, Set.smul_set_singleton]
  change {d.left.map (MulAut.conj g).toMonoidHom, d.right.map (MulAut.conj g).toMonoidHom} = _
  rcases hg with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2, Set.pair_comm]

/-- Every element of the generated overgroup preserves the factor pair. -/
theorem starOvergroup_le_factorStabilizer : d.starOvergroup ≤ d.factorStabilizer := by
  apply sup_le (sup_le ?_ ?_) ?_
  · intro g hg
    apply d.mem_factorStabilizer g
    apply Or.inl
    refine ⟨mem_normalizer_iff_map_conj_eq.mp (d.left.le_normalizer hg), ?_⟩
    apply mem_normalizer_iff_map_conj_eq.mp
    apply centralizer_le_normalizer
    apply mem_centralizer_iff.mpr
    intro y hy
    exact (d.commute g hg y hy).eq.symm
  · intro g hg
    apply d.mem_factorStabilizer g
    apply Or.inl
    refine ⟨?_, mem_normalizer_iff_map_conj_eq.mp (d.right.le_normalizer hg)⟩
    apply mem_normalizer_iff_map_conj_eq.mp
    apply centralizer_le_normalizer
    apply mem_centralizer_iff.mpr
    intro x hx
    exact (d.commute x hx g hg).eq
  · intro g hg
    exact d.mem_factorStabilizer g (d.permutes g hg)

/-- A six-point carrier: the nonidentity elements of the two embedded cores. -/
abbrev CorePoints := {x : Source.Hstar H // x ≠ 1 ∧
  (x ∈ d.left.pCoreIn 2 ∨ x ∈ d.right.pCoreIn 2)}

private theorem maps_factor (g : Source.Hstar H) (hg : g ∈ d.factorStabilizer)
    (P : Subgroup (Source.Hstar H)) (hP : P = d.left ∨ P = d.right) :
    P.map (MulAut.conj g).toMonoidHom = d.left ∨
      P.map (MulAut.conj g).toMonoidHom = d.right := by
  have hfix : MulAut.conj g • ({d.left, d.right} : Set (Subgroup (Source.Hstar H))) =
      {d.left, d.right} := hg
  have hm := Set.smul_mem_smul_set (a := MulAut.conj g)
    (show P ∈ ({d.left, d.right} : Set _) by simpa using hP)
  rw [hfix] at hm
  exact hm

/-- Pair preservation extends from T to the generated overgroup. -/
theorem starOvergroup_permutes (g : d.starOvergroup) :
    (d.left.map (MulAut.conj g.val).toMonoidHom = d.left ∧
      d.right.map (MulAut.conj g.val).toMonoidHom = d.right) ∨
    (d.left.map (MulAut.conj g.val).toMonoidHom = d.right ∧
      d.right.map (MulAut.conj g.val).toMonoidHom = d.left) := by
  have hL := d.maps_factor g.val (d.starOvergroup_le_factorStabilizer g.property)
    d.left (Or.inl rfl)
  have hR := d.maps_factor g.val (d.starOvergroup_le_factorStabilizer g.property)
    d.right (Or.inr rfl)
  rcases hL with hL | hL <;> rcases hR with hR | hR
  · have he : d.left = d.right := map_injective (MulAut.conj g.val).injective (hL.trans hR.symm)
    exact Or.inl ⟨hL, hR.trans he⟩
  · exact Or.inl ⟨hL, hR⟩
  · exact Or.inr ⟨hL, hR⟩
  · have he : d.left = d.right := map_injective (MulAut.conj g.val).injective (hL.trans hR.symm)
    exact Or.inl ⟨hL.trans he.symm, hR⟩

/-- The characteristic cores are preserved or interchanged with their factors. -/
theorem starOvergroup_permutes_cores (g : d.starOvergroup) :
    ((d.left.pCoreIn 2).map (MulAut.conj g.val).toMonoidHom = d.left.pCoreIn 2 ∧
      (d.right.pCoreIn 2).map (MulAut.conj g.val).toMonoidHom = d.right.pCoreIn 2) ∨
    ((d.left.pCoreIn 2).map (MulAut.conj g.val).toMonoidHom = d.right.pCoreIn 2 ∧
      (d.right.pCoreIn 2).map (MulAut.conj g.val).toMonoidHom = d.left.pCoreIn 2) := by
  rw [map_pCoreIn_of_injective 2 d.left _ (MulAut.conj g.val).injective,
    map_pCoreIn_of_injective 2 d.right _ (MulAut.conj g.val).injective]
  rcases d.starOvergroup_permutes g with h | h
  · exact Or.inl ⟨congrArg (pCoreIn 2) h.1, congrArg (pCoreIn 2) h.2⟩
  · exact Or.inr ⟨congrArg (pCoreIn 2) h.1, congrArg (pCoreIn 2) h.2⟩

private theorem corePoint_conj (g : Source.Hstar H) (hg : g ∈ d.factorStabilizer)
    (x : Source.Hstar H) (hx : x ≠ 1 ∧
      (x ∈ d.left.pCoreIn 2 ∨ x ∈ d.right.pCoreIn 2)) :
    MulAut.conj g x ≠ 1 ∧
      (MulAut.conj g x ∈ d.left.pCoreIn 2 ∨ MulAut.conj g x ∈ d.right.pCoreIn 2) := by
  refine ⟨by simpa using hx.1, ?_⟩
  have step (P : Subgroup (Source.Hstar H)) (hP : P = d.left ∨ P = d.right)
      (hm : x ∈ P.pCoreIn 2) :
      MulAut.conj g x ∈ d.left.pCoreIn 2 ∨ MulAut.conj g x ∈ d.right.pCoreIn 2 := by
    have hm' := mem_map_of_mem (MulAut.conj g).toMonoidHom hm
    rw [map_pCoreIn_of_injective 2 P _ (MulAut.conj g).injective] at hm'
    rcases d.maps_factor g hg P hP with he | he
    · exact Or.inl (he ▸ hm')
    · exact Or.inr (he ▸ hm')
  exact hx.2.elim (step d.left (Or.inl rfl)) (step d.right (Or.inr rfl))

/-- Literal conjugation, restricted to the two parabolic cores. -/
noncomputable def corePointAction : d.starOvergroup →* Equiv.Perm d.CorePoints where
  toFun g := Equiv.Perm.subtypePerm (MulAut.conj g.val).toEquiv (by
    intro x
    constructor
    · intro hx
      have h := d.corePoint_conj g.val⁻¹
        (d.factorStabilizer.inv_mem (d.starOvergroup_le_factorStabilizer g.property))
        (MulAut.conj g.val x) hx
      simpa [MulAut.conj_apply, mul_assoc] using h
    · exact d.corePoint_conj g.val (d.starOvergroup_le_factorStabilizer g.property) x)
  map_one' := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change 1 * x.val * 1⁻¹ = x.val
    simp
  map_mul' g h := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (g.val * h.val) * x.val * (g.val * h.val)⁻¹ =
      g.val * (h.val * x.val * h.val⁻¹) * g.val⁻¹
    simp [mul_assoc]

/-- The point action computes the actual ambient conjugate. -/
theorem corePointAction_apply (g : d.starOvergroup) (x : d.CorePoints) :
    (d.corePointAction g x : Source.Hstar H) = g.val * x.val * g.val⁻¹ := rfl

/-- The restriction of H → H/O₂(H) to the full lifted overgroup. -/
noncomputable def starProjection : d.overgroup →* d.starOvergroup :=
  ((QuotientGroup.mk' (pCore 2 H)).comp (inclusion d.overgroup_le)).codRestrict
    d.starOvergroup (by
      intro g
      obtain ⟨h, hh, he⟩ := g.property
      have hi : inclusion d.overgroup_le g = h := Subtype.ext he.symm
      change QuotientGroup.mk' (pCore 2 H) (inclusion d.overgroup_le g) ∈ d.starOvergroup
      rw [hi]
      exact hh)

theorem starProjection_apply (g : d.overgroup) :
    (d.starProjection g : Source.Hstar H) =
      QuotientGroup.mk' (pCore 2 H) (inclusion d.overgroup_le g) := rfl

/-- Full inverse image, rather than a chosen supplement, makes this map onto. -/
theorem starProjection_surjective : Function.Surjective d.starProjection := by
  intro s
  obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective (pCore 2 H) s.val
  have hm : h ∈ d.starOvergroup.comap (QuotientGroup.mk' (pCore 2 H)) := by
    change QuotientGroup.mk' (pCore 2 H) h ∈ d.starOvergroup
    rw [hh]
    exact s.property
  refine ⟨⟨h.val, ⟨h, hm, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  exact hh

/-- The kernel embeds in the original O₂(H). -/
theorem starProjection_kernel_isPGroup : IsPGroup 2 d.starProjection.ker := by
  let f : d.starProjection.ker →* H := (inclusion d.overgroup_le).comp d.starProjection.ker.subtype
  have hf (x : d.starProjection.ker) : f x ∈ pCore 2 H := by
    apply (QuotientGroup.eq_one_iff (N := pCore 2 H) (f x)).mp
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp x.property)
  let r : d.starProjection.ker →* pCore 2 H := f.codRestrict _ hf
  apply pCore_isPGroup.of_injective r
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : pCore 2 H => (z.val : G)) hxy

/-- The original overgroup acts on the very same six core elements. -/
noncomputable def liftedCorePointAction : d.overgroup →* Equiv.Perm d.CorePoints :=
  d.corePointAction.comp d.starProjection

theorem liftedCorePointAction_apply (g : d.overgroup) (x : d.CorePoints) :
    (d.liftedCorePointAction g x : Source.Hstar H) =
      (d.starProjection g : Source.Hstar H) * x.val *
        (d.starProjection g : Source.Hstar H)⁻¹ := rfl

/-- Lifting through the two-core does not change the literal permutation image. -/
theorem liftedCorePointAction_range : d.liftedCorePointAction.range = d.corePointAction.range := by
  rw [liftedCorePointAction, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr d.starProjection_surjective, ← MonoidHom.range_eq_map]

/-- Splitting the literal point carrier into its two nonidentity core blocks. -/
noncomputable def corePointsEquivSum : d.CorePoints ≃
    {x : d.left.pCoreIn 2 // x ≠ 1} ⊕ {x : d.right.pCoreIn 2 // x ≠ 1} := by
  classical
  let nonidentityEquiv (P : Subgroup (Source.Hstar H)) :
      {x : Source.Hstar H // x ≠ 1 ∧ x ∈ P} ≃ {x : P // x ≠ 1} := {
    toFun := fun x => ⟨⟨x.val, x.property.2⟩, fun h => x.property.1 (congrArg Subtype.val h)⟩
    invFun := fun x => ⟨x.val.val, fun h => x.property (Subtype.ext h), x.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let U : Set (Source.Hstar H) := {x | x ≠ 1 ∧ x ∈ d.left.pCoreIn 2}
  let V : Set (Source.Hstar H) := {x | x ≠ 1 ∧ x ∈ d.right.pCoreIn 2}
  have hd : Disjoint U V := Set.disjoint_left.mpr (by
    intro x hx hy
    exact hx.1 (Subgroup.disjoint_def.mp d.disjoint
      (pCoreIn_le 2 d.left hx.2) (pCoreIn_le 2 d.right hy.2)))
  let split : d.CorePoints ≃ (U ∪ V : Set (Source.Hstar H)) :=
    Equiv.subtypeEquivRight (fun _ => and_or_left)
  exact (split.trans (Equiv.Set.union hd)).trans
    (Equiv.sumCongr (nonidentityEquiv (d.left.pCoreIn 2))
      (nonidentityEquiv (d.right.pCoreIn 2)))

theorem corePointsEquivSum_symm_inl (x : {x : d.left.pCoreIn 2 // x ≠ 1}) :
    (d.corePointsEquivSum.symm (Sum.inl x) : Source.Hstar H) = x.val.val := rfl

theorem corePointsEquivSum_symm_inr (x : {x : d.right.pCoreIn 2 // x ≠ 1}) :
    (d.corePointsEquivSum.symm (Sum.inr x) : Source.Hstar H) = x.val.val := rfl

variable [Finite G]

/-- Both ambient core carriers have the intrinsic S₄ core order. -/
theorem core_cards : Nat.card (d.left.pCoreIn 2) = 4 ∧ Nat.card (d.right.pCoreIn 2) = 4 := by
  constructor
  · rw [pCoreIn, card_map_of_injective d.left.subtype_injective]
    exact (Matrix.PSL3Two.ParabolicCoreModel.core_data d.leftEquiv).2
  · rw [pCoreIn, card_map_of_injective d.right.subtype_injective]
    exact (Matrix.PSL3Two.ParabolicCoreModel.core_data d.rightEquiv).2

private theorem nonidentity_card (P : Subgroup (Source.Hstar H)) (hc : Nat.card P = 4) :
    Nat.card {x : P // x ≠ 1} = 3 := by
  classical
  let : Fintype P := Fintype.ofFinite P
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp only [Fintype.card_unique, ← Nat.card_eq_fintype_card, hc]

/-- There are literally six distinct nonidentity core elements. -/
theorem corePoints_card : Nat.card d.CorePoints = 6 := by
  rw [Nat.card_congr d.corePointsEquivSum, Nat.card_sum,
    nonidentity_card _ d.core_cards.1, nonidentity_card _ d.core_cards.2]

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup.ParabolicPair

end
