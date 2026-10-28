module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiWeightProfile
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiConstituentKernels
public import Theory.Representation.DistinctKernelGenerators

/-!
# Cartan separation in ordered radical products

In a completely reducible representation, images of irreducible constituents
with different action kernels cannot cancel, even if some constituent maps
are zero. Apply this to the actual root Frattini maps into the radical
Frattini quotient: membership of an ordered product forces membership of
each coordinate. Odd Frattini faithfulness also gives an irreducibility
criterion from a cyclic root-action image of order q-1 on a quotient of
order q.

Source: Fong--Seitz I (1973), pp.51--53, the Wedderburn-component argument
in (6H). ReeSource.SeparatedProducts in CFSG discharges the action and
kernel premises using the literal linear and Suzuki panel markings.
-/

@[expose] public noncomputable section
open Subgroup
set_option backward.isDefEq.respectTransparency false
open scoped MonoidAlgebra IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open RootCoordinates HexagonStructure

/-- A zero sum of images of simple constituents with different kernels has
zero in each image. Some of the constituent maps may themselves vanish. -/
theorem constituent_images_zero_of_sum_zero
    {k H W : Type*} [Field k] [Group H] [AddCommGroup W] [Module k W]
    {ι : Type*} [Fintype ι] (V : ι → Type*)
    [∀ t, AddCommGroup (V t)] [∀ t, Module k (V t)]
    (ρ : ∀ t, Representation k H (V t)) (σ : Representation k H W)
    (hir : ∀ t, (ρ t).IsIrreducible) (hcr : σ.IsCompletelyReducible)
    (hker : Pairwise fun t u => (ρ t).ker ≠ (ρ u).ker)
    (f : ∀ t, (ρ t).IntertwiningMap σ) (v : ∀ t, V t)
    (hz : ∑ t, f t (v t) = 0) : ∀ t, f t (v t) = 0 := by
  classical
  intro t
  by_cases ht : f t = 0
  · rw [ht]; rfl
  let := hir t
  have hinj := (Representation.IsIrreducible.injective_or_eq_zero (f t)).resolve_right ht
  let : IsSemisimpleModule k[H] σ.asModule := hcr
  let fm := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (f t)
  obtain ⟨pm,hpm⟩ := IsSemisimpleModule.extension_property fm
    (show Function.Injective fm from hinj)
    (LinearMap.id : (ρ t).asModule →ₗ[k[H]] (ρ t).asModule)
  let p := (Representation.IntertwiningMap.equivLinearMapAsModule σ (ρ t)).symm pm
  have hp (x : V t) : p (f t x) = x := LinearMap.congr_fun hpm x
  have hzero (u : ι) (hu : u ≠ t) : p (f u (v u)) = 0 := by
    let := hir u
    have he := Representation.intertwiner_eq_zero_of_distinct_kernels
      (hker hu) (p.comp (f u))
    exact congrArg (fun g => g (v u)) he
  have hh := congrArg p hz
  rw [map_sum,Finset.sum_eq_single t,map_zero,hp] at hh
  · rw [hh,map_zero]
  · intro u _ hut; exact hzero u hut
  · simp

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The quotient map preserves every constituent coordinate separately.
This is the ordered-product form of the source Wedderburn argument. -/
theorem separated_root_frattini_product_support
    (i : Fin 2) (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    {r : ℕ} (k : Fin r → Fin 2) (w : Fin r → Weyl Q)
    (hA : ∀ t, rootAt Q split (k t) (w t) ≤ simpleRemainder Q split i)
    (hir : ∀ t, (rootAtCartanFrattiniRepresentation Q split (k t) (w t)).IsIrreducible)
    (hker : Pairwise fun t u => (rootAction Q split (k t) (w t)).ker ≠
      (rootAction Q split (k u) (w u)).ker)
    (a : ∀ t, rootAt Q split (k t) (w t))
    (hz : (List.ofFn (fun t => (a t : X ⧸ Q.D))).prod ∈
      (frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype) :
    ∀ t, (a t : X ⧸ Q.D) ∈
      (frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype := by
  let d := radicalSection Q split i hKi
  let σ := radicalHRepresentation Q split i hKi
  let F (t : Fin r) := Additive (rootAt Q split (k t) (w t) ⧸ frattini (rootAt Q split (k t) (w t)))
  let ρ (t : Fin r) := rootAtCartanFrattiniRepresentation Q split (k t) (w t)
  let f (t : Fin r) := rootFrattiniIntertwiner Q split i hKi (k t) (w t) (hA t)
  let q := QuotientGroup.mk' d.effectiveDenominator
  let v (t : Fin r) : F t := Additive.ofMul (QuotientGroup.mk (a t))
  let b (t : Fin r) := inclusion (hA t) (a t)
  have hb : (List.ofFn b).prod ∈ frattini (simpleRemainder Q split i) := by
    obtain ⟨x,hx,he⟩ := hz
    have he' : x = (List.ofFn b).prod := by
      apply Subtype.ext
      change (simpleRemainder Q split i).subtype x =
        (simpleRemainder Q split i).subtype ((List.ofFn b).prod)
      rw [map_list_prod,List.map_ofFn]
      exact he
    exact he' ▸ hx
  have hq : q ((List.ofFn b).prod) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [suzuki_radical_effectiveDenominator Q split i hKi]
    exact hb
  have hsum : ∑ t, f t (v t) = 0 := by
    have hh := congrArg Additive.ofMul hq
    rw [map_list_prod,List.map_ofFn] at hh
    change (List.ofFn (fun t => Additive.ofMul (q (b t)))).sum = 0 at hh
    have hfv (t : Fin r) : f t (v t) = Additive.ofMul (q (b t)) := rfl
    simpa only [hfv,List.sum_ofFn] using hh
  have hcr : Representation.IsCompletelyReducible σ :=
    Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime σ (Or.inr (by
      rw [ringChar.eq (ZMod 2) 2]; exact ⟨Nat.prime_two,split.odd⟩))
  have hsep : Pairwise fun t u => (ρ t).ker ≠ (ρ u).ker := by
    intro t u htu
    simpa only [ρ,rootAtCartanFrattiniRepresentation_kernel] using hker htu
  have hz' := constituent_images_zero_of_sum_zero F ρ σ hir hcr hsep f v hsum
  intro t
  have ht : q (b t) = 1 := congrArg Additive.toMul (hz' t)
  have ht' := (QuotientGroup.eq_one_iff _).mp ht
  rw [suzuki_radical_effectiveDenominator Q split i hKi] at ht'
  exact mem_map_of_mem (simpleRemainder Q split i).subtype ht'


/-- A cyclic odd image of order q-1 acts irreducibly on a root quotient of
order q. Odd Frattini faithfulness retains the full action image. -/
theorem root_frattini_irreducible_of_card
    (i : Fin 2) (w : Weyl Q) (d : ℕ) (hd : 0 < d)
    (hcyc : IsCyclic (rootAction Q split i w).range)
    (hcard : Nat.card (rootAction Q split i w).range = 2^d-1)
    (hquot : Nat.card (rootAt Q split i w ⧸ frattini (rootAt Q split i w)) = 2^d) :
    (rootAtCartanFrattiniRepresentation Q split i w).IsIrreducible := by
  let A := rootAt Q split i w
  let C := (rootAction Q split i w).range
  let E := A ⧸ frattini A
  let f := (quotientAut (frattini A)).comp C.subtype
  let : IsCyclic C := hcyc
  have hf : Function.Injective f := MonoidHom.injective_frattini_action_of_coprime
    (rootAt_isTwo Q split i w).out C.subtype C.subtype_injective
    (split.odd.of_dvd_right (card_dvd_of_surjective
      (rootAction Q split i w).rangeRestrict (rootAction Q split i w).rangeRestrict_surjective)).symm
  let D := f.range
  let : IsCyclic D := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hf' : Function.Injective f.rangeRestrict := by
    intro x y he; exact hf (congrArg Subtype.val he)
  have hD : Nat.card D = 2^d-1 :=
    (Nat.card_congr (Equiv.ofBijective f.rangeRestrict ⟨hf',f.rangeRestrict_surjective⟩)).symm.trans hcard
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card (A ⧸ frattini A)
    rw [hquot]; exact Nat.one_lt_pow hd.ne' (by decide))
  let ρ := rootAtCartanFrattiniRepresentation Q split i w
  have ht (x y : E) (hx : x ≠ 1) (hy : y ≠ 1) :
      ∃ h, rootAtCartanFrattiniAction Q split i w h x = y := by
    obtain ⟨c,hc,_⟩ := RootAction.regular_of_card D.subtype D.subtype_injective hd hD hquot x y hx hy
    obtain ⟨a,ha⟩ := c.property
    obtain ⟨h,hh⟩ := a.property
    refine ⟨h,?_⟩
    change ((quotientAut (frattini A)) (rootAction Q split i w h)) x = y
    rw [hh]
    exact (congrArg (fun g : MulAut E => g x) ha).trans hc
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hn : S.toSubmodule ≠ ⊥ := fun he => hS (Subrepresentation.toSubmodule_injective he)
  let : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hn
  obtain ⟨x,hx⟩ := exists_ne (0 : S.toSubmodule)
  have hx' : x.val.toMul ≠ 1 := fun he => hx (Subtype.ext (Additive.toMul.injective he))
  apply top_unique
  intro y _
  by_cases hy : y = 0
  · rw [hy]; exact S.toSubmodule.zero_mem
  obtain ⟨h,hh⟩ := ht x.val.toMul y.toMul hx' (fun he => hy (Additive.toMul.injective he))
  have he : ρ h x.val = y := Additive.toMul.injective hh
  exact he ▸ S.apply_mem_toSubmodule h x.property

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
