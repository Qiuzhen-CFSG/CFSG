module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.FiveOverlap
public import Theory.SpecificGroups.SymmetricFive.WreathComponents
public import Theory.GroupTheory.RegularWreathSubgroup

/-!
# A cubic escaping the paired-five overlap

The product action on the 25 pairs of letters gives a fixed point for
each Sylow two-subgroup. Its stabilizer is maximal: it is a conjugate
of the regular wreath product of a maximal self-normalizing S₄. Inside
that stabilizer, a normal subgroup containing an axis transposition
contains a cubic whose normalizer escapes the stabilizer.

The two coordinates and the coordinate-exchanging action are retained.
The source applications are PairedFiveChiefExclusion and M22CodeSolvable.
Source: Aschbacher--Smith 3.1.9(6), p.578, used in 8.2.2(1), p.715.
-/

@[expose] public noncomputable section
open Subgroup
namespace MathieuCode.NormalizedShadowRows.FivePairOverlap
open Theory.SpecificGroups.SymmetricFive.WreathComponents
abbrev Points := C2 → Fin 5
instance pointAction : MulAction W Points where
  smul w v i := w.left i (v (w.right⁻¹ * i))
  one_smul v := by
    funext i
    change (1 : Equiv.Perm (Fin 5)) (v ((1 : C2)⁻¹ * i)) = v i
    simp
  mul_smul a b v := by
    funext i
    change (a.left i * b.left (a.right⁻¹ * i)) (v ((a.right * b.right)⁻¹ * i)) =
      a.left i (b.left (a.right⁻¹ * i) (v (b.right⁻¹ * (a.right⁻¹ * i))))
    simp [mul_assoc]

def axis (i : C2) : Sym →* W where
  toFun a := ⟨Pi.mulSingle i a,1⟩
  map_one' := by ext <;> simp
  map_mul' a b := by
    apply RegularWreathProduct.ext
    · funext j
      by_cases hj : j = i <;> simp [RegularWreathProduct.mul_left, Pi.mulSingle, hj]
    · rfl

@[simp] theorem axis_apply (i : C2) (a : Sym) :
    axis i a = ⟨Pi.mulSingle i a,1⟩ := rfl

theorem axis_injective (i : C2) : Function.Injective (axis i) := by
  intro a b h
  have hh := congrArg (fun w : W => w.left i) h
  simpa [axis_apply] using hh

theorem axis_stabilizes (v : Points) (i : C2) (a : Sym) :
    axis i a ∈ MulAction.stabilizer W v ↔ a (v i) = v i := by
  constructor
  · intro h
    have hh := congrFun h i
    change (Pi.mulSingle i a : C2 → Sym) i (v (1⁻¹ * i)) = v i at hh
    simpa using hh
  · intro h
    change (axis i a) • v = v
    funext j
    change (Pi.mulSingle i a : C2 → Sym) j (v (1⁻¹ * j)) = v j
    by_cases hj : i = j
    · subst j
      simpa using h
    · simp [Pi.mulSingle_eq_of_ne (Ne.symm hj)]

theorem stabilizer_proper (v : Points) : MulAction.stabilizer W v ≠ ⊤ := by
  obtain ⟨j,hj⟩ := exists_ne (v 1)
  intro he
  have hh := (axis_stabilizes v 1 (Equiv.swap (v 1) j)).mp
    (show axis 1 (Equiv.swap (v 1) j) ∈ MulAction.stabilizer W v from he ▸ mem_top _)
  exact hj (by simpa only [Equiv.swap_apply_left] using hh)

theorem fixed_point (S : Sylow 2 W) :
    ∃ v : Points, (S : Subgroup W) ≤ MulAction.stabilizer W v := by
  obtain ⟨v,hv⟩ := S.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card Points (by
    norm_num [Points,Nat.card_fun,C2])
  exact ⟨v,fun _ hx => hv ⟨_,hx⟩⟩

private theorem point_maximal : IsCoatom (MulAction.stabilizer Sym (4 : Fin 5)) := by
  let B := MulAction.stabilizer Sym (4 : Fin 5)
  have hi : B.index = 5 := by
    rw [MulAction.index_stabilizer,MulAction.orbit_eq_univ]
    simp
  change IsCoatom B
  refine ⟨fun he => by simp [he] at hi,fun K hK => ?_⟩
  have hm := relIndex_mul_index hK.le
  rw [hi] at hm
  have hp : (B.relIndex K * K.index).Prime := by
    rw [hm]
    decide
  rcases Nat.prime_mul_iff.mp hp with ⟨_,hK⟩ | ⟨_,hrel⟩
  · exact index_eq_one.mp hK
  · exact (hK.not_ge (relIndex_eq_one.mp hrel)).elim

private theorem point_self_normalizing :
    normalizer (MulAction.stabilizer Sym (4 : Fin 5) : Set Sym) =
      MulAction.stabilizer Sym (4 : Fin 5) := by
  apply le_antisymm ?_ (MulAction.stabilizer Sym (4 : Fin 5)).le_normalizer
  intro g hg
  have he : g.symm 4 = 4 := by
    have hh : ∀ j : Fin 5, (∀ a : Sym, a 4 = 4 → a j = j) → j = 4 := by
      decide +kernel
    apply hh
    intro a ha
    have hc : (g*a*g⁻¹) 4 = 4 :=
      (mem_normalizer_iff.mp hg a).mp ha
    apply g.injective
    simpa using hc
  have hh := congrArg g he
  simpa using hh.symm

/-- Every grid point stabilizer is maximal, in the literal regular wreath product. -/
theorem stabilizer_maximal (v : Points) : IsCoatom (MulAction.stabilizer W v) := by
  let c : Points := fun _ => 4
  have hcoord : MulAction.stabilizer W c =
      RegularWreathProduct.coordinateSubgroup (Q := C2) (MulAction.stabilizer Sym (4 : Fin 5)) := by
    ext w
    change (fun i => w.left i (c (w.right⁻¹*i))) = c ↔ ∀ i, w.left i 4 = 4
    exact funext_iff
  have hm : IsCoatom (MulAction.stabilizer W c) := by
    rw [hcoord]
    exact RegularWreathProduct.coordinateSubgroup_isCoatom _ point_maximal point_self_normalizing
  let g : W := ⟨fun i => Equiv.swap 4 (v i),1⟩
  have hgv : g • c = v := by
    funext i
    change Equiv.swap 4 (v i) 4 = v i
    exact Equiv.swap_apply_left _ _
  rw [←hgv,MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup _).mpr hm

/-- A transposition on one coordinate gives a cubic escaping the whole grid stabilizer. -/
theorem cubic_of_axis_swap (v : Points) (C : Subgroup W)
    (hC : C ≤ MulAction.stabilizer W v)
    (hn : MulAction.stabilizer W v ≤ normalizer (C : Set W))
    (i : C2) (a : Sym) (ha : axis i a ∈ C) (hs : a.IsSwap) :
    ∃ Y : Subgroup W, IsPGroup 3 Y ∧ Y ≠ ⊥ ∧ Y ≤ C ∧
      ¬ normalizer (Y : Set W) ≤ MulAction.stabilizer W v := by
  let C₀ := C.comap (axis i)
  have hC₀ : C₀ ≤ MulAction.stabilizer Sym (v i) := by
    intro a ha
    exact (axis_stabilizes v i a).mp (hC ha)
  have hn₀ : MulAction.stabilizer Sym (v i) ≤ normalizer (C₀ : Set Sym) := by
    apply le_normalizer_iff.mpr
    intro a ha x hx
    change axis i (a*x*a⁻¹) ∈ C
    rw [map_mul,map_mul,map_inv]
    exact le_normalizer_iff.mp hn (axis i a) ((axis_stabilizes v i a).mpr ha) _ hx
  obtain ⟨x,hx,ho,hescape⟩ := FiveOverlap.cubic_of_swap (v i) C₀ hC₀ hn₀ a ha hs
  let Y := (zpowers x).map (axis i)
  have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,ho,pow_one])
  refine ⟨Y,hp.map _,?_,map_le_iff_le_comap.mpr (zpowers_le.mpr hx),?_⟩
  · intro he
    have hh := (map_eq_bot_iff_of_injective _ (axis_injective i)).mp he
    have hx1 := zpowers_eq_bot.mp hh
    rw [hx1,orderOf_one] at ho
    contradiction
  · intro hY
    apply hescape
    intro g hg
    exact (axis_stabilizes v i g).mp
      (hY ((zpowers x).le_normalizer_map (axis i) (mem_map_of_mem (axis i) hg)))
end MathieuCode.NormalizedShadowRows.FivePairOverlap
