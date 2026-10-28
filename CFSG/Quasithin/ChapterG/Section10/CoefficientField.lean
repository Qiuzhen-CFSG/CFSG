module
public import CFSG.Quasithin.ChapterG.Section10.NumericalGeometry
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Theory.Representation.SL2NaturalOffenders.FieldAction.Basic
public import Mathlib.FieldTheory.Fixed

/-!
# Coefficient fields of the original marked transvection action

When the marked space has binary dimension at least three, every invertible
operator commuting with the actor fixes its marked point. Otherwise the
marked space and its image are disjoint, while the source displacement on the
point hyperplane forces the latter space to have dimension at most two.

Consequently a coefficient field for a linear actor is binary. For a semilinear
elementary actor, apply this to its fixed coefficient field; its coefficient
image has order at most two, so the full coefficient field has order at most
four. All original G.10 transvection and hyperplane-displacement hypotheses
remain in the theorem.

Source: Aschbacher--Smith, G.10.1 and the field-action step in G.11.7.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup D}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

omit [FiniteDimensional (ZMod 2) V] in
/-- The full centered transvections on W have exactly the marked fixed line. -/
theorem fixed_on_marked_space (w : V) (hw : w ∈ W)
    (hf : ∀ x : X, ρ x w = w) : w ∈ Submodule.span (ZMod 2) {v} := by
  let wW : W := ⟨w,hw⟩
  let vW : W := ⟨v,h.point_mem⟩
  have hh : wW ∈ Submodule.span (ZMod 2) {vW} := by
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
      (Submodule.span (ZMod 2) {vW}) wW).mp
    intro f hf0
    have hfv : f vW = 0 := ((Submodule.mem_dualAnnihilator f).mp hf0) _ (Submodule.mem_span_singleton_self _)
    obtain ⟨x,hx⟩ := h.full_transvections f hfv
    have he := (hx wW).symm.trans (hf x)
    have hz : f wW • v = 0 := add_eq_left.mp he
    exact (smul_eq_zero.mp hz).resolve_right h.point_ne_zero
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hh
  exact Submodule.mem_span_singleton.mpr ⟨c,congrArg Subtype.val hc⟩

/-- A commuting linear automorphism fixes the marked point once W has
at least three dimensions. -/
theorem centralizingLinearEquiv_fixes_point
    (J : V ≃ₗ[ZMod 2] V)
    (hJ : ∀ (x : X) w, ρ x (J w) = J (ρ x w))
    (hd : 3 ≤ finrank (ZMod 2) W) : J v = v := by
  classical
  by_contra hne
  have haxis {w : V} (hv : w ∈ Submodule.span (ZMod 2) {v})
      (hj : w ∈ Submodule.span (ZMod 2) {J v}) : w = 0 := by
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hv
    obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp hj
    fin_cases a <;> fin_cases b
    · change (0 : ZMod 2) • v = w at ha
      simpa only [zero_smul] using ha.symm
    · change (0 : ZMod 2) • v = w at ha
      simpa only [zero_smul] using ha.symm
    · change (0 : ZMod 2) • J v = w at hb
      simpa only [zero_smul] using hb.symm
    · change (1 : ZMod 2) • v = w at ha
      change (1 : ZMod 2) • J v = w at hb
      simp only [one_smul] at ha hb
      exact (hne (hb.trans ha.symm)).elim
  let U := W.map J.toLinearMap
  have hdiffW (x : X) (w : W) : ρ x w - w ∈ Submodule.span (ZMod 2) {v} := by
    obtain ⟨f,_,hf⟩ := h.transvections x
    rw [hf w,add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hdiffU (x : X) (u : V) (hu : u ∈ U) :
      ρ x u - u ∈ Submodule.span (ZMod 2) {J v} := by
    obtain ⟨w,hw,rfl⟩ := hu
    change ρ x (J w) - J w ∈ _
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hdiffW x ⟨w,hw⟩)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c,?_⟩
    calc
      c • J v = J (c • v) := (J.map_smul c v).symm
      _ = J (ρ x w - w) := congrArg J hc
      _ = ρ x (J w) - J w := by simp only [map_sub,hJ]
  have hinter : Disjoint W U := by
    apply Submodule.disjoint_def.mpr
    intro w hw hu
    have hf (x : X) : ρ x w = w := sub_eq_zero.mp
      (haxis (hdiffW x ⟨w,hw⟩) (hdiffU x w hu))
    have hwv := h.fixed_on_marked_space w hw hf
    obtain ⟨z,hz,hzw⟩ := hu
    have hzf (x : X) : ρ x z = z := by
      apply J.injective
      rw [← hJ]
      change ρ x (J z) = J z
      rw [show J z = w from hzw,hf]
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (h.fixed_on_marked_space z hz hzf)
    have hwj : w ∈ Submodule.span (ZMod 2) {J v} :=
      Submodule.mem_span_singleton.mpr ⟨c,by rw [← J.map_smul,hc]; exact hzw⟩
    exact haxis hwv hwj
  let f : U →ₗ[ZMod 2] ZMod 2 := (B v).comp U.subtype
  have hker : f.ker ≤ (Submodule.span (ZMod 2) {J v}).comap U.subtype := by
    intro u hu
    have hf (x : X) : ρ x u = u := by
      apply sub_eq_zero.mp
      apply (Submodule.disjoint_def.mp hinter)
      · exact h.displacement x u hu
      · obtain ⟨w,hw,he⟩ := u.property
        refine ⟨ρ x w - w,W.sub_mem (h.stable_W x w hw) hw,?_⟩
        change J (ρ x w - w) = ρ x u - u
        rw [map_sub,← hJ]
        exact congrArg (fun z => ρ x z - z) he
    obtain ⟨w,hw,he⟩ := u.property
    have hwfix (x : X) : ρ x w = w := by
      apply J.injective
      rw [← hJ]
      change ρ x (J w) = J w
      rw [show J w = (u : V) from he,hf]
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (h.fixed_on_marked_space w hw hwfix)
    exact Submodule.mem_span_singleton.mpr ⟨c,by rw [← J.map_smul,hc]; exact he⟩
  have hk : finrank (ZMod 2) f.ker ≤ 1 := by
    have hk0 := Submodule.finrank_mono hker
    have hm : finrank (ZMod 2) ((Submodule.span (ZMod 2) {J v}).comap U.subtype) ≤
        finrank (ZMod 2) (Submodule.span (ZMod 2) {J v}) := by
      let j : ((Submodule.span (ZMod 2) {J v}).comap U.subtype) →ₗ[ZMod 2]
          Submodule.span (ZMod 2) {J v} :=
        { toFun := fun u => ⟨u.val.val,u.property⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      exact LinearMap.finrank_le_finrank_of_injective (f := j)
        (by
          intro a b he
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun z : Submodule.span (ZMod 2) {J v} => (z : V)) he)
    have hvj : J v ≠ 0 := fun he => h.point_ne_zero (J.injective (he.trans J.map_zero.symm))
    rw [finrank_span_singleton hvj] at hm
    omega
  have hr : finrank (ZMod 2) f.range ≤ 1 := by
    exact (Submodule.finrank_le f.range).trans_eq (Module.finrank_self _)
  have heq := f.finrank_range_add_finrank_ker
  have hu : finrank (ZMod 2) U = finrank (ZMod 2) W := J.finrank_map_eq W
  omega
/-- A coefficient field commuting with the actor is binary once the original
marked transvection space has dimension at least three. -/
theorem coefficient_card_le_two
    {K : Type*} [Field K] [Algebra (ZMod 2) K] [Module K V]
    [IsScalarTower (ZMod 2) K V]
    (hlinear : ∀ (x : X) (c : K) w, ρ x (c • w) = c • ρ x w)
    (hd : 3 ≤ finrank (ZMod 2) W) : Nat.card K ≤ 2 := by
  classical
  let f : K → Submodule.span (ZMod 2) {v} := fun c => ⟨c • v,by
    by_cases hc : c = 0
    · simp only [hc,zero_smul,Submodule.zero_mem]
    · let J := (LinearEquiv.smulOfNeZero K V c hc : V ≃ₗ[K] V).restrictScalars (ZMod 2)
      have hj : J v = v := h.centralizingLinearEquiv_fixes_point J
        (fun x w => hlinear x c w) hd
      change c • v ∈ _
      rw [show c • v = v from hj]
      exact Submodule.mem_span_singleton_self _⟩
  have hi : Function.Injective f := fun a b he =>
    smul_left_injective K h.point_ne_zero (congrArg Subtype.val he)
  let : Finite (Submodule.span (ZMod 2) {v}) := Module.finite_of_finite (ZMod 2)
  have hc := Nat.card_le_card_of_injective f hi
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Submodule.span (ZMod 2) {v}),
    finrank_span_singleton h.point_ne_zero,Nat.card_zmod,pow_one] at hc
  exact hc
/-- For a semilinear elementary actor the fixed coefficient field is binary,
and its coefficient image has order at most two. -/
theorem coefficient_card_le_four_of_semilinear
    {K : Type*} [Field K] [Finite K] [Algebra (ZMod 2) K] [Module K V]
    [IsScalarTower (ZMod 2) K V]
    (φ : X →* (K ≃+* K))
    (hsemi : ∀ (x : X) (c : K) w, ρ x (c • w) = φ x c • ρ x w)
    (hd : 3 ≤ finrank (ZMod 2) W) : Nat.card K ≤ 4 := by
  classical
  let C := φ.range
  let : Finite C := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  let := Fintype.ofFinite C
  let : FaithfulSMul C K := ⟨fun h => Subtype.ext (RingEquiv.ext h)⟩
  let k := FixedPoints.subfield C K
  have hc : Nat.card C ≤ 2 := SL2NaturalOffenders.fieldAction_range_card_le_two X inferInstance φ
  have hdegree : finrank k K = Nat.card C := by
    simpa only [k,Nat.card_eq_fintype_card] using FixedPoints.finrank_eq_card C K
  let f : k → Submodule.span (ZMod 2) {v} := fun c => ⟨(c : K) • v,by
    by_cases hz : (c : K) = 0
    · simp only [hz,zero_smul,Submodule.zero_mem]
    · let J := (LinearEquiv.smulOfNeZero K V (c : K) hz).restrictScalars (ZMod 2)
      have hj : J v = v := h.centralizingLinearEquiv_fixes_point J (by
        intro x w
        change ρ x ((c : K) • w) = (c : K) • ρ x w
        rw [hsemi,show φ x (c : K) = (c : K) from c.property ⟨φ x,⟨x,rfl⟩⟩]) hd
      change (c : K) • v ∈ _
      rw [show (c : K) • v = v from hj]
      exact Submodule.mem_span_singleton_self _⟩
  have hi : Function.Injective f := by
    intro a b he
    exact Subtype.ext (smul_left_injective K h.point_ne_zero (congrArg Subtype.val he))
  let : Finite (Submodule.span (ZMod 2) {v}) := Module.finite_of_finite (ZMod 2)
  have hk := Nat.card_le_card_of_injective f hi
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Submodule.span (ZMod 2) {v}),
    finrank_span_singleton h.point_ne_zero,Nat.card_zmod,pow_one] at hk
  calc
    Nat.card K = Nat.card k ^ Nat.card C := by
      rw [Module.natCard_eq_pow_finrank (K := k),hdegree]
    _ ≤ 2 ^ Nat.card C := Nat.pow_le_pow_left hk _
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) hc
    _ = 4 := by norm_num
end CFSG.Quasithin.ChapterG.Section10.Hypothesis
