module
public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.ElementaryPlanes
public import Theory.GroupTheory.PGroup.AnisotropicFactors

/-!
# Complete anisotropic square fibers in UT₃(F₄)

A nonzero central square has at most twelve roots: its x coordinate is
nonzero, its y coordinate is determined by x, and the central coordinate
is arbitrary. The twelve noncentral elements of an anisotropic sixteen
therefore exhaust that fiber. The result transports through an actual
multiplicative equivalence and retains the given subgroup and square value.

Source application: the field-four splitting in DGS, Groups and Graphs
(1985), (10.9), p.163, using (5.16), pp.116–117.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.HyperbolicRecognition
open Matrix.PSL3Four Matrix.PSL3Four.SylowModel

private theorem root_square_fiber_le (z : center RootNormalizerModel.Root) (hz : z ≠ 1) :
    Nat.card {x : RootNormalizerModel.Root // x ^ 2 = (z : RootNormalizerModel.Root)} ≤ 12 := by
  classical
  have hzc : z.val.c ≠ 0 := by
    intro hc
    apply hz
    apply Subtype.ext
    obtain ⟨hx,hy⟩ := (mem_center_U z.val).mp z.property
    exact U.ext hx hy hc
  have hs (x : {x : RootNormalizerModel.Root // x ^ 2 = (z : RootNormalizerModel.Root)}) :
      x.val.x * x.val.y = z.val.c := by
    have hh := congrArg U.c x.property
    simpa only [pow_two,mul_c,CharTwo.add_self_eq_zero,zero_add] using hh
  let f : {x : RootNormalizerModel.Root // x ^ 2 = (z : RootNormalizerModel.Root)} →
      {v : F // v ≠ 0} × F := fun x =>
    (⟨x.val.x,fun hx => hzc (by rw [←hs x,hx,zero_mul])⟩,x.val.c)
  have hf : Function.Injective f := by
    intro x y hxy
    have hx : x.val.x = y.val.x := congrArg (fun a => a.1.val) hxy
    have hc : x.val.c = y.val.c := congrArg Prod.snd hxy
    have hy : x.val.y = y.val.y := by
      apply mul_left_cancel₀ (f x).1.property
      change x.val.x * x.val.y = x.val.x * y.val.y
      rw [hs x,hx,hs y]
    exact Subtype.ext (U.ext hx hy hc)
  have hh := Nat.card_le_card_of_injective f hf
  have hF : Nat.card {v : F // v ≠ 0} = 3 := by
    let := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    simp only [Fintype.card_unique,←Nat.card_eq_fintype_card,card_F]
  simpa only [Nat.card_prod,hF,card_F] using hh

/-- An anisotropic sixteen contains the entire fiber of its nontrivial square. -/
theorem anisotropic_square_fiber_exhausted {H : Type*} [Group H] [Finite H]
    (e : H ≃* RootNormalizerModel.Root) (A : Subgroup H)
    (hA : Nat.card A = 16) (hZA : center H ≤ A)
    (z : center H) (hz : z ≠ 1)
    (hs : ∀ x ∈ A, x ∉ center H → x ^ 2 = (z : H)) :
    ∀ x : H, x ^ 2 = (z : H) → x ∈ A := by
  classical
  let C := (center H).subgroupOf A
  have hC : Nat.card C = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZA).toEquiv,
      Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact (Nat.card_congr (show center RootNormalizerModel.Root ≃ F from
      { toFun := fun x => x.val.c
        invFun := fun c => ⟨⟨0,0,c⟩,(mem_center_U _).mpr ⟨rfl,rfl⟩⟩
        left_inv := fun x => Subtype.ext (U.ext
          ((mem_center_U x.val).mp x.property).1.symm
          ((mem_center_U x.val).mp x.property).2.symm rfl)
        right_inv := fun _ => rfl })).trans card_F
  have hdomain : Nat.card {a : A // a.val ∉ center H} = 12 := by
    let := Fintype.ofFinite A
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    simp only [←Nat.card_eq_fintype_card]
    change Nat.card A - Nat.card C = 12
    rw [hA,hC]
  let f : {a : A // a.val ∉ center H} → {x : H // x ^ 2 = (z : H)} :=
    fun a => ⟨a.val,hs a.val a.val.property a.property⟩
  have hi : Function.Injective f := by
    intro x y hxy
    have hh : x.val.val = y.val.val := congrArg (fun t : {v : H // v ^ 2 = (z : H)} => t.val) hxy
    exact Subtype.ext (Subtype.ext hh)
  have hbound : Nat.card {x : H // x ^ 2 = (z : H)} ≤ 12 := by
    rw [Theory.GroupTheory.squareFiber_card_eq e]
    exact root_square_fiber_le (Subgroup.centerCongr e z)
      (fun hh => hz ((Subgroup.centerCongr e).injective (by simpa using hh)))
  have hcard : Nat.card {x : H // x ^ 2 = (z : H)} = 12 := by
    have hh := Nat.card_le_card_of_injective f hi
    omega
  have hf := (Nat.bijective_iff_injective_and_card f).mpr ⟨hi,hdomain.trans hcard.symm⟩
  intro x hx
  obtain ⟨y,hy⟩ := hf.2 ⟨x,hx⟩
  have hh : y.val.val = x := congrArg Subtype.val hy
  exact hh ▸ y.val.property
end Theory.GroupTheory.HyperbolicRecognition

