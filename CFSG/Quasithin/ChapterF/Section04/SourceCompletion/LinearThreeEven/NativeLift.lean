module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeEven.NativeGeometry

/-!
# Exact native linear-three amalgam automorphisms

The native and twisted markings satisfy the same literal cubic word. Their
paired completion has a hexagon and diameter at most three. The first coset
cover is injective by the native short-cycle bound; its inverse followed by
the second projection gives the required automorphism, retaining every
endpoint element. Native finiteness makes this map surjective and injective.
Generation proves uniqueness and hence multiplicative coherence of the lifts.

The reverse adapter retains both endpoints and the entire common Borel.
No recognition or order bound for an unknown ambient group is used.
Source: the native compatible realization in Aschbacher–Smith 5.3.2, p.659,
and the marked refinement of F.4.8–10, pp.278–279 (`refs/quasithin.pdf`).
-/

@[expose] public noncomputable section
open Matrix Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.SmallCompletion
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
local notation "α" => GreenBook.LieModels.LinearThree.amalgam F
open NativeCompletion

theorem paired_diameter {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (e : RankTwoAmalgam.Iso α α) :
    let c := (modelCompletion F).pairCompletion ((modelCompletion F).comapIso e)
    ∀ v w : NativeCompletion.Vertex c, (NativeCompletion.graph c).dist v w ≤ 3 := by
  let c := modelCompletion F
  let d := c.comapIso e
  let z := c.pairCompletion d
  let x : pointParabolic F := ⟨reflection F false,reflection_mem F false⟩
  let y : lineParabolic F := ⟨reflection F true,reflection_mem F true⟩
  let s := z.left x
  let t := z.right y
  have hs : s ∈ z.left.range := ⟨x,rfl⟩
  have ht : t ∈ z.right.range := ⟨y,rfl⟩
  have hsout : s ∉ z.middle.range := by
    rintro ⟨b,hb⟩
    have he := congrArg (c.pairFst d) hb
    change c.pairFst d (z.left ((α).left b)) = c.pairFst d (z.left x) at he
    rw [c.pairFst_left d,c.pairFst_left d] at he
    change b.val = reflection F false at he
    exact reflection_not_mem_borel F false (he ▸ b.property)
  have htout : t ∉ z.middle.range := by
    rintro ⟨b,hb⟩
    have he := congrArg (c.pairFst d) hb
    change c.pairFst d (z.left ((α).left b)) = c.pairFst d (z.right y) at he
    rw [c.pairFst_left d,c.pairFst_right d] at he
    change b.val = reflection F true at he
    exact reflection_not_mem_borel F true (he ▸ b.property)
  have hs2 : s^2=1 := by
    change (z.left x)^2=1
    rw [←map_pow,show x^2=1 from Subtype.ext (reflection_sq F false),map_one]
  have ht2 : t^2=1 := by
    change (z.right y)^2=1
    rw [←map_pow,show y^2=1 from Subtype.ext (reflection_sq F true),map_one]
  have hc : (s*t)^3 ∈ z.middle.range := by
    rw [show (s*t)^3=1 from paired_reflections_cube F hF hn e]
    exact one_mem _
  have hex := NativeCompletion.exists_six_cycle_of_involutions z (paired_overlap F e) hF s t hs ht hsout htout hs2 ht2 hc
  exact NativeCompletion.diameter_le_three_of_six_cycle z (paired_overlap F e) hF hex

/-- Both prescribed endpoint maps extend pointwise to the concrete native group. -/
theorem native_amalgam_automorphism {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (e : RankTwoAmalgam.Iso α α) :
    ∃ A : MulAut PSL(3,F),
      (∀ x : pointParabolic F, A x.val = (e.left x).val) ∧
      (∀ y : lineParabolic F, A y.val = (e.right y).val) := by
  let c := modelCompletion F
  let d := c.comapIso e
  let z := c.pairCompletion d
  have hi : Function.Injective (c.pairFst d) := by
    apply (paired_first_cover F e).injective_of_diameter_lt_girth
      (NativeCompletion.connected z) (paired_diameter F hF hn e)
    intro v p hp
    have hh := NativeCompletion.cycle_length_gt_four c (model_overlap F) hF v p hp
    omega
  let f : c.Pair d ≃* PSL(3,F) :=
    MulEquiv.ofBijective (c.pairFst d) ⟨hi,(paired_first_cover F e).surjective⟩
  let a : PSL(3,F) →* PSL(3,F) := (c.pairSnd d).comp f.symm.toMonoidHom
  have ha : Function.Surjective a := (paired_second_cover F e).surjective.comp f.symm.surjective
  refine ⟨MulEquiv.ofBijective a ((Nat.bijective_iff_surjective_and_card a).mpr ⟨ha,rfl⟩), ?_, ?_⟩
  · intro x
    have hx : f.symm x.val = z.left x := by
      apply f.injective
      rw [f.apply_symm_apply]
      exact (c.pairFst_left d x).symm
    change c.pairSnd d (f.symm x.val) = _
    rw [hx,c.pairSnd_left d]
    rfl
  · intro y
    have hy : f.symm y.val = z.right y := by
      apply f.injective
      rw [f.apply_symm_apply]
      exact (c.pairFst_right d y).symm
    change c.pairSnd d (f.symm y.val) = _
    rw [hy,c.pairSnd_right d]
    rfl

omit [CharP F 2] in
/-- Endpoint generation makes exact native lifts unique. -/
theorem native_automorphism_ext (a b : MulAut PSL(3,F))
    (hl : ∀ x : pointParabolic F, a x.val = b x.val)
    (hr : ∀ y : lineParabolic F, a y.val = b y.val) : a=b := by
  have ht : (⊤ : Subgroup PSL(3,F)) ≤ a.toMonoidHom.eqLocus b.toMonoidHom := by
    rw [←parabolics_sup_eq_top F]
    exact sup_le (fun x hx => hl ⟨x,hx⟩) (fun y hy => hr ⟨y,hy⟩)
  ext x
  exact ht (mem_top x)

/-- The unique extension of the prescribed pair automorphism. -/
def nativeLift {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (e : RankTwoAmalgam.Iso α α) : MulAut PSL(3,F) :=
  (native_amalgam_automorphism F hF hn e).choose

theorem nativeLift_left {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (e : RankTwoAmalgam.Iso α α) (x : pointParabolic F) :
    nativeLift F hF hn e x.val = (e.left x).val :=
  (native_amalgam_automorphism F hF hn e).choose_spec.1 x

theorem nativeLift_right {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (e : RankTwoAmalgam.Iso α α) (y : lineParabolic F) :
    nativeLift F hF hn e y.val = (e.right y).val :=
  (native_amalgam_automorphism F hF hn e).choose_spec.2 y

theorem nativeLift_middle {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (e : RankTwoAmalgam.Iso α α) (b : borel F) :
    nativeLift F hF hn e b.val = (e.middle b).val :=
  (nativeLift_left F hF hn e ((α).left b)).trans (congrArg Subtype.val (e.left_commutes b))

theorem nativeLift_unique {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (e : RankTwoAmalgam.Iso α α) (a : MulAut PSL(3,F))
    (hl : ∀ x : pointParabolic F, a x.val = (e.left x).val)
    (hr : ∀ y : lineParabolic F, a y.val = (e.right y).val) :
    a = nativeLift F hF hn e :=
  native_automorphism_ext F a _ (fun x => (hl x).trans (nativeLift_left F hF hn e x).symm)
    (fun y => (hr y).trans (nativeLift_right F hF hn e y).symm)

/-- Uniqueness makes the exact extension multiplicative. -/
def nativeLiftHom {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n) :
    RankTwoAmalgam.Iso α α →* MulAut PSL(3,F) where
  toFun := nativeLift F hF hn
  map_one' := by
    apply native_automorphism_ext F
    · intro x; rw [nativeLift_left]; rfl
    · intro y; rw [nativeLift_right]; rfl
  map_mul' a b := by
    apply native_automorphism_ext F
    · intro x
      simp only [nativeLift_left, RankTwoAmalgam.Iso.mul_left, MulAut.mul_apply]
    · intro y
      simp only [nativeLift_right, RankTwoAmalgam.Iso.mul_right, MulAut.mul_apply]

/-- The lift retains the full compatible action, so it loses no kernel data. -/
theorem nativeLiftHom_injective {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n) :
    Function.Injective (nativeLiftHom F hF hn) := by
  intro a b h
  apply RankTwoAmalgam.Iso.ext
  · apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact (nativeLift_left F hF hn a x).symm.trans
      ((congrArg (fun f : MulAut PSL(3,F) => f x.val) h).trans (nativeLift_left F hF hn b x))
  · apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact (nativeLift_middle F hF hn a x).symm.trans
      ((congrArg (fun f : MulAut PSL(3,F) => f x.val) h).trans (nativeLift_middle F hF hn b x))
  · apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact (nativeLift_right F hF hn a x).symm.trans
      ((congrArg (fun f : MulAut PSL(3,F) => f x.val) h).trans (nativeLift_right F hF hn b x))

/-- The same lift with the native line endpoint first. -/
def nativeReverseLiftHom {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n) :
    RankTwoAmalgam.Iso (α).reverse (α).reverse →* MulAut PSL(3,F) :=
  (nativeLiftHom F hF hn).comp
    { toFun := RankTwoAmalgam.Iso.reverse
      map_one' := rfl
      map_mul' _ _ := rfl }

theorem nativeReverseLift_left {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (e : RankTwoAmalgam.Iso (α).reverse (α).reverse) (x : lineParabolic F) :
    nativeReverseLiftHom F hF hn e x.val = (e.left x).val :=
  nativeLift_right F hF hn e.reverse x

theorem nativeReverseLift_right {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (e : RankTwoAmalgam.Iso (α).reverse (α).reverse) (x : pointParabolic F) :
    nativeReverseLiftHom F hF hn e x.val = (e.right x).val :=
  nativeLift_left F hF hn e.reverse x

theorem nativeReverseLift_middle {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (e : RankTwoAmalgam.Iso (α).reverse (α).reverse) (b : borel F) :
    nativeReverseLiftHom F hF hn e b.val = (e.middle b).val :=
  nativeLift_middle F hF hn e.reverse b

theorem nativeReverseLiftHom_injective {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n) :
    Function.Injective (nativeReverseLiftHom F hF hn) := by
  intro a b h
  have hh : a.reverse=b.reverse := nativeLiftHom_injective F hF hn h
  exact congrArg RankTwoAmalgam.Iso.reverse hh

end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven
