module

public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Centers of Sylow subgroups in binary linear groups

Every Sylow two-subgroup of GLₙ(2), SLₙ(2), or PSLₙ(2), for `n ≥ 2`, has
center of order at most two. In particular this supplies the linear component
bound used in Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 15.4.20, combined manuscript of 1 March 2004, printed p.1164.

Choose a coordinate line `L` inside a coordinate hyperplane `H`. Their
block-unipotent radicals generate a two-group because the latter normalizes
the former. Place this two-group in a Sylow subgroup `P`. Each radical is
self-centralizing, so `Z(P)` lies in their intersection. A transformation in
that intersection is determined by a single binary coordinate: it fixes `H`
pointwise and its displacement has image in `L`. Sylow conjugacy gives the
bound for every Sylow subgroup, without a group order computation.

The matrix/linear-map equivalence and the determinant-one property over the
binary field transfer the result to SL. Its scalar center is trivial, so the
actual quotient projection gives the comparison with PSL; the projective
quotient is retained throughout.
-/

open Subgroup
namespace BinaryLinear

private theorem radical_normalizes_of_le {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {L H : Submodule (ZMod 2) V} (hLH : L ≤ H) :
    radical H ≤ Subgroup.normalizer (radical L : Set _) := by
  apply le_trans _ (parabolic_le_normalizer L)
  intro g hg v
  constructor
  · intro hv
    have he : g v = v := g.injective (hg.1 (g v) (hLH hv))
    rwa [he] at hv
  · intro hv
    simpa only [hg.1 v (hLH hv)] using hv

private theorem center_mem_radical {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {W : Submodule (ZMod 2) V} (hW : W ≠ ⊥) (hWt : W ≠ ⊤)
    {S : Subgroup (BinaryLinear.GL V)} (hWS : radical W ≤ S) (z : center S) :
    (z.val.val : BinaryLinear.GL V) ∈ radical W := by
  apply centralizer_radical_le hW hWt
  apply mem_centralizer_iff.mpr
  intro g hg
  exact congrArg Subtype.val (mem_center_iff.mp z.property (⟨g, hWS hg⟩ : S))

variable {ι : Type*} [DecidableEq ι]

private theorem radical_intersection_injective (i j : ι) :
    Function.Injective (fun g : ↥(radical (Submodule.span (ZMod 2) {Pi.single i 1}) ⊓
      radical (LinearMap.proj j : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2).ker) =>
        (g.val (Pi.single j 1)) i) := by
  intro g h heq
  change g.val (Pi.single j 1) i = h.val (Pi.single j 1) i at heq
  have hj : g.val (Pi.single j 1) = h.val (Pi.single j 1) := by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (g.property.1.2 (Pi.single j 1))
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (h.property.1.2 (Pi.single j 1))
    have hab : a = b := by
      have ha' := congrFun ha i
      have hb' := congrFun hb i
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
        Pi.sub_apply] at ha' hb'
      rw [ha', hb', heq]
    have := ha.symm.trans (hab ▸ hb)
    exact sub_left_inj.mp this
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hv : v - v j • Pi.single j 1 ∈
      (LinearMap.proj j : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2).ker := by
    simp
  have hg := g.property.2.1 _ hv
  have hh := h.property.2.1 _ hv
  simp only [map_sub, map_smul] at hg hh
  rw [hj] at hg
  exact sub_left_inj.mp (hg.trans hh.symm)

private theorem sylow_center_bound [Fintype ι] (i j : ι) (hij : i ≠ j)
    (S : Sylow 2 (BinaryLinear.GL (ι → ZMod 2))) : Nat.card (center S) ≤ 2 := by
  let L : Submodule (ZMod 2) (ι → ZMod 2) := Submodule.span (ZMod 2) {Pi.single i 1}
  let H := (LinearMap.proj j : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2).ker
  have he : Pi.single i (1 : ZMod 2) ∈ L := Submodule.mem_span_singleton_self _
  have hLH : L ≤ H := by
    apply Submodule.span_le.mpr
    intro v hv
    obtain rfl := Set.mem_singleton_iff.mp hv
    simp [H, hij.symm]
  have hL : L ≠ ⊥ := by
    intro h
    simp [h] at he
  have hHt : H ≠ ⊤ := by
    intro h
    have ht : Pi.single j (1 : ZMod 2) ∈ H := h ▸ Submodule.mem_top
    simp [H] at ht
  have hLt : L ≠ ⊤ := ne_top_of_le_ne_top hHt hLH
  have hH : H ≠ ⊥ := ne_bot_of_le_ne_bot hL hLH
  have hp := (radical_two L).to_sup_of_normal_left' (radical_two H)
    (radical_normalizes_of_le hLH)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hLP : radical L ≤ (P : Subgroup _) := le_sup_left.trans hP
  have hHP : radical H ≤ (P : Subgroup _) := le_sup_right.trans hP
  let f : center P → ↥(radical L ⊓ radical H) := fun z =>
    ⟨z.val.val, center_mem_radical hL hLt hLP z, center_mem_radical hH hHt hHP z⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun g : ↥(radical L ⊓ radical H) => g.val) hab
  have hb : Nat.card (center P) ≤ 2 := by
    have := Nat.card_le_card_of_injective
      ((fun g : ↥(radical L ⊓ radical H) => (g.val (Pi.single j 1)) i) ∘ f)
      ((radical_intersection_injective i j).comp hf)
    simpa using this
  let : Finite (BinaryLinear.GL (ι → ZMod 2)) :=
    Finite.of_injective (fun g : BinaryLinear.GL (ι → ZMod 2) => (g : _ → _))
      DFunLike.coe_injective
  rw [Nat.card_congr (centerCongr (S.equiv P)).toEquiv]
  exact hb

/-- The center bound for the group of invertible binary linear maps. -/
public theorem linear_sylow_center_card_le_two {n : ℕ} (hn : 2 ≤ n)
    (S : Sylow 2 (BinaryLinear.GL (Fin n → ZMod 2))) : Nat.card (center S) ≤ 2 :=
  sylow_center_bound (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ (by intro h; have := congrArg Fin.val h; simp at this) S

/-- Multiplicative equivalences preserve the center order of the transported Sylow subgroup. -/
public theorem sylow_center_card_congr {G K : Type*} [Group G] [Group K] [Finite G]
    (e : G ≃* K) (S : Sylow 2 G) :
    Nat.card (center S) = Nat.card (center (S.mapSurjective (f := e.toMonoidHom) e.surjective)) :=
  Nat.card_congr (centerCongr ((S : Subgroup G).equivMapOfInjective
    e.toMonoidHom e.injective)).toEquiv

private noncomputable def matrixEquivLinear (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin n) (ZMod 2) ≃*
      BinaryLinear.GL (Fin n → ZMod 2) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin n → ZMod 2))

/-- The center bound for the actual binary general linear matrix group. -/
public theorem matrix_sylow_center_card_le_two {n : ℕ} (hn : 2 ≤ n)
    (S : Sylow 2 (Matrix.GeneralLinearGroup (Fin n) (ZMod 2))) :
    Nat.card (center S) ≤ 2 := by
  rw [sylow_center_card_congr (matrixEquivLinear n) S]
  exact linear_sylow_center_card_le_two hn _

open scoped MatrixGroups

private theorem binary_toGL_surjective (n : ℕ) :
    Function.Surjective (Matrix.SpecialLinearGroup.toGL :
      SL(n, ZMod 2) →* Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) := by
  intro g
  have hu : ∀ u : (ZMod 2)ˣ, u = 1 := by decide
  have hd : Matrix.det (g : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 :=
    congrArg Units.val (hu (Matrix.GeneralLinearGroup.det g))
  exact ⟨⟨g, hd⟩, Units.ext rfl⟩

private noncomputable def slEquivMatrix (n : ℕ) :
    SL(n, ZMod 2) ≃* Matrix.GeneralLinearGroup (Fin n) (ZMod 2) :=
  MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, binary_toGL_surjective n⟩

/-- The center bound for the actual binary special linear group. -/
public theorem sl_sylow_center_card_le_two {n : ℕ} (hn : 2 ≤ n)
    (S : Sylow 2 SL(n, ZMod 2)) : Nat.card (center S) ≤ 2 := by
  rw [sylow_center_card_congr (slEquivMatrix n) S]
  exact matrix_sylow_center_card_le_two hn _

private theorem binary_center_eq_bot {n : ℕ} (hn : 0 < n) :
    Subgroup.center SL(n, ZMod 2) = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  change g = 1
  obtain ⟨a, ha, hga⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have ha0 : a ≠ 0 := by
    intro hzero
    simp [hzero, hn.ne'] at ha
  have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
  apply Subtype.ext
  simpa [ha1] using hga.symm

private noncomputable def projectiveEquivSL {n : ℕ} (hn : 0 < n) :
    PSL(n, ZMod 2) ≃* SL(n, ZMod 2) :=
  (MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center SL(n, ZMod 2)))
    ⟨by rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', binary_center_eq_bot hn],
      QuotientGroup.mk'_surjective _⟩).symm

/-- The center bound for the actual binary projective special linear quotient. -/
public theorem psl_sylow_center_card_le_two {n : ℕ} (hn : 2 ≤ n)
    (S : Sylow 2 PSL(n, ZMod 2)) : Nat.card (center S) ≤ 2 := by
  rw [sylow_center_card_congr (projectiveEquivSL (by omega : 0 < n)) S]
  exact sl_sylow_center_card_le_two hn _

end BinaryLinear
