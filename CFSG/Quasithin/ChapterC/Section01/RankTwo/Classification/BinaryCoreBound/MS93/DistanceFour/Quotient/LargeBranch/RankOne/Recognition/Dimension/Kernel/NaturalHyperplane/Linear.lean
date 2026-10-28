module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Push
/-!
# A hyperplane in two binary natural modules

A nonidentity involution fixes a plane in two natural SL2(2) copies. If its
image on a subspace of dimension at least three lies in an ambient line,
that image is nonzero. Rank-nullity forces the fixed plane into the subspace.
The elementary rank-one matrix identity then puts every translate of the
image line back in the subspace. The ambient line is not assumed to lie in
the four-dimensional module: its containment follows from nonzero displacement.

This is the linear argument used in Meierfrankenfeld--Stellmacher (1993),
Pushing up weak BN-pairs of rank two, (4.6.12)(5), printed p.912.
-/

@[expose] public section
open Matrix
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.NaturalHyperplane
/-- Binary coefficient field. -/
abbrev K := ZMod 2
/-- One natural module. -/
abbrev E := Fin 2 → K
/-- Two identically marked natural copies. -/
abbrev W := Fin 2 → E
/-- The full binary rank-one group. -/
abbrev G := Matrix.SpecialLinearGroup (Fin 2) K

/-- The diagonal matrix action. -/
def act (t : G) : W →ₗ[K] W :=
  LinearMap.pi fun j => t.val.mulVecLin.comp (LinearMap.proj j)
/-- Displacement by one group element. -/
def disp (t : G) : W →ₗ[K] W := act t - LinearMap.id

private theorem fixed_count : ∀ t : G, t ≠ 1 → t * t = 1 →
    (Finset.univ.filter fun v : W => (fun j => t.val.mulVec (v j)) = v).card = 4 := by
  decide +kernel

private theorem involutions : ∀ t : G, t ≠ 1 → t * t = 1 →
    t.val = !![1,1;0,1] ∨ t.val = !![1,0;1,1] ∨ t.val = !![0,1;1,0] := by
  decide +kernel

private def nilpotent (i : Fin 3) : Matrix (Fin 2) (Fin 2) K :=
  ![!![0,1;0,0], !![0,0;1,0], !![1,1;1,1]] i

private theorem sandwich_small : ∀ i : Fin 3, ∀ A : Matrix (Fin 2) (Fin 2) K,
    nilpotent i * A * nilpotent i = 0 ∨
      nilpotent i * A * nilpotent i = nilpotent i := by
  decide +kernel

private theorem sandwich (t g : G) (ht : t ≠ 1) (htt : t * t = 1) :
    (t.val - 1) * g.val * (t.val - 1) = 0 ∨
      (t.val - 1) * g.val * (t.val - 1) = t.val - 1 := by
  rcases involutions t ht htt with h | h | h
  · have he : (!![1,1;0,1] : Matrix (Fin 2) (Fin 2) K) - 1 = nilpotent 0 := by decide
    rw [h, he]
    exact sandwich_small 0 g.val
  · have he : (!![1,0;1,1] : Matrix (Fin 2) (Fin 2) K) - 1 = nilpotent 1 := by decide
    rw [h, he]
    exact sandwich_small 1 g.val
  · have he : (!![0,1;1,0] : Matrix (Fin 2) (Fin 2) K) - 1 = nilpotent 2 := by decide
    rw [h, he]
    exact sandwich_small 2 g.val

private theorem ker_finrank (t : G) (ht : t ≠ 1) (htt : t * t = 1) :
    Module.finrank K (disp t).ker = 2 := by
  classical
  have hc : Nat.card (disp t).ker = 4 := by
    change Nat.card { v : W // disp t v = 0 } = 4
    rw [Nat.card_eq_fintype_card]
    simp only [disp, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    rw [Fintype.card_subtype]
    exact fixed_count t ht htt
  rw [Module.natCard_eq_pow_finrank (K := K), Nat.card_zmod] at hc
  have h : 2 ^ Module.finrank K (disp t).ker = 2 ^ 2 := hc
  exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) h

private theorem orbit_displacement (t g : G) (ht : t ≠ 1) (htt : t * t = 1)
    (v : W) : disp t (act g (disp t v)) = 0 ∨
      disp t (act g (disp t v)) = disp t v := by
  have he (v : W) (j : Fin 2) : disp t v j = (t.val - 1).mulVec (v j) := by
    simp [disp, act, Matrix.sub_mulVec]
  rcases sandwich t g ht htt with h | h
  · left
    ext j i
    have hh := congrFun (congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A.mulVec (v j)) h) i
    simpa only [he, act, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, mul_assoc, Matrix.zero_mulVec, Pi.zero_apply] using hh
  · right
    ext j i
    have hh := congrFun (congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A.mulVec (v j)) h) i
    simpa only [he, act, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, mul_assoc] using hh

variable {V : Type*} [AddCommGroup V] [Module K V] [Finite V]

/-- Nonzero displacement recovers the ambient line, and its full group orbit
is contained in the original subspace. -/
theorem line_orbit (e : W →ₗ[K] V) (he : Function.Injective e)
    (t : G) (ht : t ≠ 1) (htt : t * t = 1)
    (H : Submodule K W) (hH : 3 ≤ Module.finrank K H)
    (L : Submodule K V) (hL : Module.finrank K L = 1)
    (hbound : ∀ v ∈ H, e (disp t v) ∈ L) :
    ∃ v ∈ H, disp t v ≠ 0 ∧ L = Submodule.span K {e (disp t v)} ∧
      ∀ g : G, act g (disp t v) ∈ H := by
  have hk := ker_finrank t ht htt
  have bound (S : Submodule K W) (hS : ∀ v ∈ S, e (disp t v) ∈ L) :
      Module.finrank K S ≤ 3 := by
    let F : S →ₗ[K] V := (e.comp (disp t)).comp S.subtype
    have hr : F.range ≤ L := by
      rintro _ ⟨v, rfl⟩
      exact hS v v.property
    have hrank := Submodule.finrank_mono hr
    rw [hL] at hrank
    let k : F.ker →ₗ[K] (disp t).ker :=
      (S.subtype.comp F.ker.subtype).codRestrict _ (by
        intro v
        change disp t (v : S) = 0
        apply he
        simpa only [map_zero] using (show e (disp t (v : S)) = 0 from v.property))
    have hkinj : Function.Injective k := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : (disp t).ker => (z : W)) h
    have hkrank := LinearMap.finrank_le_finrank_of_injective hkinj
    rw [hk] at hkrank
    have hadd := F.finrank_range_add_finrank_ker
    omega
  have hsumBound : ∀ v ∈ H ⊔ (disp t).ker, e (disp t v) ∈ L := by
    change H ⊔ (disp t).ker ≤ L.comap (e.comp (disp t))
    apply sup_le
    · exact hbound
    · intro v hv
      change e (disp t v) ∈ L
      rw [show disp t v = 0 from hv, map_zero]
      exact L.zero_mem
  have hsum := bound _ hsumBound
  have hsumEq : H = H ⊔ (disp t).ker :=
    Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
  have hkerH : (disp t).ker ≤ H := by
    rw [hsumEq]
    exact le_sup_right
  have hex : ∃ v ∈ H, disp t v ≠ 0 := by
    by_contra! hn
    have hle : H ≤ (disp t).ker := hn
    have hd := Submodule.finrank_mono hle
    omega
  obtain ⟨v, hv, hv0⟩ := hex
  have he0 : e (disp t v) ≠ 0 := by
    intro h
    exact hv0 (he (h.trans (map_zero e).symm))
  have hspan : Submodule.span K {e (disp t v)} = L := by
    apply Submodule.eq_of_le_of_finrank_le
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (hbound v hv))
    · rw [hL, finrank_span_singleton he0]
  refine ⟨v, hv, hv0, hspan.symm, ?_⟩
  intro g
  rcases orbit_displacement t g ht htt v with hz | hz
  · exact hkerH hz
  · have hx : act g (disp t v) - v ∈ (disp t).ker := by
      change disp t (act g (disp t v) - v) = 0
      rw [map_sub, hz, sub_self]
    simpa only [sub_add_cancel] using H.add_mem (hkerH hx) hv
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.NaturalHyperplane
