module

public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapDiagonal
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Fixed elements in a central product of swapped factors

If P and its conjugate by an involution commute, multiplication gives a
surjection from P × P onto their join. A fixed element with coordinates
(p,q) differs from the norm of p by an element of the intersection of the
two factors. That intersection is central in the join. This proves the
fixed-center supplement without assuming a direct product or a trivial center.

Source: GLS2, Chapter B, Lemma 3.27, first paragraph of the proof.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem commutingSwap_commute (P : Subgroup G) (a : G)
    (hc : P ≤ centralizer (P.map (MulAut.conj a).toMonoidHom : Set G))
    (x y : P) : Commute (P.subtype x)
      (((MulAut.conj a).toMonoidHom.comp P.subtype) y) :=
  (mem_centralizer_iff.mp (hc x.property) _ (mem_map_of_mem _ y.property)).symm

/-- The norm map for two commuting subgroups interchanged by conjugation. -/
def commutingSwapNorm (P : Subgroup G) (a : G)
    (hc : P ≤ centralizer (P.map (MulAut.conj a).toMonoidHom : Set G)) : P →* G :=
  (P.subtype.noncommCoprod ((MulAut.conj a).toMonoidHom.comp P.subtype)
    (commutingSwap_commute P a hc)).comp ((MonoidHom.id P).prod (MonoidHom.id P))

@[simp] theorem commutingSwapNorm_apply (P : Subgroup G) (a : G)
    (hc : P ≤ centralizer (P.map (MulAut.conj a).toMonoidHom : Set G)) (x : P) :
    commutingSwapNorm P a hc x = (x : G) * (a * x * a⁻¹) := rfl

private theorem conj_twice {a : G} (ha : a ^ 2 = 1) (x : G) :
    MulAut.conj a (MulAut.conj a x) = x := by
  have haa : a * a = 1 := by simpa [pow_two] using ha
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  simp only [MulAut.conj_apply, hai]
  calc
    a * (a * x * a) * a = (a * a) * x * (a * a) := by group
    _ = x := by rw [haa, one_mul, mul_one]

theorem commutingSwapNorm_range_le_centralizer (P : Subgroup G) (a : G)
    (hc : P ≤ centralizer (P.map (MulAut.conj a).toMonoidHom : Set G))
    (ha : a ^ 2 = 1) :
    (commutingSwapNorm P a hc).range ≤ centralizer ({a} : Set G) := by
  rintro _ ⟨x, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have hcomm := (mem_centralizer_iff.mp (hc x.property) _
    (mem_map_of_mem (MulAut.conj a).toMonoidHom x.property)).symm
  have he : MulAut.conj a (commutingSwapNorm P a hc x) = commutingSwapNorm P a hc x := by
    change MulAut.conj a ((x : G) * MulAut.conj a x) = (x : G) * MulAut.conj a x
    rw [map_mul, conj_twice ha]
    exact hcomm.symm
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- A fixed element of a central product of swapped factors is a norm times
an element of the fixed center. No direct-product hypothesis is used. -/
theorem centralizer_sup_conjugate_eq_norm_sup_center
    (P : Subgroup G) (a : G)
    (hc : P ≤ centralizer (P.map (MulAut.conj a).toMonoidHom : Set G))
    (ha : a ^ 2 = 1) :
    let E := P ⊔ P.map (MulAut.conj a).toMonoidHom
    E ⊓ centralizer ({a} : Set G) =
      (commutingSwapNorm P a hc).range ⊔
        ((center E).map E.subtype ⊓ centralizer ({a} : Set G)) := by
  dsimp only
  let Q := P.map (MulAut.conj a).toMonoidHom
  let E := P ⊔ Q
  let n := commutingSwapNorm P a hc
  have hnC := commutingSwapNorm_range_le_centralizer P a hc ha
  have hnE : n.range ≤ E := by
    rintro _ ⟨x, rfl⟩
    exact mul_mem_sup x.property (mem_map_of_mem _ x.property)
  apply le_antisymm
  · rintro x ⟨hxE, hxC⟩
    let f : P × P →* G := P.subtype.noncommCoprod
      ((MulAut.conj a).toMonoidHom.comp P.subtype)
      (commutingSwap_commute P a hc)
    have hf : f.range = E := by
      dsimp only [f]
      rw [MonoidHom.noncommCoprod_range, MonoidHom.range_comp, range_subtype]
    have hxf : x ∈ f.range := by rw [hf]; exact hxE
    obtain ⟨⟨p,q⟩, hpq⟩ := hxf
    change (p : G) * MulAut.conj a q = x at hpq
    subst x
    have he : MulAut.conj a ((p : G) * MulAut.conj a q) =
        (p : G) * MulAut.conj a q :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hxC).symm
    rw [map_mul, conj_twice ha] at he
    let z : G := (MulAut.conj a p)⁻¹ * MulAut.conj a q
    have hzQ : z ∈ Q := mul_mem (inv_mem (mem_map_of_mem _ p.property))
      (mem_map_of_mem _ q.property)
    have hzP : z ∈ P := by
      have hpcomm : Commute (p : G) (MulAut.conj a p) := commutingSwap_commute P a hc p p
      have hze : z = (p : G)⁻¹ * q := by
        apply (mul_left_cancel_iff (a := (p : G))).mp
        dsimp only [z]
        calc
          (p : G) * ((MulAut.conj a p)⁻¹ * MulAut.conj a q) =
              (MulAut.conj a p)⁻¹ * ((p : G) * MulAut.conj a q) := by
                rw [← mul_assoc, hpcomm.inv_right.eq, mul_assoc]
          _ = (MulAut.conj a p)⁻¹ * (MulAut.conj a p * q) := by rw [he]
          _ = (p : G) * ((p : G)⁻¹ * q) := by group
      rw [hze]
      exact mul_mem (inv_mem p.property) q.property
    have hzE : z ∈ E := mem_sup_left hzP
    have hzEP : E ≤ centralizer ({z} : Set G) := by
      apply sup_le
      · intro y hy
        exact mem_centralizer_singleton_iff.mpr
          (mem_centralizer_iff.mp (le_centralizer_iff.mp hc hzQ) y hy)
      · intro y hy
        exact mem_centralizer_singleton_iff.mpr
          (mem_centralizer_iff.mp (hc hzP) y hy)
    have hzZ : z ∈ (center E).map E.subtype := by
      refine ⟨⟨z,hzE⟩, mem_center_iff.mpr ?_, rfl⟩
      intro y
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp (hzEP y.property)
    have hx : n p * z = (p : G) * MulAut.conj a q := by
      change ((p : G) * MulAut.conj a p) * ((MulAut.conj a p)⁻¹ * MulAut.conj a q) = _
      group
    have hzC : z ∈ centralizer ({a} : Set G) := by
      have hnp : n p ∈ centralizer ({a} : Set G) := hnC ⟨p,rfl⟩
      have hz := mul_mem (inv_mem hnp) hxC
      simpa only [← hx, inv_mul_cancel_left] using hz
    rw [← hx]
    exact mul_mem_sup ⟨p,rfl⟩ ⟨hzZ,hzC⟩
  · apply sup_le (le_inf hnE hnC)
    exact le_inf (inf_le_left.trans (map_subtype_le _)) inf_le_right

end Theory.GroupTheory

end
