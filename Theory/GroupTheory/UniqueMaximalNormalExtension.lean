module

public import Theory.Order.UniqueMaximalOver
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.SetLike.Fintype

/-!
# Unique maximal overgroups in normal extensions

Unique maximality lifts through a surjection when its kernel lies in the
specified subgroup. If Q normalizes L and L has a unique maximal subgroup M
above L ∩ Q, conjugation by Q preserves M. The product MQ is proper in LQ,
and the subgroup product formula puts every proper overgroup of Q in MQ.
Normality is required only in the generated extension.

These elementary subgroup-lattice arguments handle arbitrary kernels and
central extensions. Source application: Aschbacher–Smith, combined manuscript
(1 March 2004), proof of E.6.14, printed p.251.
-/

open Subgroup
open scoped Pointwise

namespace Subgroup
variable {G A : Type*} [Group G] [Group A] [Finite G]

omit [Finite G] in
private theorem hasUniqueMaximalOver_of_greatest {x m u : Subgroup G} (hxm : x ≤ m) (hmu : m < u)
    (hm : ∀ v, x ≤ v → v < u → v ≤ m) : Order.HasUniqueMaximalOver x u := by
  have hc : m ⋖ u := ⟨hmu, fun v hmv hvu => (not_lt_of_ge (hm v (hxm.trans hmv.le) hvu)) hmv⟩
  refine ⟨hxm.trans_lt hmu, m, ⟨hxm, hc⟩, ?_⟩
  intro v hv
  exact ((hv.2.eq_or_eq (hm v hv.1 hv.2.lt) hmu.le).resolve_right hmu.ne).symm

/-- Lift unique maximality through a surjection whose kernel lies in the supplied subgroup. -/
public theorem hasUniqueMaximalOver_of_surjective (f : G →* A)
    (hf : Function.Surjective f) {S : Subgroup G}
    (hk : f.ker ≤ S) (h : Order.HasUniqueMaximalOver (S.map f) ⊤) :
    Order.HasUniqueMaximalOver S ⊤ := by
  let : Finite A := Finite.of_surjective f hf
  obtain ⟨M, hM, _⟩ := h.2
  apply hasUniqueMaximalOver_of_greatest (m := M.comap f) (map_le_iff_le_comap.mp hM.1)
  · exact lt_top_iff_ne_top.mpr (fun he => hM.2.ne (by
      have hh := congrArg (map f) he
      simpa only [map_comap_eq_self_of_surjective hf, map_top_of_surjective f hf] using hh))
  · intro V hSV hV
    apply map_le_iff_le_comap.mp
    apply h.le_maximal hM (map_mono hSV)
    apply lt_top_iff_ne_top.mpr
    intro he
    have hh := congrArg (comap f) he
    rw [comap_map_eq_self (hk.trans hSV), comap_top] at hh
    exact hV.ne hh

/-- Regard intrinsic unique maximality as an interval in the ambient subgroup lattice. -/
public theorem hasUniqueMaximalOver_map_subtype {L : Subgroup G} {S : Subgroup L}
    (h : Order.HasUniqueMaximalOver S ⊤) :
    Order.HasUniqueMaximalOver (S.map L.subtype) L := by
  obtain ⟨M, hM, _⟩ := h.2
  apply hasUniqueMaximalOver_of_greatest (m := M.map L.subtype) (map_mono hM.1)
  · apply lt_of_le_of_ne (map_subtype_le _)
    intro he
    have ht : M = ⊤ := by
      ext x
      constructor
      · exact fun _ => mem_top _
      · intro _
        have hx : (x : G) ∈ M.map L.subtype := by rw [he]; exact x.property
        obtain ⟨y, hy, hyx⟩ := hx
        exact (Subtype.ext hyx : y = x) ▸ hy
    exact hM.2.ne ht
  · intro V hSV hV
    have hVM : V.subgroupOf L ≤ M := by
      apply h.le_maximal hM
      · intro x hx
        exact hSV (mem_map.mpr ⟨x, hx, rfl⟩)
      · apply lt_top_iff_ne_top.mpr
        intro he
        have hh := congrArg (map L.subtype) he
        rw [map_subgroupOf_eq_of_le hV.le, ← MonoidHom.range_eq_map, range_subtype] at hh
        exact hV.ne hh
    rw [← map_subgroupOf_eq_of_le hV.le]
    exact map_mono hVM

/-- Unique maximality over the intersection with a normalized subgroup extends to the join. -/
public theorem hasUniqueMaximalOver_sup_of_normalizes {L Q : Subgroup G}
    (hn : Q ≤ normalizer (L : Set G))
    (h : Order.HasUniqueMaximalOver (L ⊓ Q) L) :
    Order.HasUniqueMaximalOver Q (L ⊔ Q) := by
  obtain ⟨M, hM, _⟩ := h.2
  have hQM : Q ≤ normalizer (M : Set G) := by
    intro q hq
    let e := MulAut.conj q
    have hL : L.map e.toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp (hn hq)
    have hI : (L ⊓ Q).map e.toMonoidHom = L ⊓ Q :=
      mem_normalizer_iff_map_conj_eq.mp
        (inf_normalizer_le_normalizer_inf ⟨hn hq, Q.le_normalizer hq⟩)
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply h.2.unique _ hM
    constructor
    · rw [← hI]
      exact map_mono hM.1
    · have hc := (apply_covBy_apply_iff e.mapSubgroup).mpr hM.2
      change M.map e.toMonoidHom ⋖ L.map e.toMonoidHom at hc
      rwa [hL] at hc
  have product {A B : Subgroup G} (hnB : B ≤ normalizer (A : Set G))
      {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
    have hh : x ∈ (A : Set G) * (B : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left A B hnB]
      exact hx
    exact hh
  have hproper : M ⊔ Q < L ⊔ Q := by
    apply lt_of_le_of_ne (sup_le_sup hM.2.le le_rfl)
    intro he
    apply hM.2.ne
    apply le_antisymm hM.2.le
    intro x hx
    have hxMQ : x ∈ M ⊔ Q := by rw [he]; exact mem_sup_left hx
    obtain ⟨m, hm, q, hq, hmq⟩ := product hQM hxMQ
    have hqL : q ∈ L := by
      have hh := L.mul_mem (L.inv_mem (hM.2.le hm)) hx
      rwa [← hmq, inv_mul_cancel_left] at hh
    rw [← hmq]
    exact M.mul_mem hm (hM.1 ⟨hqL, hq⟩)
  apply hasUniqueMaximalOver_of_greatest le_sup_right hproper
  intro V hQV hV
  have hVL : V ⊓ L < L := by
    apply lt_of_le_of_ne inf_le_right
    intro he
    have hLV : L ≤ V := he ▸ (inf_le_left : V ⊓ L ≤ V)
    exact hV.not_ge (sup_le hLV hQV)
  have hVM : V ⊓ L ≤ M := h.le_maximal hM
    (le_inf (inf_le_right.trans hQV) inf_le_left) hVL
  intro x hx
  obtain ⟨l, hl, q, hq, hlq⟩ := product hn (hV.le hx)
  have hlV : l ∈ V := by
    have hh := V.mul_mem hx (V.inv_mem (hQV hq))
    rwa [← hlq, mul_inv_cancel_right] at hh
  rw [← hlq]
  exact mul_mem_sup (hVM ⟨hlV, hl⟩) hq

end Subgroup
