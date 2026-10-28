module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Common normal subgroups and normalizer control

Three elementary tools used in Aschbacher–Smith, *The Classification of
Quasithin Groups*, combined manuscript (1 March 2004), §C.5:
* a commutator bound forces a candidate to be a common normal subgroup;
* the Frattini argument transfers control of a Sylow normalizer;
* control of two conjugate factors controls their join.

These are general group-theoretic statements. The block analysis and the
QTKE hypotheses needed to supply their inputs belong to the source development.
-/

namespace Subgroup

/-- The commutator argument of C.5.5: a nontrivial candidate normalized by M
and contained in R cannot lie in Q when [Q,K] lies in that candidate. -/
public theorem not_le_of_no_common_normal_subgroup {G : Type*} [Group G] (M H K R Q U V : Subgroup G)
    (hH : H ≤ K ⊔ M) (hR : R ≤ M ⊔ H)
    (hno : ∀ N : Subgroup G, N ≤ R → (N.subgroupOf (M ⊔ H)).Normal → N = ⊥)
    (hUV : U ≤ V) (hU : U ≠ ⊥) (hVR : V ≤ R)
    (hMV : M ≤ normalizer (V : Set G)) (hcomm : ⁅Q, K⁆ ≤ U) : ¬ V ≤ Q := by
  intro hVQ
  have hKV : K ≤ normalizer (V : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono hVQ le_rfl).trans (hcomm.trans hUV))
  have hnorm : (V.subgroupOf (M ⊔ H)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (hVR.trans hR)).mpr
      (sup_le hMV (hH.trans (sup_le hKV hMV)))
  exact hU (eq_bot_iff.mpr (by simpa [hno V hVR hnorm] using hUV))

/-- Frattini reduction: if C is normal in N and centralizes U, then control
of the normalizer in N of a Sylow subgroup of C implies that N normalizes U. -/
public theorem le_normalizer_of_sylow_normalizer_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (C N U : Subgroup G) (hCN : C ≤ N) (hNC : N ≤ normalizer (C : Set G))
    (hCU : C ≤ centralizer (U : Set G)) (P : Sylow p C)
    (hPU : N ⊓ normalizer ((P : Subgroup C).map C.subtype : Set G) ≤
      normalizer (U : Set G)) : N ≤ normalizer (U : Set G) := by
  let C' := C.subgroupOf N
  let _ : C'.Normal := (normal_subgroupOf_iff_le_normalizer hCN).mpr hNC
  let e : C ≃* C' := (subgroupOfEquivOfLe hCN).symm
  let P' : Sylow p C' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmap : ((P' : Subgroup C').map C'.subtype).map N.subtype =
      (P : Subgroup C).map C.subtype := by
    change (((P : Subgroup C).map e.toMonoidHom).map C'.subtype).map N.subtype = _
    rw [map_map, map_map]
    rfl
  have hfr := congrArg (fun A : Subgroup N => A.map N.subtype)
    P'.normalizer_sup_eq_top
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, N.range_subtype, subgroupOf_map_subtype,
    inf_of_le_left hCN] at hfr
  rw [← hfr]
  refine sup_le (?_ : _) (hCU.trans (centralizer_le_normalizer _))
  apply le_trans ?_ hPU
  refine le_inf ?_ ?_
  · exact map_le_iff_le_comap.mpr (by intro x _; exact x.property)
  · have hn := ((P' : Subgroup C').map C'.subtype).le_normalizer_map N.subtype
    rwa [hmap] at hn

/-- If N normalizes U and is invariant under t, it also normalizes the
t-conjugate of U. Thus N and any subgroup preserving their join preserve
that join; every resulting conjugate of U centralizes U when the join does. -/
public theorem conjugate_le_centralizer_of_normalizes_pair {G : Type*} [Group G] (N T U : Subgroup G) (t x : G)
    (ht : t ∈ normalizer (N : Set G)) (hNU : N ≤ normalizer (U : Set G))
    (hTU : T ≤ normalizer ((U ⊔ U.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hcomm : U ⊔ U.map (MulAut.conj t).toMonoidHom ≤ centralizer (U : Set G))
    (hx : x ∈ N ⊔ T) : U.map (MulAut.conj x).toMonoidHom ≤ centralizer (U : Set G) := by
  have hNUt : N ≤ normalizer (U.map (MulAut.conj t).toMonoidHom : Set G) := by
    rw [← map_equiv_normalizer_eq U (MulAut.conj t)]
    have hn := Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) hNU
    have heq : N.map (MulAut.conj t).toMonoidHom = N :=
      mem_normalizer_iff_map_conj_eq.mp ht
    rwa [heq] at hn
  have hNjoin := (le_inf hNU hNUt).trans
    (normalizer_inf_normalizer_le_normalizer_sup U (U.map (MulAut.conj t).toMonoidHom))
  have hnx := (sup_le hNjoin hTU) hx
  have hmap := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom)
    (show U ≤ U ⊔ U.map (MulAut.conj t).toMonoidHom from le_sup_left)
  have heq : (U ⊔ U.map (MulAut.conj t).toMonoidHom).map
      (MulAut.conj x).toMonoidHom = U ⊔ U.map (MulAut.conj t).toMonoidHom :=
    mem_normalizer_iff_map_conj_eq.mp hnx
  rw [heq] at hmap
  exact hmap.trans hcomm

end Subgroup
