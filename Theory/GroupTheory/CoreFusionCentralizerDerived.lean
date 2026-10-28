module

public import Theory.GroupTheory.SylowCentralizerConjugacy
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic

/-!
# Weak closure in a core excludes a derived central involution

Let `H` contain the derived subgroup of a Sylow subgroup `S`, and suppose a
central element `z` has no distinct ambient conjugate in `H`. If a distinct
`t` in `S` is conjugate to `z`, then `z` is absent from the derived subgroup
of `C_S(t)`.

Conjugate `t` to `z`, then conjugate the transported Sylow centralizer into
`S` inside `C_G(z)`. A hypothetical derived `z` maps into `H`, where weak
closure identifies its image with `z`. Injectivity then identifies `t` with
`z`, a contradiction. Neither saturation nor a rank bound is needed.

Source: Janko–Thompson (1970), §4, printed pp.389–390.
-/

open Subgroup
open scoped Pointwise
namespace Sylow
/-- Core-local weak closure excludes the central element from the derived
subgroup of a distinct fused element's Sylow centralizer. -/
public theorem central_involution_not_mem_centralizer_derived_of_core_fusion
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (H : Subgroup S) (hderived : _root_.commutator S ≤ H)
    (z t : S) (hzc : z ∈ center S) (hne : t ≠ z)
    (hconj : IsConj (z : G) (t : G))
    (hinside : ∀ u : S, u ∈ H → IsConj (z : G) (u : G) → u = z) :
    z ∉ ⁅centralizer ({t} : Set S), centralizer ({t} : Set S)⁆ := by
  let E := centralizer ({t} : Set S)
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj.symm
  let f : G ≃* G := MulAut.conj g
  have hft : f (t : G) = z := hg
  let C := centralizer ({(z : G)} : Set G)
  have hSC : (S : Subgroup G) ≤ C := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hzc ⟨s, hs⟩))
  let U := (E.map (S : Subgroup G).subtype).map f.toMonoidHom
  have hUC : U ≤ C := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [← hft]
    change f (a : G) * f (t : G) = f (t : G) * f (a : G)
    simpa only [Subgroup.coe_mul, map_mul] using congrArg f
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))
  have hpU : IsPGroup 2 U := ((S.isPGroup'.to_subgroup E).map _).map _
  obtain ⟨T, hT⟩ := (hpU.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq C T (S.subtype hSC)
  let a : G := (k : G) * g
  let q : G ≃* G := MulAut.conj a
  have hqv (v : G) : q v = (k : G) * f v * (k : G)⁻¹ := by
    simp [q, a, f, mul_assoc]
  have hqt : q (t : G) = z := by
    rw [hqv, hft]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp k.property)
  have hqE (v : E) : q ((v : S) : G) ∈ (S : Subgroup G) := by
    have hvU : f ((v : S) : G) ∈ U :=
      mem_map_of_mem f.toMonoidHom (mem_map_of_mem (S : Subgroup G).subtype v.property)
    let u : C := ⟨f ((v : S) : G), hUC hvU⟩
    have huT : u ∈ T := hT hvU
    have huS : (MulAut.conj k) u ∈ S.subtype hSC := by
      rw [← hk]
      exact Set.smul_mem_smul_set huT
    change (k : G) * f ((v : S) : G) * (k : G)⁻¹ ∈ (S : Subgroup G) at huS
    rw [hqv]
    exact huS
  let r : E →* S :=
    { toFun := fun v => ⟨q ((v : S) : G), hqE v⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' := fun x y => Subtype.ext (map_mul q _ _) }
  intro hzD
  have hzE : z ∈ E := center_le_centralizer _ hzc
  let zE : E := ⟨z, hzE⟩
  have hzED : zE ∈ _root_.commutator E := by
    have hm : z ∈ (_root_.commutator E).map E.subtype := by
      rwa [map_subtype_commutator]
    obtain ⟨w, hw, he⟩ := hm
    exact (show w = zE from Subtype.ext he) ▸ hw
  have hrzD : r zE ∈ _root_.commutator S := by
    have hm := mem_map_of_mem r hzED
    rw [_root_.commutator_def, map_commutator] at hm
    exact (commutator_mono le_top le_top) hm
  have hrzz : r zE = z := hinside _ (hderived hrzD) (isConj_iff.mpr ⟨a, rfl⟩)
  apply hne
  apply (S : Subgroup G).subtype_injective
  apply q.injective
  exact hqt.trans (congrArg Subtype.val hrzz).symm
end Sylow
