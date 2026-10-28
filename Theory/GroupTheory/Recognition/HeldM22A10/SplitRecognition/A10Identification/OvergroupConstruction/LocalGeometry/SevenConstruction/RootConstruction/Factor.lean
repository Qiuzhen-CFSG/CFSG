module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootActions
public import Theory.GroupTheory.OrderThreeNormalizer
public import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The intrinsic alternating factor in Held's root centralizer

`RootFactor` specifies the actual splitting and A7 identification in Held 5.4.
It is an explicit intermediate input; this module does not assert its existence.
A perfect subgroup with a normalized cyclic supplement is the derived subgroup.
Consequently this factor is unique, contains the given A6, and is normalized by
mu-prime. Its symmetric extension also has derived subgroup W, so any actual S7
identification identifies W with the alternating subgroup exactly.

These reductions separate the ambient recognition and splitting in 5.3–5.4
from the symmetric identification in 5.5 and the transpositions in 5.10.
All centralizers and normalizers in the statements are in the ambient group.

Source: D. Held, *A Characterization of some multiply transitive permutation
groups, I*, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, pp.236–238, Lemmas 5.4–5.5.
-/

open Subgroup Equiv

private theorem derived_cyclic_sup {G : Type*} [Group G] (W : Subgroup G)
    [Group.IsPerfect W] (t : G) (ht : t ∈ normalizer (W : Set G)) :
    ⁅W ⊔ zpowers t, W ⊔ zpowers t⁆ = W := by
  let X := W ⊔ zpowers t
  have hW : W ≤ X := le_sup_left
  have htW : zpowers t ≤ normalizer (W : Set G) := zpowers_le.mpr ht
  let : (W.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hW).mpr (sup_le W.le_normalizer htW)
  have htop : W.subgroupOf X ⊔ (zpowers t).subgroupOf X = ⊤ :=
    (codisjoint_subgroupOf_sup W (zpowers t)).eq_top
  have hcomm : IsMulCommutative ((zpowers t).subgroupOf X) := inferInstance
  have hder : commutator X ≤ W.subgroupOf X :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top htop hcomm
  apply le_antisymm
  · simpa only [map_subtype_commutator, map_subgroupOf_eq_of_le hW] using
      map_mono (f := X.subtype) hder
  · exact W.commutator_eq_self.symm.le.trans (commutator_mono hW hW)

namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e)

/-- The actual internal A7 factor of the full root centralizer, before proving
its compatibility with A6 and mu-prime. Its construction is Held's 5.4. -/
public structure RootFactor where
  W : Subgroup G
  alternatingEquiv : W ≃* alternatingGroup (Fin 7)
  centralizer_root : centralizer ({L.u * L.v} : Set G) = zpowers (L.u * L.v) ⊔ W
  root_disjoint : Disjoint (zpowers (L.u * L.v)) W

variable (F : RootFactor D e L)

/-- The factor centralizes the root in the ambient group. -/
public theorem RootFactor.W_le_centralizer : F.W ≤ centralizer ({L.u * L.v} : Set G) := by
  rw [F.centralizer_root]
  exact le_sup_right

/-- Perfectness transported from the actual alternating group. -/
public theorem RootFactor.isPerfect : Group.IsPerfect F.W := by
  let : Group.IsPerfect (alternatingGroup (Fin 7)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.ofSurjective (f := F.alternatingEquiv.symm.toMonoidHom)
    F.alternatingEquiv.symm.surjective

/-- The alternating factor is the derived subgroup of the full root centralizer. -/
public theorem RootFactor.eq_commutator :
    F.W = ⁅centralizer ({L.u * L.v} : Set G), centralizer ({L.u * L.v} : Set G)⁆ := by
  let : Group.IsPerfect F.W := F.isPerfect D e L
  have hn : L.u * L.v ∈ normalizer (F.W : Set G) := by
    apply centralizer_le_normalizer (F.W : Set G)
    intro w hw
    exact mem_centralizer_singleton_iff.mp (F.W_le_centralizer D e L hw)
  rw [F.centralizer_root, sup_comm]
  exact (derived_cyclic_sup F.W (L.u * L.v) hn).symm

/-- The given perfect A6 lies in the derived subgroup, hence in the factor. -/
public theorem RootFactor.A_le : L.A ≤ F.W := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect L.A :=
    Group.IsPerfect.ofSurjective (f := L.alternatingEquiv.symm.toMonoidHom)
      L.alternatingEquiv.symm.surjective
  have hA : L.A ≤ centralizer ({L.u * L.v} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (L.root_centralizes a ha).symm.eq
  rw [F.eq_commutator D e L]
  exact L.A.commutator_eq_self.symm.le.trans (commutator_mono hA hA)

/-- The factor subgroup is intrinsic, independent of the chosen splitting witness. -/
public theorem RootFactor.unique_W (F' : RootFactor D e L) : F.W = F'.W := by
  rw [F.eq_commutator D e L, F'.eq_commutator D e L]

/-- Inversion of the root preserves its centralizer and therefore its derived subgroup. -/
public theorem RootFactor.mu'_normalizes : mu' D e ∈ normalizer (F.W : Set G) := by
  let f := MulAut.conj (mu' D e)
  have hroot : f (L.u * L.v) = (L.u * L.v)⁻¹ := by
    simpa only [f, MulAut.conj_apply, coordinate_inv D e 2 (by decide)] using
      mu'_root D e L
  have hC : (centralizer ({L.u * L.v} : Set G)).map f.toMonoidHom =
      centralizer ({L.u * L.v} : Set G) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hc : Commute (L.u * L.v)⁻¹ (f x) := by
        rw [← hroot]
        exact (show Commute (L.u * L.v) x from
          (mem_centralizer_singleton_iff.mp hx).symm).map f.toMonoidHom
      apply mem_centralizer_singleton_iff.mpr
      change f x * (L.u * L.v) = (L.u * L.v) * f x
      exact (Commute.inv_left_iff.mp hc).symm.eq
    · intro y hy
      refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
      apply mem_centralizer_singleton_iff.mpr
      apply f.injective
      simp only [map_mul, f.apply_symm_apply, hroot]
      exact (show Commute y (L.u * L.v) from
        mem_centralizer_singleton_iff.mp hy).inv_right.eq
  rw [mem_normalizer_iff_map_conj_eq, F.eq_commutator D e L, map_commutator]
  change ⁅(centralizer ({L.u * L.v} : Set G)).map f.toMonoidHom,
      (centralizer ({L.u * L.v} : Set G)).map f.toMonoidHom⁆ = _
  rw [hC]

/-- Adjoining the normalizing element mu-prime preserves the derived subgroup W. -/
public theorem RootFactor.extension_commutator :
    ⁅F.W ⊔ zpowers (mu' D e), F.W ⊔ zpowers (mu' D e)⁆ = F.W := by
  let : Group.IsPerfect F.W := F.isPerfect D e L
  exact derived_cyclic_sup F.W (mu' D e) (F.mu'_normalizes D e L)

/-- Every S7 equivalence identifies W exactly with its alternating subgroup. -/
public theorem RootFactor.even_subgroup
    (s : (F.W ⊔ zpowers (mu' D e) : Subgroup G) ≃* Perm (Fin 7)) :
    (alternatingGroup (Fin 7)).comap s.toMonoidHom =
      F.W.subgroupOf (F.W ⊔ zpowers (mu' D e)) := by
  have hmap : (commutator (F.W ⊔ zpowers (mu' D e) : Subgroup G)).map
      s.toMonoidHom = alternatingGroup (Fin 7) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr s.surjective,
      ← _root_.commutator_def, alternatingGroup.commutator_perm_eq (by simp)]
  rw [← hmap, comap_map_eq_self_of_injective s.injective]
  apply map_subtype_inj.mp
  rw [map_subtype_commutator, map_subgroupOf_eq_of_le le_sup_left]
  exact F.extension_commutator D e L

/-- The inverter is outside W, since the nonidentity root has order three. -/
public theorem RootFactor.mu'_not_mem : mu' D e ∉ F.W := by
  intro hm
  have hc := mem_centralizer_singleton_iff.mp (F.W_le_centralizer D e L hm)
  have hfix : mu' D e * (L.u * L.v) * mu' D e = L.u * L.v := by
    rw [hc, mul_assoc, ← pow_two, element_square D e 2 (by decide), mul_one]
  have hrinv : L.u * L.v = (L.u * L.v)⁻¹ := hfix.symm.trans (mu'_root D e L)
  have hr2 : (L.u * L.v) ^ 2 = 1 := by
    rw [pow_two]
    exact eq_inv_iff_mul_eq_one.mp hrinv
  have hr1 : L.u * L.v = 1 := by
    simpa only [pow_succ, hr2, one_mul] using root_cube D e L
  exact root_ne_one D e L hr1

/-- All four marked elements actually lie in the symmetric extension. -/
public theorem RootFactor.marked_mem :
    ({mu' D e, L.v * mu' D e, pi D e * mu D e * mu' D e, xi D e} : Set G) ⊆
      (F.W ⊔ zpowers (mu' D e) : Subgroup G) := by
  have hm : mu' D e ∈ (F.W ⊔ zpowers (mu' D e) : Subgroup G) :=
    (show zpowers (mu' D e) ≤ F.W ⊔ zpowers (mu' D e) from le_sup_right) (mem_zpowers _)
  have hA : L.A ≤ F.W ⊔ zpowers (mu' D e) := (F.A_le D e L).trans le_sup_left
  intro x hx
  change x ∈ (F.W ⊔ zpowers (mu' D e) : Subgroup G)
  rcases hx with rfl | rfl | rfl | rfl
  · exact hm
  · exact mul_mem (hA L.v_mem) hm
  · exact mul_mem (hA L.pi_mu_mem) hm
  · simpa only [inv_mul_cancel_left] using mul_mem (inv_mem hm) (hA L.mu'_xi_mem)

/-- The full ambient normalizer, conditional only on the actual root factor.
This is the first equality in Held 5.5. -/
public theorem RootFactor.normalizer_root :
    normalizer (zpowers (L.u * L.v) : Set G) =
      (zpowers (L.u * L.v) ⊔ F.W) ⊔ zpowers (mu' D e) := by
  have hinv : (mu' D e)⁻¹ * (L.u * L.v) * mu' D e = (L.u * L.v)⁻¹ := by
    rw [coordinate_inv D e 2 (by decide)]
    exact mu'_root D e L
  rw [normalizer_zpowers_order_three (L.u * L.v) (mu' D e) (root_order D e L) hinv,
    F.centralizer_root, sup_comm (zpowers (mu' D e))]

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction
