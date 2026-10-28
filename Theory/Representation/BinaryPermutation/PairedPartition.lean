module
public import Theory.Representation.BinaryPermutation.PairedResidual
public import Theory.GroupTheory.PResidual.PerfectCover
public import Mathlib.GroupTheory.IndexNormal

/-!
# Two-residual of the even three-pair stabilizer

The paired A₄ has index two in the even stabilizer of the partition into
three pairs and one singleton. Its cubic generators lie in the two-residual,
while the index-two quotient gives the reverse containment. Its centralizer
is therefore the identity together with the triple transposition.

Source: Aschbacher--Smith 15.1.25(5), printed p.1102.
-/

public section
open Subgroup
namespace AlternatingSeven.ThreeResidualLocals

/-- The two-residual of the actual even three-pair stabilizer is the paired A₄. -/
theorem paired_partition_twoResidual :
    (pResidual 2 (alternatingGroup (Fin 7) ⊓ centralizer ({pairing} : Set Perm7) : Subgroup _)).map
      (alternatingGroup (Fin 7) ⊓ centralizer ({pairing} : Set Perm7)).subtype = pairedFour := by
  let P := alternatingGroup (Fin 7) ⊓ normalizer (pairedFour : Set Perm7)
  have hKP : pairedFour ≤ P := le_inf models_le_alternating.2.2 pairedFour.le_normalizer
  have hcard : Nat.card P = 24 := alternating_normalizer_pairedFour_card
  have hindex : (pairedFour.subgroupOf P).index = 2 := by
    have hh := (pairedFour.subgroupOf P).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hKP).toEquiv,pairedFour_card,hcard] at hh
    omega
  let : (pairedFour.subgroupOf P).Normal :=
    (pairedFour.subgroupOf P).normal_of_index_eq_two hindex
  have hquot : IsPGroup 2 (P ⧸ pairedFour.subgroupOf P) :=
    IsPGroup.of_card (n := 1) (by rw [←index_eq_card,hindex]; rfl)
  have hupper : (pResidual 2 P).map P.subtype ≤ pairedFour := by
    rintro x ⟨y,hy,rfl⟩
    exact (show pResidual 2 P ≤ pairedFour.subgroupOf P from sInf_le ⟨inferInstance,hquot⟩) hy
  have hlower : pairedFour ≤ (pResidual 2 P).map P.subtype := by
    apply (pairedFour_le_paired_threeResidual (alternatingGroup (Fin 7)) le_rfl).trans
    apply map_mono
    rw [primePowerGenerated_le_iff]
    intro x n hx
    exact mem_pResidual_of_orderOf_coprime
      (((by decide : Nat.Coprime 2 3).pow_right n).of_dvd_right (orderOf_dvd_of_pow_eq_one hx))
  have he := le_antisymm hupper hlower
  have hPP : P = alternatingGroup (Fin 7) ⊓ centralizer ({pairing} : Set Perm7) :=
    congrArg (fun H : Subgroup Perm7 => alternatingGroup (Fin 7) ⊓ H) pairedFour_normalizer_eq
  exact (congrArg (fun H : Subgroup Perm7 => (pResidual 2 H).map H.subtype) hPP).symm.trans he

/-- The source two-residual has exactly the centralizer used in the block argument. -/
theorem centralizer_paired_partition_residual (g : Perm7) :
    g ∈ centralizer (((pResidual 2
      (alternatingGroup (Fin 7) ⊓ centralizer ({pairing} : Set Perm7) : Subgroup _)).map
        (alternatingGroup (Fin 7) ⊓ centralizer ({pairing} : Set Perm7)).subtype) : Set Perm7) ↔
      g = 1 ∨ g = pairing := by
  rw [paired_partition_twoResidual]
  exact centralizer_pairedFour_iff g


/-- Both the residual and its centralizer transport under the same relabeling. -/
theorem conjugate_partition_twoResidual (P : Subgroup Perm7) (c : Perm7)
    (hP : P = (centralizer ({pairing} : Set Perm7)).map (MulAut.conj c).toMonoidHom) :
    (pResidual 2 (alternatingGroup (Fin 7) ⊓ P : Subgroup Perm7)).map
      (alternatingGroup (Fin 7) ⊓ P).subtype = pairedFour.map (MulAut.conj c).toMonoidHom := by
  have hA : (alternatingGroup (Fin 7)).map (MulAut.conj c).toMonoidHom = alternatingGroup (Fin 7) :=
    Normal.map_conj_eq _ c
  have hi : alternatingGroup (Fin 7) ⊓ P =
      (alternatingGroup (Fin 7) ⊓ centralizer ({pairing} : Set Perm7)).map
        (MulAut.conj c).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj c).injective,hA,hP]
  have he := map_embedded_pResidual 2
    (alternatingGroup (Fin 7) ⊓ centralizer ({pairing} : Set Perm7))
    (MulAut.conj c).toMonoidHom
  rw [paired_partition_twoResidual,←hi] at he
  exact he.symm

theorem centralizer_conjugate_pairedFour (g c : Perm7)
    (hg : g ∈ centralizer (pairedFour.map (MulAut.conj c).toMonoidHom : Set Perm7)) :
    g = 1 ∨ g.cycleType = {2,2,2} := by
  let e := MulAut.conj c
  have hc : e.symm g ∈ centralizer (pairedFour : Set Perm7) := by
    intro x hx
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using hg (e x) (mem_map_of_mem e.toMonoidHom hx)
  rcases (centralizer_pairedFour_iff _).mp hc with h | h
  · left
    apply e.symm.injective
    simpa only [map_one] using h
  · right
    have he : g = e pairing := by rw [←h,e.apply_symm_apply]
    rw [he]
    exact Equiv.Perm.cycleType_conj.trans pairing_cycleType


end AlternatingSeven.ThreeResidualLocals
