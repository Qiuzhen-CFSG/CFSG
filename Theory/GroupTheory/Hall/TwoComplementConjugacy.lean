module
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction

/-!
# Conjugating two odd complements by the normal two-subgroup

Two odd solvable complements of the same finite normal two-subgroup are
conjugate by an element of that two-subgroup. Hall conjugacy first supplies
an element of their common product; its odd factor can be removed because
it normalizes the prescribed complement. Only the local factors need be
finite, so the ambient completion may be infinite.

Source application: the full Cartan transporters at the start of DGS (10.8),
Groups and Graphs (1985), printed p.160, in Assembly.BTwoPathCartan.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Subgroup.OddHall
variable {X : Type*} [Group X]
/-- Conjugate the second complement onto the first by the original two-subgroup. -/
theorem exists_two_conjugator_of_common_sup
    (Q K C : Subgroup X) [Finite Q] [Finite K] [Finite C]
    [Group.IsSolvable K]
    (hQ : IsPGroup 2 Q) (hK : Nat.Coprime 2 (Nat.card K))
    (hC : Nat.Coprime 2 (Nat.card C))
    (hNK : K ≤ normalizer (Q : Set X)) (hNC : C ≤ normalizer (Q : Set X))
    (he : Q ⊔ C = Q ⊔ K) :
    ∃ q ∈ Q, C.map (MulAut.conj q).toMonoidHom = K := by
  let E := Q ⊔ K
  have hfinite : (E : Set X).Finite := by
    rw [show (E : Set X) = (Q : Set X) * (K : Set X) from
      coe_mul_of_right_le_normalizer_left Q K hNK]
    exact (Set.toFinite (Q : Set X)).mul (Set.toFinite (K : Set X))
  let _ : Finite E := hfinite.to_subtype
  let _ := hQ.isNilpotent
  have hsolv : Group.IsSolvable E := Group.isSolvable_sup_of_normalizes Q K hNK
  have hKE : K ≤ E := le_sup_right
  have hCE : C ≤ E := le_sup_right.trans he.le
  obtain ⟨b,hb⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable hsolv
    (oddHall_of_normalized_sup hQ hK hNK rfl)
    (oddHall_of_normalized_sup hQ hC hNC he)
  have hm : C = K.map (MulAut.conj (b : X)).toMonoidHom := by
    have hh := congrArg (Subgroup.map E.subtype) hb
    rw [map_subgroupOf_eq_of_le hCE, map_map] at hh
    have hf : E.subtype.comp (MulAut.conj b).toMonoidHom =
        (MulAut.conj (b : X)).toMonoidHom.comp E.subtype := rfl
    simpa only [hf, ← map_map, map_subgroupOf_eq_of_le hKE] using hh
  have hp : (b : X) ∈ (Q : Set X) * (K : Set X) := by
    rw [←coe_mul_of_right_le_normalizer_left Q K hNK]
    exact b.property
  obtain ⟨q,hq,k,hk,hqk⟩ := hp
  have hn : K.map (MulAut.conj k).toMonoidHom = K :=
    mem_normalizer_iff_map_conj_eq.mp (K.le_normalizer hk)
  refine ⟨q⁻¹,Q.inv_mem hq,?_⟩
  rw [hm,map_map]
  have hf : (MulAut.conj q⁻¹).toMonoidHom.comp (MulAut.conj (b : X)).toMonoidHom =
      (MulAut.conj k).toMonoidHom := by
    ext z
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, MulAut.conj_apply, ←hqk]
    group
  rw [hf,hn]
end Subgroup.OddHall
