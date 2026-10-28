module
public import Theory.Mathieu.M11.Properties.InvolutionCentralizer
public import Theory.Mathieu.M11.Properties.Sylow3
public import Theory.SpecificGroups.GL2.ThreeSolvable

/-!
# A solvable generating pair through each Sylow two-subgroup of M₁₁

Conjugate the native involution centralizer of order 48 and the Sylow
three-normalizer of order 144 to contain the same prescribed Sylow
two-subgroup. Both orders have the full two-part of |M₁₁|. The involution
centralizer is maximal; the order-144 group cannot lie in it, so their join
is M₁₁. The first group is the proved GL₂(3) carrier. The second has its
literal normal Sylow three-subgroup of order nine with two-group quotient
of order sixteen. These structures prove solvability of both members.

This supplies the local-family input for Aschbacher–Smith E.1.14(4),
printed p.214, citing Asc82a Lemma 4.9. The intrinsic centralizer and
normalizer calculations are those of GLS3 Table 5.3a, as implemented in
the imported native Witt-design modules. No maximal-subgroup table or
unchecked computational certificate is assumed here.
-/

public section
open Subgroup
namespace Sporadic.Mathieu.M11RankOne

private theorem exists_sylow_le (H : Subgroup M11)
    (hc : (Nat.card H).factorization 2 = 4) :
    ∃ S : Sylow 2 M11, (S : Subgroup M11) ≤ H := by
  classical
  let P : Sylow 2 H := Classical.choice inferInstance
  let J := (P : Subgroup H).map H.subtype
  have hJ : Nat.card J = 2 ^ 4 := by
    rw [← Nat.card_congr ((P : Subgroup H).equivMapOfInjective H.subtype
      H.subtype_injective).toEquiv, P.card_eq_multiplicity, hc]
  let S : Sylow 2 M11 := Sylow.ofCard J (by rw [hJ, m11_order]; decide +kernel)
  exact ⟨S, map_subtype_le _⟩

private theorem exists_conjugate_containing (T : Sylow 2 M11) (H : Subgroup M11)
    (hc : (Nat.card H).factorization 2 = 4) :
    ∃ g : M11, (T : Subgroup M11) ≤ H.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨S, hS⟩ := exists_sylow_le H hc
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M11 S T
  refine ⟨g, ?_⟩
  rw [← hg]
  exact map_mono hS

private theorem normalizer_solvable :
    Group.IsSolvable (normalizer (m11Sylow3Subgroup : Set M11)) := by
  let N := normalizer (m11Sylow3Subgroup : Set M11)
  let Q := m11Sylow3Subgroup.subgroupOf N
  have hc : Nat.card Q = 9 :=
    (Nat.card_congr (subgroupOfEquivOfLe m11Sylow3Subgroup.le_normalizer).toEquiv).trans
      m11Sylow3Subgroup_card
  let : Q.Normal := Subgroup.normal_in_normalizer
  have hq : Nat.card (N ⧸ Q) = 16 := by
    have h := Q.card_mul_index
    rw [hc, m11Sylow3_normalizer_card] at h
    change 9 * Nat.card (N ⧸ Q) = 144 at h
    omega
  let : Group.IsNilpotent Q := (IsPGroup.of_card (p := 3) (n := 2) hc).isNilpotent
  let : Group.IsNilpotent (N ⧸ Q) := (IsPGroup.of_card (p := 2) (n := 4) hq).isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient Q).mpr ⟨inferInstance, inferInstance⟩

/-- Every Sylow subgroup lies in a generating pair of solvable subgroups. -/
theorem exists_solvable_pair (T : Sylow 2 M11) :
    ∃ H J : Subgroup M11, (T : Subgroup M11) ≤ H ∧ (T : Subgroup M11) ≤ J ∧
      H ⊔ J = ⊤ ∧ Group.IsSolvable H ∧ Group.IsSolvable J := by
  let C := m11InvolutionCentralizer
  let N := normalizer (m11Sylow3Subgroup : Set M11)
  obtain ⟨g, hg⟩ := exists_conjugate_containing T C (by
    rw [m11_involutionCentralizer_card]; decide +kernel)
  obtain ⟨h, hh⟩ := exists_conjugate_containing T N (by
    rw [m11Sylow3_normalizer_card]; decide +kernel)
  let H := C.map (MulAut.conj g).toMonoidHom
  let J := N.map (MulAut.conj h).toMonoidHom
  have hH : IsCoatom H := by
    exact (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup C).mpr
      m11_involutionCentralizer_isCoatom
  have hj : ¬ J ≤ H := by
    intro hj
    have hd := card_dvd_of_le hj
    have hcJ : Nat.card J = 144 :=
      (Nat.card_congr ((MulAut.conj h).subgroupMap N).symm.toEquiv).trans
        m11Sylow3_normalizer_card
    have hcH : Nat.card H = 48 :=
      (Nat.card_congr ((MulAut.conj g).subgroupMap C).symm.toEquiv).trans
        m11_involutionCentralizer_card
    rw [hcJ, hcH] at hd
    norm_num at hd
  have hlt : H < H ⊔ J := lt_of_le_of_ne le_sup_left
    (fun he => hj (le_sup_right.trans he.symm.le))
  have hgen : H ⊔ J = ⊤ := hH.2 _ hlt
  let : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :=
    Matrix.GeneralLinearGroup.three_isSolvable
  let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective
    (f := m11InvolutionCentralizer_mulEquiv_gl2.toMonoidHom)
    m11InvolutionCentralizer_mulEquiv_gl2.injective
  let : Group.IsSolvable N := normalizer_solvable
  exact ⟨H, J, hg, hh, hgen,
    Group.isSolvable_of_surjective (f := ((MulAut.conj g).subgroupMap C).toMonoidHom)
      ((MulAut.conj g).subgroupMap C).surjective,
    Group.isSolvable_of_surjective (f := ((MulAut.conj h).subgroupMap N).toMonoidHom)
      ((MulAut.conj h).subgroupMap N).surjective⟩
end Sporadic.Mathieu.M11RankOne
