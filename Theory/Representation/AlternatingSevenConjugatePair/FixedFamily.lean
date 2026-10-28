module

public import Theory.Representation.AlternatingSevenConjugatePair.FixedFamily.Linear
public import Theory.Representation.AlternatingSevenConjugatePair.FixedFamily.Coordinates

/-!
# The unique Sylow four-group with fixed codimension four

The regular four-group on four letters commutes with a three-cycle on the
remaining letters. Its fixed spaces in both faithful summands therefore have
dimension at least two, and the involution bounds make both dimensions two.
The other four-group cannot have the same codimension: their common involution
would identify their fixed spaces, forcing two noncommuting generators to
commute in the faithful representation. Sylow conjugacy transports the unique
witness to every Sylow subgroup of S₇.

Only the single-involution codimension calculation remains an explicit premise.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.8,
printed p.389/PDF p.400.
-/

@[expose] public section

open Representation.BinaryOffender
open scoped Pointwise
namespace Representation.AlternatingSevenConjugatePair.FixedFamily
open ElementaryGeometry
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem regularFour_dimensions (D : Pair V)
    (hinv : ∀ t : S7, orderOf t = 2 →
      fixedCodim D.representation (Subgroup.zpowers t) = 4) :
    Module.finrank (ZMod 2) (D.firstFixedSpace regularFour) = 2 ∧
    Module.finrank (ZMod 2) (D.secondFixedSpace regularFour) = 2 := by
  let B := regularFour.subgroupOf (alternatingGroup (Fin 7))
  let _ : IsElementaryAbelian 2 regularFour := regularFour_elementary.2
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf
    (show regularFour ≤ alternatingGroup (Fin 7) from inf_le_right)
  let c : alternatingGroup (Fin 7) := ⟨cubic, cubic_even⟩
  have hc : c ^ 3 = 1 := Subtype.ext cubic_cube
  have hc1 : c ≠ 1 := fun h => cubic_ne_one (congrArg Subtype.val h)
  have hcomm : ∀ b ∈ B, b * c = c * b := by
    intro b hb
    exact Subtype.ext (regularFour_commutes_cubic b hb)
  have hU := cubic_centralizer_fixed_dimension D.first.toRepresentation D.first_faithful
    B (IsElementaryAbelian.isPGroup 2 B) c hc hc1 hcomm
  have hW := cubic_centralizer_fixed_dimension D.second.toRepresentation D.second_faithful
    B (IsElementaryAbelian.isPGroup 2 B) c hc hc1 hcomm
  have heU := (summandFixedEquiv D.representation D.first regularFour inf_le_right).finrank_eq
  have heW := (summandFixedEquiv D.representation D.second regularFour inf_le_right).finrank_eq
  change Module.finrank (ZMod 2) (fixedSpace D.first.toRepresentation B) =
    Module.finrank (ZMod 2) (D.firstFixedSpace regularFour) at heU
  change Module.finrank (ZMod 2) (fixedSpace D.second.toRepresentation B) =
    Module.finrank (ZMod 2) (D.secondFixedSpace regularFour) at heW
  have hle := summand_fixed_dimensions_le_two D hinv regularFour regularFour_elementary inf_le_right
  omega

theorem regularFour_codim (D : Pair V)
    (hinv : ∀ t : S7, orderOf t = 2 →
      fixedCodim D.representation (Subgroup.zpowers t) = 4) :
    fixedCodim D.representation regularFour = 4 :=
  (codim_four_iff_summand_dimensions D hinv regularFour regularFour_elementary inf_le_right).mpr
    (regularFour_dimensions D hinv)

theorem fixedSpace_eq_involution (D : Pair V)
    (hinv : ∀ t : S7, orderOf t = 2 →
      fixedCodim D.representation (Subgroup.zpowers t) = 4)
    (A : Subgroup S7) (hc : fixedCodim D.representation A = 4)
    (t : S7) (htA : t ∈ A) (ht : orderOf t = 2) :
    fixedSpace D.representation A = fixedSpace D.representation (Subgroup.zpowers t) := by
  apply Submodule.eq_of_le_of_finrank_eq
    (fixedSpace_antitone D.representation (Subgroup.zpowers_le.mpr htA))
  have hA := fixedCodim_add_finrank D.representation A
  have ht' := fixedCodim_add_finrank D.representation (Subgroup.zpowers t)
  rw [hc] at hA
  rw [hinv t ht] at ht'
  omega

theorem pairFour_codim_ne_four (D : Pair V)
    (hinv : ∀ t : S7, orderOf t = 2 →
      fixedCodim D.representation (Subgroup.zpowers t) = 4) :
    fixedCodim D.representation pairFour ≠ 4 := by
  intro hp
  have hr := regularFour_codim D hinv
  have hpz := fixedSpace_eq_involution D hinv pairFour hp centralInvolution
    centralInvolution_mem.1 centralInvolution_order
  have hrz := fixedSpace_eq_involution D hinv regularFour hr centralInvolution
    centralInvolution_mem.2 centralInvolution_order
  have hpp := fixedSpace_eq_involution D hinv pairFour hp pairInvolution
    pairInvolution_mem pairInvolution_order
  have hrr := fixedSpace_eq_involution D hinv regularFour hr crossSwap
    crossSwap_mem_regularFour crossSwap_order
  exact pair_cross_noncommute (commute_of_same_involution_fixedSpace D.representation
    D.faithful pairInvolution crossSwap
    (by simpa [pairInvolution_order] using pow_orderOf_eq_one pairInvolution)
    (by simpa [crossSwap_order] using pow_orderOf_eq_one crossSwap)
    (hpp.symm.trans (hpz.trans (hrz.symm.trans hrr))))

theorem standard_codim_four_unique (D : Pair V)
    (hinv : ∀ t : S7, orderOf t = 2 →
      fixedCodim D.representation (Subgroup.zpowers t) = 4)
    (A : Subgroup S7) (hA : IsElementaryTwo A) (hAT : A ≤ sylowTwo)
    (hAL : A ≤ alternatingGroup (Fin 7)) (hr : rank A = 2)
    (hc : fixedCodim D.representation A = 4) : A = regularFour := by
  rcases four_group_coverage A hA hAT hAL hr with rfl | h
  · exact (pairFour_codim_ne_four D hinv hc).elim
  · exact h

private theorem conjugate_cancel (A : Subgroup S7) (g : S7) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id A using 1
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem exists_unique_codim_four (D : Pair V)
    (hinv : ∀ t : S7, orderOf t = 2 →
      fixedCodim D.representation (Subgroup.zpowers t) = 4) (T : Sylow 2 S7) :
    ∃ A : Subgroup S7, A ≤ (T : Subgroup S7) ∧ A ≤ alternatingGroup (Fin 7) ∧
      IsElementaryTwo A ∧ rank A = 2 ∧ fixedCodim D.representation A = 4 ∧
      ∀ B : Subgroup S7, B ≤ (T : Subgroup S7) → B ≤ alternatingGroup (Fin 7) →
        IsElementaryTwo B → rank B = 2 → fixedCodim D.representation B = 4 → B = A := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S7 T standardSylow
  have hT : (T : Subgroup S7).map (MulAut.conj g).toMonoidHom = sylowTwo :=
    congrArg Sylow.toSubgroup hg
  have hTinv : sylowTwo.map (MulAut.conj g⁻¹).toMonoidHom = (T : Subgroup S7) := by
    rw [← hT, conjugate_cancel]
  let A := regularFour.map (MulAut.conj g⁻¹).toMonoidHom
  have hAT : A ≤ (T : Subgroup S7) := by
    rw [← hTinv]
    exact Subgroup.map_mono (inf_le_left.trans fourTwoElementary_le_sylowTwo)
  have hAL : A ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨a, ha, rfl⟩
    exact (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem a ha.2 g⁻¹
  refine ⟨A, hAT, hAL, regularFour_elementary.map_conj g⁻¹,
    (rank_map_conj regularFour g⁻¹).trans regularFour_rank,
    (fixedCodim_map_conj D.representation regularFour g⁻¹).trans
      (regularFour_codim D hinv), ?_⟩
  intro B hBT hBL hB hr hc
  have hB'T : B.map (MulAut.conj g).toMonoidHom ≤ sylowTwo := hT ▸ Subgroup.map_mono hBT
  have hB'L : B.map (MulAut.conj g).toMonoidHom ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨b, hb, rfl⟩
    exact (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem b (hBL hb) g
  have he := standard_codim_four_unique D hinv (B.map (MulAut.conj g).toMonoidHom)
    (hB.map_conj g) hB'T hB'L ((rank_map_conj B g).trans hr)
    ((fixedCodim_map_conj D.representation B g).trans hc)
  have := congrArg (fun H : Subgroup S7 => H.map (MulAut.conj g⁻¹).toMonoidHom) he
  rwa [conjugate_cancel] at this

end Representation.AlternatingSevenConjugatePair.FixedFamily
