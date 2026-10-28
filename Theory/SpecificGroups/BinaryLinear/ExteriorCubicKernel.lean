module
public import Theory.SpecificGroups.BinaryLinear.ExteriorParabolicResidual
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankSquareFree

/-!
# Rank-one intersections in the binary exterior Levi

The cubic core of C₃ × SL₃(2) is exactly the first direct factor. For a
finite group A with this two-core quotient, any subgroup K of three-rank
at least two meets the literal O₂,₃(A) preimage in three-rank one. Project
to SL₃(2), whose order has only one factor of three, and use the kernel
rank inequality. The two-group kernel preserves the rank in the cubic
factor.

Source application: Aschbacher--Smith 15.2.23(d), printed p.1117.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace BinaryLinear.ExteriorParabolic

private theorem cubic_card : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

private theorem slThree_core_bot : pCore 3 SL(3,ZMod 2) = ⊥ := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup SL(3,ZMod 2) := Matrix.PSL3Two.equiv.isSimpleGroup
  rcases (inferInstance : (pCore 3 SL(3,ZMod 2)).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hp := pCore_isPGroup (p := 3) (G := SL(3,ZMod 2))
    rw [h] at hp
    have hp' : IsPGroup 3 SL(3,ZMod 2) := hp.of_equiv topEquiv
    obtain ⟨n,hn⟩ := hp'.exists_card_eq
    have hc : Nat.Coprime (Nat.card SL(3,ZMod 2)) 2 := by
      rw [hn]
      exact (by decide : Nat.Coprime 3 2).pow_left n
    rw [Matrix.PSL3Two.card_SL] at hc
    norm_num at hc

/-- The cubic core of the residual Levi is exactly the first direct factor. -/
theorem residualModel_cubicCore :
    pCore 3 (alternatingGroup (Fin 3) × SL(3,ZMod 2)) =
      (MonoidHom.snd (alternatingGroup (Fin 3)) SL(3,ZMod 2)).ker := by
  have ht : pCore 3 (alternatingGroup (Fin 3)) = ⊤ := by
    apply top_unique
    apply le_sSup
    refine ⟨inferInstance, ?_⟩
    exact (IsPGroup.of_card (p := 3) (n := 1) cubic_card).of_equiv topEquiv.symm
  rw [pCore_prod, ht, slThree_core_bot]
  ext x
  simp

variable {A : Type*} [Group A] [Finite A]

/-- Every subgroup of three-rank at least two meets the characteristic
O₂,₃ preimage in a subgroup of three-rank exactly one. -/
theorem cubicPreimage_intersection_rank
    (e : (A ⧸ pCore 2 A) ≃* (alternatingGroup (Fin 3) × SL(3,ZMod 2)))
    (K : Subgroup A) (hK : 2 ≤ primeRank 3 K) :
    primeRank 3 (K ⊓ (pCore 3 (A ⧸ pCore 2 A)).comap
      (QuotientGroup.mk' (pCore 2 A)) : Subgroup A) = 1 := by
  let q := QuotientGroup.mk' (pCore 2 A)
  let a := e.toMonoidHom.comp (q.comp K.subtype)
  let f := (MonoidHom.snd _ _).comp a
  let g : f.ker →* alternatingGroup (Fin 3) := (MonoidHom.fst _ _).comp (a.comp f.ker.subtype)
  have hg : IsPGroup 2 g.ker := by
    let j : g.ker →* pCore 2 A :=
      (K.subtype.comp (f.ker.subtype.comp g.ker.subtype)).codRestrict _ (by
        intro x
        apply (QuotientGroup.eq_one_iff _).mp
        apply e.map_eq_one_iff.mp
        exact Prod.ext x.property x.val.property)
    apply pCore_isPGroup.of_injective j
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : pCore 2 A => (z : A)) h
  have hu : primeRank 3 f.ker ≤ 1 := by
    have he : primeRank 3 ((⊤ : Subgroup f.ker).map g) = primeRank 3 f.ker := by
      rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 3) g hg,
        primeRank_equiv 3 topEquiv]
    rw [← he]
    exact (primeRank_subgroup_le 3 _).trans (primeRank_le_one_of_square_not_dvd (by
      rw [cubic_card]
      decide))
  have hv : primeRank 3 SL(3,ZMod 2) ≤ 1 := primeRank_le_one_of_square_not_dvd (by
    rw [Matrix.PSL3Two.card_SL]
    decide)
  have hl := primeRank_le_ker_add (p := 3) f
  have hr : primeRank 3 f.ker = 1 := by omega
  have heq : (pCore 3 (A ⧸ pCore 2 A)).comap q =
      ((MonoidHom.snd _ _).comp (e.toMonoidHom.comp q)).ker := by
    ext x
    change q x ∈ pCore 3 (A ⧸ pCore 2 A) ↔ (e (q x)).2 = 1
    have hh := mem_map_iff_mem (f := e.toMonoidHom) (K := pCore 3 (A ⧸ pCore 2 A))
      e.injective (x := q x)
    rw [pCore_map_iso 3 e, residualModel_cubicCore] at hh
    exact hh.symm
  rw [heq]
  let ei : f.ker ≃* (K ⊓ ((MonoidHom.snd _ _).comp (e.toMonoidHom.comp q)).ker : Subgroup A) :=
    { toFun := fun x => ⟨x.val.val,x.val.property,x.property⟩
      invFun := fun x => ⟨⟨x.val,x.property.1⟩,x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  rwa [← primeRank_equiv 3 ei]

end BinaryLinear.ExteriorParabolic
