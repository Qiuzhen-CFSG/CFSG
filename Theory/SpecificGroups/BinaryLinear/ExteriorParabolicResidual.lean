module
public import Theory.GroupTheory.PCoreProduct
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.GroupTheory.PResidual.PrimeToCoreMap
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# The cubic residual in the binary 2+3 Levi factor

The actual diagonal-block factor SL₂(2) × SL₃(2) has prime-to-three
residual C₃ × SL₃(2), with C₃ realized as the alternating subgroup on
three letters. Its cubic core has order three. The SL₂ projective-line
comparison and the checked simplicity of SL₃(2) prove these assertions;
the latter comparison retains the attribution and license of its ATLAS port.

Source: Aschbacher--Smith 15.2.23(d), printed p.1117.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace BinaryLinear.ExteriorParabolic

private theorem permThree_cubicCore_card : Nat.card (pCore 3 (Equiv.Perm (Fin 3))) = 3 := by
  have ha : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card,card_alternatingGroup]
    decide
  have hp : IsPGroup 3 (alternatingGroup (Fin 3)) := IsPGroup.of_card (n := 1) ha
  have hle : alternatingGroup (Fin 3) ≤ pCore 3 (Equiv.Perm (Fin 3)) :=
    le_sSup ⟨inferInstance,hp⟩
  have hlo : 3 ≤ Nat.card (pCore 3 (Equiv.Perm (Fin 3))) := by
    exact ha.ge.trans (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hle))
  have hd : Nat.card (pCore 3 (Equiv.Perm (Fin 3))) ∣ 6 := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin,Nat.factorial_succ,Nat.factorial_zero] using
      (pCore 3 (Equiv.Perm (Fin 3))).card_subgroup_dvd_card
  have hc : Nat.Coprime (Nat.card (pCore 3 (Equiv.Perm (Fin 3)))) 2 := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := Equiv.Perm (Fin 3))).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_left n
  have hd3 : Nat.card (pCore 3 (Equiv.Perm (Fin 3))) ∣ 3 :=
    hc.dvd_mul_left.mp hd
  exact le_antisymm (Nat.le_of_dvd (by decide) hd3) hlo

private theorem slThree_cubicCore_bot : pCore 3 SL(3,ZMod 2) = ⊥ := by
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

/-- The cubic core of the actual 2+3 Levi factor has order three. -/
theorem levi_cubicCore_card : Nat.card (pCore 3 (SL(2,ZMod 2) × SL(3,ZMod 2))) = 3 := by
  let e := Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three
  have htwo : Nat.card (pCore 3 SL(2,ZMod 2)) = 3 := by
    rw [← card_map_of_injective (f := e.toMonoidHom) e.injective, pCore_map_iso 3 e]
    exact permThree_cubicCore_card
  rw [pCore_prod,Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,
    htwo,slThree_cubicCore_bot]
  simp

/-- Taking O^{3′} preserves this cubic core with its intrinsic subgroup map. -/
theorem residual_levi_cubicCore_card :
    Nat.card (pCore 3 (primeToResidual 3 (SL(2,ZMod 2) × SL(3,ZMod 2)))) = 3 := by
  rw [← card_map_of_injective (primeToResidual 3 (SL(2,ZMod 2) × SL(3,ZMod 2))).subtype_injective,
    map_pCore_primeToResidual]
  exact levi_cubicCore_card

private theorem residual_prod {A B : Type*} [Group A] [Group B] [Finite A] [Finite B] :
    primeToResidual 3 (A × B) = (primeToResidual 3 A).prod (primeToResidual 3 B) := by
  apply le_antisymm
  · intro x hx
    exact ⟨map_primeToResidual_le_of_hom 3 (MonoidHom.fst A B)
      (mem_map_of_mem _ hx), map_primeToResidual_le_of_hom 3 (MonoidHom.snd A B)
      (mem_map_of_mem _ hx)⟩
  · rintro ⟨x,y⟩ ⟨hx,hy⟩
    have hl := map_primeToResidual_le_of_hom 3 (MonoidHom.inl A B) (mem_map_of_mem _ hx)
    have hr := map_primeToResidual_le_of_hom 3 (MonoidHom.inr A B) (mem_map_of_mem _ hy)
    simpa using (primeToResidual 3 (A × B)).mul_mem hl hr

private theorem permThree_residual : primeToResidual 3 (Equiv.Perm (Fin 3)) =
    alternatingGroup (Fin 3) := by
  apply le_antisymm
  · apply primeToResidual_le
    rw [alternatingGroup.index_eq_two]
    decide
  · apply le_primeToResidual_of_isPGroup
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_eq_fintype_card,card_alternatingGroup]
    decide

private theorem slThree_residual : primeToResidual 3 SL(3,ZMod 2) = ⊤ := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup SL(3,ZMod 2) := Matrix.PSL3Two.equiv.isSimpleGroup
  rcases (inferInstance : (primeToResidual 3 SL(3,ZMod 2)).Normal).eq_bot_or_eq_top with h | h
  · have hc := primeToResidual_index_coprime (G := SL(3,ZMod 2)) 3
    rw [h,index_bot,Matrix.PSL3Two.card_SL] at hc
    norm_num at hc
  · exact h

/-- The prime-to-three residual of the marked Levi factor is C₃ × SL₃(2).
The cyclic factor is the literal alternating subgroup on three letters. -/
noncomputable def leviResidualEquiv :
    primeToResidual 3 (SL(2,ZMod 2) × SL(3,ZMod 2)) ≃*
      alternatingGroup (Fin 3) × SL(3,ZMod 2) := by
  let e := Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three
  exact (primeToResidualEquiv 3 (e.prodCongr (MulEquiv.refl SL(3,ZMod 2)))).trans
    ((MulEquiv.subgroupCongr (by rw [residual_prod,permThree_residual,slThree_residual])).trans
      ((prodEquiv _ _).trans ((MulEquiv.refl _).prodCongr topEquiv)))

end BinaryLinear.ExteriorParabolic
