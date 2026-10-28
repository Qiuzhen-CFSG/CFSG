module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.ResidualLocal.ModelFacts.Four

/-!
# The literal residual as the supported alternating four-group

Project the two-block centralizer to its first block. The image lies in a
group of order eight, so the two-residual lies in the kernel. That kernel is
the last-block A₄, whose two-residual is itself. Transport through the actual
block embedding identifies the residual with the pointwise stabilizer of
0, 1, 2, 3, including the precise image of `(45)(67)`.

The marked isomorphism transports cardinality, involution conjugacy and the
Klein four centralizer to the original subgroup of A₈.
Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38.
-/

@[expose] public section
open Equiv Equiv.Perm Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index.ResidualModel
abbrev FirstCentralizer := centralizer ({fourMark} : Set (Perm (Fin 4)))
instance firstCentralizerDecidable : DecidablePred (· ∈ FirstCentralizer) := fun a =>
  decidable_of_iff (a * fourMark = fourMark * a) mem_centralizer_singleton_iff.symm

theorem firstCentralizer_card : Nat.card FirstCentralizer = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

def firstHom : Blocks →* FirstCentralizer where
  toFun a := ⟨a.val.1, mem_centralizer_singleton_iff.mpr a.property.1.eq⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def fourToBlocks : Four →* Blocks where
  toFun a := ⟨(1, a.val), by
    refine ⟨Commute.one_left _, ?_⟩
    simpa only [map_one, one_mul] using mem_alternatingGroup.mp a.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem fourToBlocks_injective : Function.Injective fourToBlocks := by
  intro a b h
  exact Subtype.ext (congrArg (fun x : Blocks => x.val.2) h)

theorem first_ker_eq_range : firstHom.ker = fourToBlocks.range := by
  ext a
  constructor
  · intro ha
    have he : a.val.1 = 1 := congrArg Subtype.val ha
    have hs : a.val.2 ∈ alternatingGroup (Fin 4) := by
      apply mem_alternatingGroup.mpr
      simpa only [he, map_one, one_mul] using a.property.2
    exact ⟨⟨a.val.2, hs⟩, Subtype.ext (Prod.ext he.symm rfl)⟩
  · rintro ⟨a, rfl⟩
    rfl

theorem blocks_residual : pResidual 2 Blocks = firstHom.ker := by
  apply le_antisymm
  · have hp : IsPGroup 2 FirstCentralizer :=
      IsPGroup.of_card (n := 3) (by rw [firstCentralizer_card]; norm_num)
    exact sInf_le ⟨inferInstance,
      (hp.to_subgroup firstHom.range).of_equiv (QuotientGroup.quotientKerEquivRange firstHom).symm⟩
  · rw [first_ker_eq_range]
    have h := map_pResidual_le 2 fourToBlocks
    rwa [four_residual, ← MonoidHom.range_eq_map] at h

def fourToC : Four →* C := blocksToC.comp fourToBlocks

def fourToEight : Four →* Eight := C.subtype.comp fourToC

/-- The literal embedding fixes the first block pointwise. -/
theorem fourToEight_apply_first (a : Four) (j : Fin 4) :
    (fourToEight a : Perm (Fin 8)) (Fin.castAdd 4 j) = Fin.castAdd 4 j := by
  change (finSumFinEquiv.permCongr (Perm.sumCongr 1 a.val)) (Fin.castAdd 4 j) = _
  simp only [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
    Perm.sumCongr_apply, Sum.map_inl, Perm.one_apply, finSumFinEquiv_apply_left]

/-- On the second block the embedding acts by the given four-point permutation. -/
theorem fourToEight_apply_last (a : Four) (j : Fin 4) :
    (fourToEight a : Perm (Fin 8)) (Fin.natAdd 4 j) = Fin.natAdd 4 (a.val j) := by
  change (finSumFinEquiv.permCongr (Perm.sumCongr 1 a.val)) (Fin.natAdd 4 j) = _
  simp only [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_natAdd,
    Perm.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right]

theorem fourToEight_injective : Function.Injective fourToEight :=
  C.subtype_injective.comp (blocksToC_injective.comp fourToBlocks_injective)

/-- The residual is the actual A₄ supported on the last four points. -/
theorem R_eq_range : R = fourToEight.range := by
  rw [R, ← map_pResidual 2 blocksEquiv, blocks_residual, first_ker_eq_range,
    ← MonoidHom.range_comp, ← MonoidHom.range_comp]
  rfl

/-- The residual is exactly the pointwise stabilizer of the first four points. -/
theorem mem_R_iff_fixed_first (a : Eight) :
    a ∈ R ↔ ∀ j : Fin 4, (a : Perm (Fin 8)) (Fin.castAdd 4 j) = Fin.castAdd 4 j := by
  constructor
  · rw [R_eq_range]
    rintro ⟨b, rfl⟩
    exact fourToEight_apply_first b
  · intro hf
    have h0 : (a : Perm (Fin 8)) 0 = 0 := hf 0
    have h1 : (a : Perm (Fin 8)) 1 = 1 := hf 1
    have h2 : (a : Perm (Fin 8)) 2 = 2 := hf 2
    have h3 : (a : Perm (Fin 8)) 3 = 3 := hf 3
    have h01 : Commute (a : Perm (Fin 8)) (swap 0 1) := by
      change _ * _ = _ * _
      rw [mul_swap_eq_swap_mul, h0, h1]
    have h23 : Commute (a : Perm (Fin 8)) (swap 2 3) := by
      change _ * _ = _ * _
      rw [mul_swap_eq_swap_mul, h2, h3]
    have ha : a ∈ C := mem_centralizer_singleton_iff.mpr
      (Subtype.ext (h01.mul_right h23).eq)
    obtain ⟨b, hb⟩ := blocksEquiv.surjective ⟨a, ha⟩
    have he : blockPerm b.val = (a : Perm (Fin 8)) :=
      congrArg (fun x : C => (x.val : Perm (Fin 8))) hb
    have hfirst : b.val.1 = 1 := by
      apply Equiv.ext
      intro j
      have hh := hf j
      rw [← he] at hh
      change (finSumFinEquiv.permCongr (Perm.sumCongr b.val.1 b.val.2))
        (Fin.castAdd 4 j) = _ at hh
      simpa only [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
        Perm.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left, Fin.castAdd_inj, Perm.one_apply] using hh
    have hker : b ∈ firstHom.ker := Subtype.ext hfirst
    have hr : b ∈ pResidual 2 Blocks := blocks_residual.symm ▸ hker
    have hc : blocksEquiv b ∈ pResidual 2 C := by
      rw [← map_pResidual 2 blocksEquiv]
      exact mem_map.mpr ⟨b, hr, rfl⟩
    exact mem_map.mpr ⟨blocksEquiv b, hc, congrArg Subtype.val hb⟩

noncomputable def fourEquiv : Four ≃* R :=
  (MonoidHom.ofInjective fourToEight_injective).trans
    (MulEquiv.subgroupCongr R_eq_range.symm)

theorem fourEquiv_apply (a : Four) : (fourEquiv a : Eight) = fourToEight a := rfl

theorem fourToEight_involution : fourToEight fourInvolution = i8 := by
  apply Subtype.ext
  decide +kernel

theorem i_mem : i8 ∈ R := by
  rw [R_eq_range]
  exact ⟨fourInvolution, fourToEight_involution⟩

theorem fourEquiv_involution : fourEquiv fourInvolution = (⟨i8, i_mem⟩ : R) :=
  Subtype.ext fourToEight_involution

theorem R_card : Nat.card R = 12 :=
  (Nat.card_congr fourEquiv.toEquiv).symm.trans four_card

theorem R_involution_fusion (a : R) (ha : orderOf a = 2) :
    IsConj a (⟨i8, i_mem⟩ : R) := by
  have h := fourEquiv.toMonoidHom.map_isConj
    (four_involution_fusion (fourEquiv.symm a) ((fourEquiv.symm.orderOf_eq a).trans ha))
  simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, fourEquiv_involution] using h

noncomputable def fourCentralizerEquiv : FourCentralizer ≃*
    centralizer ({⟨i8, i_mem⟩} : Set R) where
  toFun a := ⟨fourEquiv a.val, mem_centralizer_singleton_iff.mpr (by
    rw [← fourEquiv_involution, ← map_mul, ← map_mul]
    exact congrArg fourEquiv (mem_centralizer_singleton_iff.mp a.property))⟩
  invFun a := ⟨fourEquiv.symm a.val, mem_centralizer_singleton_iff.mpr (by
    apply fourEquiv.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply, fourEquiv_involution] using
      mem_centralizer_singleton_iff.mp a.property)⟩
  left_inv a := Subtype.ext (fourEquiv.symm_apply_apply a.val)
  right_inv a := Subtype.ext (fourEquiv.apply_symm_apply a.val)
  map_mul' a b := Subtype.ext (map_mul fourEquiv a.val b.val)

theorem R_centralizer_equiv : Nonempty
    (centralizer ({⟨i8, i_mem⟩} : Set R) ≃* DihedralGroup 2) :=
  ⟨fourCentralizerEquiv.symm.trans fourCentralizer_equiv.some⟩
end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index.ResidualModel

end
