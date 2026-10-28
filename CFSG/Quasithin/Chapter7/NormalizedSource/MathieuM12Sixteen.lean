module
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.ElementaryFixed
-- Intentional internal certificate continuation: reuse the checked native
-- Sylow matrices and coverage, the inner displacement calculation, and the
-- actual ambient-extension constructor without widening their public APIs.
import all CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.ElementaryFixed
import all CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.NoFF
import all CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient
import all CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.Assembly

/-!
# Terminal fixed spaces for the full M12 automorphism heart

An elementary sixteen conjugates into the verified degree-24 Sylow group.
Its outer involution has precisely sixteen possible commuting Sylow elements;
equal cardinality makes the elementary group contain every one of them.
In particular it contains the displayed inner/outer pair. Seven independent
displacement rows bound their common fixed space by three dimensions.
Their individual fixed dimensions are six and five, so their fixed spaces
span at least eight dimensions. Both bounds transport through the actual
ambient marking and feed NonFFSourceMathieuM12Excluded.

This is a small kernel-checked continuation of the native ElementaryFixed
certificate. MathieuM12Sixteen/source/generate.py reproduces its matrices.
No outer centralizer-table row is assumed.
Source: Aschbacher--Smith H.11.1(4), pp.392--393, and7.5.4, p.700.
The degree-24 ATLAS attribution is retained in Extension.Seeds.
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped Matrix IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuM12Sixteen
open ChapterH.Section10To12 ChapterH.Section10To12.M12Calculations Sporadic.Mathieu
open M12ExceptionalExtension OverlapExtensions Ambient.ElementaryFixed
private def pairIndex : Fin 2 → Fin 128 := ![2,4]
private def pairActor (k : Fin 2) : Carrier := (Overlap.element (pairIndex k)).val
private def displacementRows : Fin 2 → Fin 10 → BitVec 10 := ![![612,491,387,984,698,878,182,444,563,603],![1023,989,1023,999,999,989,703,1023,703,1023]]
private def displacement (k : Fin 2) : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  fun i j => if (displacementRows k i).getLsb j then 1 else 0
private def wordEnd : List (Fin 3) → Module.End (ZMod 2) Coordinates
  | [] => 1
  | j::w => (matrix j).mulVecLin * wordEnd w
private theorem wordEnd_apply (w : List (Fin 3)) (v : Coordinates) :
    wordEnd w v = wordAction w v := by
  induction w with
  | nil => rfl
  | cons j w ih => change (matrix j).mulVecLin (wordEnd w v) = _; rw [ih]; rfl
set_option maxRecDepth 4096 in
private theorem displacement_certificate (k : Fin 2) :
    displacement k = LinearMap.toMatrix' (wordEnd (Data.overlapWords (pairIndex k)) - 1) := by
  fin_cases k <;> decide +kernel
private def select : Fin 7 → Fin 20 := ![0,1,2,3,4,10,11]
private def free : Fin 3 → Fin 10 := ![0,1,3]
private def inverseRows : Fin 10 → BitVec 10 := ![128,256,200,512,549,352,870,666,798,719]
private def test : Matrix (Fin 10) (Fin 10) (ZMod 2) := fun i j =>
  if hi : i.val < 7 then
    let n := select ⟨i.val,hi⟩
    displacement ⟨n.val/10,by omega⟩ ⟨n.val%10,by omega⟩ j
  else if j = free ⟨i.val-7,by omega⟩ then 1 else 0
private def inverse : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  fun i j => if (inverseRows i).getLsb j then 1 else 0
set_option maxRecDepth 4096 in
private theorem inverse_certificate : inverse * test = 1 := by decide +kernel

set_option maxRecDepth 4096 in
private theorem test_kernel (v : Coordinates)
    (hf : ∀ k : Fin 2, wordAction (Data.overlapWords (pairIndex k)) v = v)
    (hz : ∀ j : Fin 3, v (free j) = 0) : v = 0 := by
  have hd (k : Fin 2) : displacement k *ᵥ v = 0 := by
    rw [displacement_certificate,LinearMap.toMatrix'_mulVec]
    change wordEnd (Data.overlapWords (pairIndex k)) v - v = 0
    rw [wordEnd_apply,hf,sub_self]
  have ht : test *ᵥ v = 0 := by
    ext i
    by_cases hi : i.val < 7
    · let n := select ⟨i.val,hi⟩
      simpa only [Matrix.mulVec,test,dif_pos hi,n,Pi.zero_apply] using
        congrFun (hd ⟨n.val/10,by omega⟩) ⟨n.val%10,by omega⟩
    · simpa [test,hi,Matrix.mulVec,dotProduct] using hz ⟨i.val-7,by omega⟩
  have hx := congrArg (fun M => M *ᵥ v) inverse_certificate
  rw [←Matrix.mulVec_mulVec,ht,Matrix.mulVec_zero,Matrix.one_mulVec] at hx
  exact hx.symm

private theorem pair_fixed_le_three :
    Module.finrank (ZMod 2)
      (fixedSpace carrierAction (zpowers (pairActor 0)) ⊓
        fixedSpace carrierAction (zpowers (pairActor 1)) : Submodule (ZMod 2) M12Heart) ≤ 3 := by
  let U := fixedSpace carrierAction (zpowers (pairActor 0)) ⊓
    fixedSpace carrierAction (zpowers (pairActor 1))
  let P : U →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    { toFun := fun v j => M12Calculations.heartEquiv.symm v.val (free j)
      map_add' := by intros; ext j; simp only [Submodule.coe_add,map_add,Pi.add_apply]
      map_smul' := by intros; ext j; simp only [SetLike.val_smul,map_smul,Pi.smul_apply]; rfl }
  have hi : Function.Injective P := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    change v = 0
    apply Subtype.ext
    apply M12Calculations.heartEquiv.symm.injective
    change M12Calculations.heartEquiv.symm v.val = M12Calculations.heartEquiv.symm (0 : M12Heart)
    rw [map_zero]
    apply test_kernel
    · intro k
      have hfix : carrierAction (pairActor k) v.val = v.val := by
        fin_cases k
        · exact (mem_fixedSpace_zpowers_iff _ _ _).mp v.property.1
        · exact (mem_fixedSpace_zpowers_iff _ _ _).mp v.property.2
      have he := element_action (pairIndex k) (M12Calculations.heartEquiv.symm v.val)
      rw [M12Calculations.heartEquiv.apply_symm_apply] at he
      change carrierAction (pairActor k) v.val = _ at he
      rw [hfix] at he
      exact (M12Calculations.heartEquiv.injective
        (he.symm.trans (M12Calculations.heartEquiv.apply_symm_apply v.val).symm))
    · intro j; exact congrFun hv j
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using
    LinearMap.finrank_le_finrank_of_injective hi

private theorem pair_mem_of_overlap (A : Subgroup Carrier)
    [IsElementaryAbelian 2 A] (hA : A ≤ overlap) (hc : Nat.card A = 16) :
    ∀ k : Fin 2, pairActor k ∈ A := by
  classical
  obtain ⟨x,hxA,hxo⟩ := SetLike.not_le_iff_exists.mp (not_le_inner A hc)
  obtain ⟨i,hi⟩ := Overlap.element_surjective ⟨x,hA hxA⟩
  have he : (Overlap.element i : Carrier) = x := congrArg Subtype.val hi
  have hp : perm i ^ 2 = 1 := by
    have hh := elemPow_eq_one_of_isElementaryAbelian (p := 2) x hxA
    rw [←he] at hh
    simpa only [Subgroup.coe_pow,Subgroup.coe_one,Overlap.element_val,perm]
      using congrArg Subtype.val hh
  have hm : ∃ j : Fin 12, generatorA (perm i (blockLabel 0)) = blockLabel j := by
    simpa only [←he,Overlap.element_val,perm] using outer_marker x hxo
  obtain ⟨k,rfl⟩ := outer_coverage i hp hm
  have hex (y : A) : ∃ q : Fin 16, (Overlap.element (centralIndices q)).val = y.val := by
    obtain ⟨l,hl⟩ := Overlap.element_surjective ⟨y,hA y.property⟩
    have hey : (Overlap.element l : Carrier) = y := congrArg Subtype.val hl
    have hcomm : perm l * perm (outerIndices k) = perm (outerIndices k) * perm l := by
      have hh : (y : Carrier)*x = x*(y : Carrier) := congrArg Subtype.val
        (mul_comm y (⟨x,hxA⟩ : A))
      rw [←he,←hey] at hh
      simpa only [Subgroup.coe_mul,Overlap.element_val,perm] using congrArg Subtype.val hh
    obtain ⟨q,rfl⟩ := commuting_coverage k l hcomm
    exact ⟨q,hey⟩
  let f : A → Fin 16 := fun y => (hex y).choose
  have hf (y : A) : (Overlap.element (centralIndices (f y))).val = y.val := (hex y).choose_spec
  have hfi : Function.Injective f := by
    intro y z hyz
    apply Subtype.ext
    rw [←hf y,←hf z,hyz]
  have hfs : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hfi,by simpa using hc⟩).2
  have hall (q : Fin 16) : (Overlap.element (centralIndices q)).val ∈ A := by
    obtain ⟨y,hy⟩ := hfs q
    exact (hy ▸ hf y).symm ▸ y.property
  intro k
  fin_cases k
  · exact hall 1
  · exact hall 2

set_option maxRecDepth 4096 in
private theorem pair_order (k : Fin 2) : orderOf (pairActor k) = 2 := by
  apply orderOf_eq_prime
  · fin_cases k <;> decide +kernel
  · fin_cases k <;> decide +kernel

private theorem inner_pair_mem : pairActor 1 ∈ M12ExceptionalExtension.inner := by
  have he : pairActor 1 = (Overlap.generator 0).val ^ 2 := by
    apply Subtype.ext
    decide +kernel
  rw [he]
  exact sq_mem_of_index_two inner_index _

set_option maxRecDepth 4096 in
private theorem outer_pair_not_mem : pairActor 0 ∉ M12ExceptionalExtension.inner := by
  intro hi
  have he := blockRestriction_spec ⟨pairActor 0,hi⟩ 0
  have hn : ∀ j : Fin 12, (pairActor 0).val (blockLabel 0) ≠ blockLabel j := by decide +kernel
  exact hn _ he

private theorem auto_inner_iff (x : Carrier) :
    automorphismEquiv x ∈ MulAut.innerSubgroup M12 ↔ x ∈ M12ExceptionalExtension.inner := by
  constructor
  · rintro ⟨g,hg⟩
    have he : innerModel.embedding g = x := by
      apply automorphismEquiv.injective
      rw [automorphismEquiv_embedding]
      exact hg
    exact he ▸ (innerModel.equiv g).property
  · intro hx
    let g := innerModel.equiv.symm ⟨x,hx⟩
    have he : innerModel.embedding g = x := congrArg Subtype.val (innerModel.equiv.apply_symm_apply ⟨x,hx⟩)
    exact ⟨g,by rw [←automorphismEquiv_embedding,he]⟩

private theorem pair_codim (k : Fin 2) :
    fixedCodim carrierAction (zpowers (pairActor k)) = if k = 0 then 5 else 4 := by
  have he := fixedSpace_comp_map Ambient.automorphismRepresentation automorphismEquiv.toMonoidHom
    (zpowers (pairActor k))
  rw [MonoidHom.map_zpowers] at he
  change fixedSpace carrierAction (zpowers (pairActor k)) = _ at he
  change Module.finrank (ZMod 2) (M12Heart ⧸ fixedSpace _ _) = _
  rw [he]
  change fixedCodim Ambient.automorphismRepresentation (zpowers (automorphismEquiv (pairActor k))) = _
  have ho := (automorphismEquiv.orderOf_eq (pairActor k)).trans (pair_order k)
  fin_cases k
  · exact LocalActors.fixedCodim_native_outer outer_involution_fusion
      Ambient.automorphismRepresentation Ambient.automorphismRepresentation_faithful
      (fun hi => outer_pair_not_mem ((auto_inner_iff _).mp hi)) ho
  · exact M12Calculations.inner_displacement _ ((auto_inner_iff _).mpr inner_pair_mem) ho

private theorem dimensions_of_overlap (A : Subgroup Carrier)
    [IsElementaryAbelian 2 A] (hA : A ≤ overlap) (hc : Nat.card A = 16) :
    Module.finrank (ZMod 2) (fixedSpace carrierAction A) ≤ 3 ∧
      8 ≤ Module.finrank (ZMod 2) (fixedSpaceSpan carrierAction A) := by
  have hm := pair_mem_of_overlap A hA hc
  have hp := pair_fixed_le_three
  have hsub : fixedSpace carrierAction A ≤ fixedSpace carrierAction (zpowers (pairActor 0)) ⊓
      fixedSpace carrierAction (zpowers (pairActor 1)) :=
    le_inf (ChapterE.fixedSpace_antitone _ (zpowers_le.mpr (hm 0)))
      (ChapterE.fixedSpace_antitone _ (zpowers_le.mpr (hm 1)))
  refine ⟨(Submodule.finrank_mono hsub).trans hp,?_⟩
  have hdim0 := fixedCodim_add_finrank carrierAction (zpowers (pairActor 0))
  have hdim1 := fixedCodim_add_finrank carrierAction (zpowers (pairActor 1))
  rw [pair_codim,if_pos rfl,finrank_m12Heart] at hdim0
  rw [pair_codim,if_neg (by decide),finrank_m12Heart] at hdim1
  have hsum := (fixedSpace carrierAction (zpowers (pairActor 0))).finrank_sup_add_finrank_inf_eq
    (fixedSpace carrierAction (zpowers (pairActor 1)))
  have hne (k : Fin 2) : pairActor k ≠ 1 := by
    intro he; have hh := pair_order k; simp [he] at hh
  have hle := Submodule.finrank_mono (sup_le
    (fixedSpace_le_fixedSpaceSpan carrierAction (hm 0) (hne 0))
    (fixedSpace_le_fixedSpaceSpan carrierAction (hm 1) (hne 1)))
  omega

private theorem dimensions_carrier (A : Subgroup Carrier)
    [IsElementaryAbelian 2 A] (hc : Nat.card A = 16) :
    Module.finrank (ZMod 2) (fixedSpace carrierAction A) ≤ 3 ∧
      8 ≤ Module.finrank (ZMod 2) (fixedSpaceSpan carrierAction A) := by
  obtain ⟨P,hP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier P VerifiedPair.commonSylow
  let C := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
  have hC : C ≤ overlap := by
    rintro _ ⟨a,ha,rfl⟩
    have hh := (P.equivSMul g ⟨a,hP ha⟩).property
    change MulAut.conj g a ∈ (g • P : Sylow 2 Carrier) at hh
    rw [hg] at hh
    exact hh
  have hcC : Nat.card C = 16 := (card_map_of_injective (MulAut.conj g).injective).trans hc
  obtain ⟨hfixed,hspan⟩ := dimensions_of_overlap C hC hcC
  refine ⟨?_,?_⟩
  · rw [(fixedSpaceConjEquiv carrierAction A g).finrank_eq]
    exact hfixed
  · let E := LinearMap.GeneralLinearGroup.toLinearEquiv (carrierAction.asGroupHom g)
    have he : ∀ a v, E (carrierAction a v) = carrierAction (MulAut.conj g a) (E v) := by
      intro a v
      change carrierAction g (carrierAction a v) = carrierAction (g*a*g⁻¹) (carrierAction g v)
      rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
      simp only [inv_mul_cancel_right]
    have hquot := fixedSpaceSpan_codim_map_equivariant carrierAction carrierAction
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective E he A
    change Module.finrank (ZMod 2) (M12Heart ⧸ fixedSpaceSpan carrierAction A) =
      Module.finrank (ZMod 2) (M12Heart ⧸ fixedSpaceSpan carrierAction C) at hquot
    have hsumA := (fixedSpaceSpan carrierAction A).finrank_quotient_add_finrank
    have hsumC := (fixedSpaceSpan carrierAction C).finrank_quotient_add_finrank
    rw [hquot] at hsumA
    omega

/-- The actual full automorphism heart satisfies both terminal H.11.1(4) bounds. -/
theorem dimensions_native (A : Subgroup (MulAut M12)) [IsElementaryAbelian 2 A]
    (hc : Nat.card A = 16) :
    Module.finrank (ZMod 2) (fixedSpace Ambient.automorphismRepresentation A) ≤ 3 ∧
      8 ≤ Module.finrank (ZMod 2) (fixedSpaceSpan Ambient.automorphismRepresentation A) := by
  let C := A.map automorphismEquiv.symm.toMonoidHom
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
  have hcC : Nat.card C = 16 := (card_map_of_injective automorphismEquiv.symm.injective).trans hc
  have hd := dimensions_carrier C hcC
  have he : ∀ a v, (LinearEquiv.refl (ZMod 2) M12Heart) (Ambient.automorphismRepresentation a v) =
      carrierAction (automorphismEquiv.symm a) v := by
    intro a v
    change Ambient.automorphismRepresentation a v =
      Ambient.automorphismRepresentation (automorphismEquiv (automorphismEquiv.symm a)) v
    rw [automorphismEquiv.apply_symm_apply]
  have hfix := fixedCodim_map_equivariant Ambient.automorphismRepresentation carrierAction
    automorphismEquiv.symm.toMonoidHom (LinearEquiv.refl _ _) he A
  have hquot := fixedSpaceSpan_codim_map_equivariant Ambient.automorphismRepresentation carrierAction
    automorphismEquiv.symm.toMonoidHom automorphismEquiv.symm.injective (LinearEquiv.refl _ _) he A
  have hsumA := (fixedSpaceSpan Ambient.automorphismRepresentation A).finrank_quotient_add_finrank
  have hsumC := (fixedSpaceSpan carrierAction C).finrank_quotient_add_finrank
  have hfA := fixedCodim_add_finrank Ambient.automorphismRepresentation A
  have hfC := fixedCodim_add_finrank carrierAction C
  change fixedCodim Ambient.automorphismRepresentation A = fixedCodim carrierAction C at hfix
  change Module.finrank (ZMod 2) (M12Heart ⧸ fixedSpaceSpan Ambient.automorphismRepresentation A) =
    Module.finrank (ZMod 2) (M12Heart ⧸ fixedSpaceSpan carrierAction C) at hquot
  rw [hquot] at hsumA
  rw [hfix] at hfA
  constructor <;> omega

/-- Markings transport the native terminal fixed-space and fixed-span bounds. -/
theorem dimensions_marked {G W : Type*} [Group G] [Finite G]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (h : M12ModuleInput ρ)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hc : Nat.card A = 16) :
    Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 3 ∧
      8 ≤ Module.finrank (ZMod 2) (fixedSpaceSpan ρ A) := by
  let d := ambientExtension ρ h
  let B := A.map d.embedding
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hcB : Nat.card B = 16 := (card_map_of_injective d.embedding_injective).trans hc
  have hd := dimensions_native B hcB
  rw [d.finrank_fixedSpace_map,d.finrank_fixedSpaceSpan_map]
  exact hd
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuM12Sixteen
