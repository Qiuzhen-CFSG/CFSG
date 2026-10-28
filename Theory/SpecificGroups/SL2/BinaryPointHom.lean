module
public import Theory.SpecificGroups.SL2.OddCoreAndRank
public import Theory.SpecificGroups.PSL2.BinaryCoreSections
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.SpecificGroups.PSL3.LinearThreeLocalStructure

/-!
# Binary point-local groups have no odd SL₂ image

For a finite field F of characteristic two with |F|>2, every homomorphism
from SL₂(F) to an odd-characteristic SL₂(E) is trivial: simplicity would
otherwise give an injection, contradicting the two-rank bound of SL₂(E).
Every elementary two-subgroup of SL₂(E) is scalar central. Thus the
commutator identity for the symplectic point radical kills that radical,
and the remaining binary SL₂ quotient has trivial image. In the linear
point-local affine model the translation image is central and the binary
SL₂ factor has trivial image; perfectness kills the full image.

These model calculations support the odd-extension exclusion in
Aschbacher–Smith 11.4.4, refs/quasithin.pdf, printed p.778. They concern
the concrete point-local groups, without any splitting assumption on an
ambient group covering those models.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups commutatorElement
namespace Theory.SpecificGroups.BinaryPointHom
variable {F E : Type*} [Field F] [Finite F] [CharP F 2] [Field E] [Finite E]

omit [Finite E] in
private theorem square_one_central (hE : (2 : E) ≠ 0) (x : SL(2,E))
    (hx : x ^ 2 = 1) : x ∈ center SL(2,E) := by
  have hd : (SpecialLinearGroup.toGL x).det = 1 := by
    apply Units.ext
    exact x.property
  rcases GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one hE
      (SpecialLinearGroup.toGL x) (by rw [←map_pow,hx,map_one]) hd with he | he
  · have h : x = 1 := SpecialLinearGroup.toGL_injective (by simpa using he)
    exact h ▸ one_mem _
  · have h : x = -1 := Subtype.ext (congrArg Units.val he)
    rw [h]
    exact mem_center_iff.mpr (fun y => by simp)

private theorem binary_hom_trivial {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (hE : (2 : E) ≠ 0) (a : SL(2,F) →* SL(2,E)) (x : SL(2,F)) : a x = 1 := by
  have hlarge : 3 < Nat.card F := by
    rw [hF]
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    norm_num at hh
    omega
  let : IsSimpleGroup PSL(2,F) := ProjectiveSpecialLinearGroup.rank_two_simple hlarge
  let : IsSimpleGroup SL(2,F) := (Theory.PSL2.sl2QuotientEquiv F).isSimpleGroup
  rcases (inferInstance : a.ker.Normal).eq_bot_or_eq_top with hk | hk
  · have hi := a.ker_eq_bot_iff.mp hk
    have hr := Theory.GroupTheory.primeRank_le_of_injective 2 a hi
    have hl := Theory.PSL2.root_two_rank_ge F hF
    rw [←primeRank_equiv 2 (Theory.PSL2.sl2QuotientEquiv F)] at hl
    rw [SpecialLinearGroup.primeRank_two_eq_one hE] at hr
    omega
  · exact (show x ∈ a.ker from hk.symm ▸ mem_top x)

omit [Finite E] in
private theorem elementary_image_central {A : Type*} [Group A]
    (P : Subgroup A) [IsElementaryAbelian 2 P]
    (hE : (2 : E) ≠ 0) (a : A →* SL(2,E)) : P.map a ≤ center SL(2,E) := by
  rintro _ ⟨x,hx,rfl⟩
  apply square_one_central hE
  rw [←map_pow]
  have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 P) (⟨x,hx⟩ : P)
  rw [show x^2=1 from congrArg Subtype.val hh,map_one]

/-- The characteristic-two symplectic point-local group has no nontrivial odd SL₂ image. -/
theorem symplectic_point_hom_trivial {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (hE : (2 : E) ≠ 0)
    (a : Theory.SpecificGroups.SymplecticFour.pointLocal (F := F) →* SL(2,E))
    (x : Theory.SpecificGroups.SymplecticFour.pointLocal (F := F)) : a x = 1 := by
  have hc := elementary_image_central
    (Theory.SpecificGroups.SymplecticFour.pointRadical (F := F)) hE a
  have hk : pCore 2 (Theory.SpecificGroups.SymplecticFour.pointLocal (F := F)) ≤ a.ker := by
    rw [Theory.SpecificGroups.SymplecticFour.pointLocal_core_eq hF hn,
      ←Theory.SpecificGroups.SymplecticFour.pointRadical_commutator_eq hF hn]
    apply (Subgroup.map_eq_bot_iff _).mp
    rw [map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (hc.trans (center_le_centralizer _))
  let b := QuotientGroup.lift _ a hk
  let e := Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hF hn
  have hh := binary_hom_trivial hF hn hE (b.comp e.symm.toMonoidHom)
    (e (QuotientGroup.mk' _ x))
  have hb : b (QuotientGroup.mk' _ x) = 1 := by
    simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply] using hh
  exact hb

/-- The characteristic-two linear point-local group has no nontrivial odd SL₂ image. -/
theorem linear_point_hom_trivial {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (hE : (2 : E) ≠ 0) (a : PSL3.LinearThree.pointLocalSL F →* SL(2,E))
    (x : PSL3.LinearThree.pointLocalSL F) : a x = 1 := by
  let e := PSL3.LinearThree.pointLocalAffineEquiv F
  let b := a.comp e.symm.toMonoidHom
  have hc := elementary_image_central (SL2.translations F) hE b
  have hb : b.range ≤ center SL(2,E) := by
    rintro _ ⟨y,rfl⟩
    rw [←SemidirectProduct.inl_left_mul_inr_right y,map_mul]
    have hi := binary_hom_trivial hF hn hE (b.comp SemidirectProduct.inr) y.right
    change b (SemidirectProduct.inr y.right) = 1 at hi
    rw [hi,mul_one]
    exact hc (mem_map_of_mem _ (by rw [←SL2.range_inl_eq_translations]; exact ⟨y.left,rfl⟩))
  let : Group.IsPerfect (PSL3.LinearThree.pointLocalSL F) :=
    PSL3.LinearThree.pointLocalSL_isPerfect F (by
      rw [hF]; exact Nat.pow_le_pow_right (by decide : 0 < 2) hn)
  let : Group.IsPerfect (SL2.Affine F) := SL2.affine_isPerfect F (by
    rw [hF]; exact Nat.pow_le_pow_right (by decide : 0 < 2) hn)
  let : Group.IsPerfect b.range := Group.IsPerfect.range b
  let : IsMulCommutative b.range := ⟨⟨fun y z => Subtype.ext
    ((mem_center_iff.mp (hb y.property) z).symm)⟩⟩
  have he : b (e x) = 1 := congrArg Subtype.val (Subsingleton.elim (b.rangeRestrict (e x)) 1)
  simpa only [b,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply] using he
end Theory.SpecificGroups.BinaryPointHom
