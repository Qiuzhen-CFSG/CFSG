module
public import Theory.Representation.BinaryPermutation.SixCoreNormalizer
public import Theory.Representation.BinaryPermutation.SixCorePoint
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six
public import CFSG.Quasithin.ChapterB.Section02.Baumann.ActionQuotient
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Augmentation-core point radicals and strong offenders

For either nonconstant weight, the point radical in any permutation group
containing A₆ lies in an even conjugate of the exceptional elementary
subgroup from B.3.4. Its subgroups cannot be strong offenders on the
five-dimensional core. The genuine conjugation action identifies both the
literal centralizer kernel and fixed codimensions, so the statement applies
to every elementary subgroup of the faithful image, including those with
non-elementary lifts. B.2.4.3 then gives full two-rank and places the original
module in the point radical's elementary Thompson subgroup.

Source: Aschbacher–Smith B.2.4(3), B.3.4 and 13.2.2(6), printed
pp.75–76,84–85,877. This supplies a preliminary to the augmentation
Baumann alternative; it does not assert the C.1.37 block conclusion.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.Offenders.SixCorePoint
open BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
abbrev S := Equiv.Perm (Fin 6)
abbrev W := core (Fin 6)
abbrev rho := coreRepresentation (Fin 6)

private theorem pointCore_le_exceptional : pointCore ≤ exceptional 6 (by decide) := by
  rw [pointCore_eq_closure]
  apply (closure_le _).mpr
  rintro x (rfl | rfl | rfl)
  · exact Six.last_le_exceptional (subset_closure rfl)
  · exact Six.plus_le_exceptional (subset_closure (Or.inl rfl))
  · exact Six.klein_le_exceptional (subset_closure (Or.inr rfl))

/-- The point radical has no strong offenders on the augmentation core,
for either weight orbit and either permutation group containing A6. -/
theorem model_no_strong (Y : Subgroup S) (hY : alternatingGroup (Fin 6) ≤ Y)
    (w : W) (hw : ¬ ∀ a : alternatingGroup (Fin 6), alternatingCoreRepresentation (Fin 6) a w = w)
    {B : Subgroup S} (hB : B ≤ (BinaryPermutation.SixCorePoint.stabilizer w ⊓ Y).pCoreIn 2) :
    ¬ IsStrongOffender rho B := by
  obtain ⟨a,ha⟩ := BinaryPermutation.SixCorePoint.exists_point_core_bound Y hY w hw
  have hB' : B.map (MulAut.conj a.val⁻¹).toMonoidHom ≤ pointCore := by
    rintro _ ⟨b,hb,rfl⟩
    obtain ⟨c,hc,he⟩ := ha (hB hb)
    change a.val⁻¹ * b * (a.val⁻¹)⁻¹ ∈ pointCore
    rw [←he]
    change c ∈ pointCore at hc
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,mul_assoc,
      inv_mul_cancel_left,inv_mul_cancel,mul_one] using hc
  intro hstrong
  have hs : IsStrongOffender rho (B.map (MulAut.conj a.val⁻¹).toMonoidHom) :=
    ⟨hstrong.1.map_conj _,by rw [fixedCodim_map_conj,rank_map_conj];exact hstrong.2⟩
  exact Six.exceptional_not_conjugate_D (hB'.trans pointCore_le_exceptional)
    ((Six.isStrongOffender_core_iff _).mp hs)

variable {H : Type*} [Group H] (V : Subgroup H) [V.Normal]
  (q : H →* S) (e : V ≃* Multiplicative W)
  (he : ∀ g v, (e (MulAut.conjNormal g v)).toAdd = rho (q g) (e v).toAdd)

include he

theorem kernel_centralizer : q.ker = centralizer (V : Set H) := by
  ext x
  change q x = 1 ↔ x ∈ centralizer (V : Set H)
  constructor
  · intro hx v hv
    have hh := he x ⟨v,hv⟩
    rw [hx,map_one,Module.End.one_apply] at hh
    have hc := congrArg Subtype.val (e.injective (Multiplicative.toAdd.injective hh))
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  · intro hx
    apply BinaryPermutation.SixCoreNormalizer.action_injective
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := e.surjective (Multiplicative.ofAdd w)
    have hv : MulAut.conjNormal x v = v := by
      apply Subtype.ext
      change x*v.val*x⁻¹ = v.val
      rw [←hx v.val v.property,mul_inv_cancel_right]
    change rho (q x) (e v).toAdd = rho 1 (e v).toAdd
    rw [←he,hv,map_one,Module.End.one_apply]

theorem point_image (z : V) :
    (centralizer ({z.val} : Set H)).map q =
      BinaryPermutation.SixCorePoint.stabilizer (e z).toAdd ⊓ q.range := by
  have hi (x : H) : q x ∈ BinaryPermutation.SixCorePoint.stabilizer (e z).toAdd ↔
      x ∈ centralizer ({z.val} : Set H) := by
    change rho (q x) (e z).toAdd = (e z).toAdd ↔ _
    rw [←he,Multiplicative.toAdd.injective.eq_iff,e.injective.eq_iff,Subtype.ext_iff]
    change x*z.val*x⁻¹ = z.val ↔ _
    rw [mul_inv_eq_iff_eq_mul,mem_centralizer_singleton_iff,eq_comm]
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨(hi x).mpr hx,⟨x,rfl⟩⟩
  · rintro a ⟨ha,x,rfl⟩
    exact ⟨x,(hi x).mp ha,rfl⟩

variable [Finite H]

theorem pointRadical_image (hk : q.ker = pCore 2 H) (z : V) :
    ((centralizer ({z.val} : Set H)).pCoreIn 2).map q =
      (BinaryPermutation.SixCorePoint.stabilizer (e z).toAdd ⊓ q.range).pCoreIn 2 := by
  rw [map_pCoreIn_of_ker_isPGroup q (hk.symm ▸ pCore_isPGroup),point_image V q e he z]

private def linearCoordinates [IsElementaryAbelian 2 V] : Additive V ≃ₗ[ZMod 2] W := by
  let a : Additive V ≃+ W := {
    toFun := fun v => (e v.toMul).toAdd
    invFun := fun w => Additive.ofMul (e.symm (Multiplicative.ofAdd w))
    left_inv := fun v => e.symm_apply_apply v
    right_inv := fun w => e.apply_symm_apply (Multiplicative.ofAdd w)
    map_add' := fun v w => e.map_mul v.toMul w.toMul }
  exact { a with map_smul' := ZMod.map_smul a }

private theorem fixedCodim_eq_model [IsElementaryAbelian 2 V] (A : Subgroup H) :
    BaumannArgument.fixedCodim V A = fixedCodim rho (A.map q) := by
  let q0 := q.rangeRestrict
  have hq0 := q.rangeRestrict_surjective
  have hk0 : q0.ker = centralizer (V : Set H) := by
    change q.rangeRestrict.ker = _
    rw [MonoidHom.ker_rangeRestrict]
    exact kernel_centralizer V q e he
  let r := Representation.NormalElementaryQuotient.representation V q0 hq0 hk0
  have heq (a : q.range) (v : Additive V) :
      linearCoordinates V e (r a v) = rho a.val (linearCoordinates V e v) := by
    obtain ⟨a,rfl⟩ := hq0 a
    have h := Representation.NormalElementaryQuotient.representation_apply V q0 hq0 hk0 a v
    have hh : (r (q0 a) v).toMul = MulAut.conjNormal a v.toMul := Subtype.ext h
    change (e _).toAdd = rho (q a) (e v.toMul).toAdd
    rw [hh]
    exact he a v.toMul
  rw [BaumannArgument.fixedCodim_eq_centralizer_quotient V q0 hq0 hk0]
  have hh := fixedCodim_map_equivariant r rho q.range.subtype (linearCoordinates V e) heq (A.map q0)
  rw [map_map] at hh
  exact hh

/-- The literal B.2.4.3 hypothesis on the actual point-centralizer two-core.
All subgroups of its faithful image are tested, including non-elementary lifts. -/
theorem pointRadical_noStrongOffenders [IsElementaryAbelian 2 V]
    (hk : q.ker = pCore 2 H) (hY : alternatingGroup (Fin 6) ≤ q.range)
    (z : V)
    (hz : ¬ ∀ a : alternatingGroup (Fin 6), alternatingCoreRepresentation (Fin 6) a (e z).toAdd = (e z).toAdd) :
    BaumannArgument.NoStrongOffenders V ((centralizer ({z.val} : Set H)).pCoreIn 2) := by
  intro A hA heA hne
  have hker := kernel_centralizer V q e he
  let k := QuotientGroup.lift (centralizer (V : Set H)) q hker.symm.le
  have hmap : (A.map (BaumannArgument.actionMap V)).map k = A.map q := by
    rw [map_map]
    rfl
  have hAq : IsElementaryAbelian 2 (A.map q) := hmap ▸ heA.map k
  have hneq : A.map q ≠ ⊥ := by
    intro hh
    apply hne
    apply (map_eq_bot_iff A).mpr
    rw [BaumannArgument.actionMap_ker,←hker]
    exact (map_eq_bot_iff A).mp hh
  have hc : Nat.card (A.map (BaumannArgument.actionMap V)) = Nat.card (A.map q) := by
    rw [←relIndex_ker,←relIndex_ker,BaumannArgument.actionMap_ker,hker]
  rw [hc,fixedCodim_eq_model V q e he A]
  apply Nat.le_of_not_gt
  intro hlt
  apply model_no_strong q.range hY (e z).toAdd hz
    ((map_mono hA).trans_eq (pointRadical_image V q e he hk z))
  exact ⟨⟨hneq,hAq⟩,hlt⟩

/-- B.2.4.3 gives full two-rank and places the original five-space in the
Thompson subgroup of the actual point radical. -/
theorem pointRadical_rank_and_module [IsElementaryAbelian 2 V]
    (hk : q.ker = pCore 2 H) (hY : alternatingGroup (Fin 6) ≤ q.range)
    (z : V)
    (hz : ¬ ∀ a : alternatingGroup (Fin 6), alternatingCoreRepresentation (Fin 6) a (e z).toAdd = (e z).toAdd) :
    let R := (centralizer ({z.val} : Set H)).pCoreIn 2
    twoRank (pCore 2 H) = twoRank R ∧ V ≤ Stellmacher.elementaryAbelianMaxJ R := by
  let R := (centralizer ({z.val} : Set H)).pCoreIn 2
  have hker := kernel_centralizer V q e he
  have hQV : pCore 2 H = centralizer (V : Set H) := hk.symm.trans hker
  have hQR : pCore 2 H ≤ R := le_pCoreIn_of_normalizes pCore_isPGroup
    (hQV.le.trans (centralizer_le (Set.singleton_subset_iff.mpr z.property))) le_normalizer_of_normal
  have hVQ : V ≤ pCore 2 H := le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 V⟩
  have hn := pointRadical_noStrongOffenders V q e he hk hY z hz
  have hh := BaumannArgument.centralizer_rank_and_alpha V R (hVQ.trans hQR) hn
  have hi : R ⊓ centralizer (V : Set H) = pCore 2 H := by
    rw [←hQV,inf_eq_right.mpr hQR]
  rw [hi] at hh
  refine ⟨hh.1,?_⟩
  have hVJ : V ≤ Stellmacher.elementaryAbelianMaxJ (pCore 2 H) := by
    intro v hv
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp (hh.2.2.1 hv)).1
  exact hVJ.trans (sSup_le fun A hA => le_sSup (hh.2.1 hA))
end CFSG.Quasithin.ChapterB.Offenders.SixCorePoint
