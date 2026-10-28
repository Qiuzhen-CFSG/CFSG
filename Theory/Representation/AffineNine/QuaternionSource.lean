module
public import Theory.Representation.AffineNine.QuaternionBound
public import Theory.Representation.AffineNine.SourceComparison
public import Theory.Representation.AffineNine.Transport
public import Theory.GroupTheory.PCorePrimeToIndex
/-!
# The strict ratio for an actual quaternion-by-nine configuration

Let D be a normal elementary nine-group in K, supplemented by a two-group
S. If O₂(K)=1, the normal subgroup C_S(D) is trivial, so D is self-centralizing.
Coordinates on D identify S faithfully with its actual image in GL₂(3), and
the specified quaternion subgroup of that image supplies the affine-nine
weight bound. The original representation is transported through the literal
semidirect-product equivalence; no splitting or equality of the full image
with Q₈ is assumed.

Source: Aschbacher--Smith 13.3.14(d), printed p.892. This establishes the
particular strict-ratio obstruction used there without the full D.2.17
classification or any assumption about offender generation.
-/
public section
open Subgroup Matrix
open scoped MatrixGroups IsMulCommutative
namespace Representation.AffineNine
private def quaternionAutAdd (a : MulAut Translation) : Plane ≃+ Plane where
  toFun v := (a (Multiplicative.ofAdd v)).toAdd
  invFun v := (a.symm (Multiplicative.ofAdd v)).toAdd
  left_inv v := a.left_inv v
  right_inv v := a.right_inv v
  map_add' v w := a.map_mul v w

private def quaternionAutLinear : MulAut Translation ≃* (Plane ≃ₗ[ZMod 3] Plane) where
  toFun a := { quaternionAutAdd a with map_smul' := ZMod.map_smul (quaternionAutAdd a) }
  invFun a := a.toAddEquiv.toMultiplicative
  left_inv a := by ext; rfl
  right_inv a := by ext; rfl
  map_mul' a b := by ext; rfl

private def quaternionNaturalEquiv : LinearGroup ≃* MulAut Translation :=
  GeneralLinearGroup.toLin.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) Plane).trans
      quaternionAutLinear.symm)

private def quaternionLinearized {D : Type*} [Group D] (c : D ≃* Translation) :
    MulAut D ≃* LinearGroup := (MulAut.congr c).trans quaternionNaturalEquiv.symm

private theorem quaternionLinearized_apply {D : Type*} [Group D]
    (c : D ≃* Translation) (a : MulAut D) (v : D) :
    naturalAction (quaternionLinearized c a) (c v) = c (a v) := by
  change quaternionNaturalEquiv (quaternionNaturalEquiv.symm (MulAut.congr c a)) (c v) = _
  rw [quaternionNaturalEquiv.apply_symm_apply]
  change c (a (c.symm (c v))) = _
  rw [c.symm_apply_apply]

private theorem quaternion_coordinates {D : Type*} [Group D] [Finite D]
    [IsElementaryAbelian 3 D] (hD : Nat.card D = 9) : Nonempty (D ≃* Translation) := by
  classical
  have hpow : 3 ^ Module.finrank (ZMod 3) (Additive D) = 3 ^ 2 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive D)
    change Nat.card D = _ at hc
    simpa only [Nat.card_zmod,hD,show (3:ℕ)^2=9 by decide] using hc.symm
  have hd := Nat.pow_right_injective (by decide : 1 < 3) hpow
  exact ⟨(Module.finBasisOfFinrankEq (ZMod 3) (Additive D) hd).equivFun.toAddEquiv.toMultiplicativeRight⟩

variable {K V : Type*} [Group K] [Finite K]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The marked normal nine-group and quaternion conjugation image force the
strict bound on the original representation. The full complement may be larger. -/
theorem cubicRatio_gt_two_of_normal_nine
    (D S : Subgroup K) [D.Normal] [IsElementaryAbelian 3 D]
    (hD : Nat.card D=9) (hS : IsPGroup 2 S) (hgen : D ⊔ S=⊤)
    (hcent : centralizer (D : Set K)=D)
    (Q : Subgroup (MulAut D)) (eQ : Q ≃* QuaternionGroup 2)
    (hQ : Q ≤ ((MulAut.conjNormal : K →* MulAut D).comp S.subtype).range)
    (ρ : Representation (ZMod 2) K V) (hf : Function.Injective ρ) :
    2 < BinaryOffender.cubicRatio ρ := by
  classical
  obtain ⟨c⟩ := quaternion_coordinates hD
  let a := (MulAut.conjNormal : K →* MulAut D).comp S.subtype
  let e := quaternionLinearized c
  let j := e.toMonoidHom.comp a
  have hdis : Disjoint D S := by
    obtain ⟨n,hn⟩ := hS.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hD,hn]
    exact (by decide : Nat.Coprime 9 2).pow_right n
  have hji : Function.Injective j := by
    apply (MonoidHom.ker_eq_bot_iff j).mp
    apply le_bot_iff.mp
    intro s hs
    have ha : a s=1 := e.injective (hs.trans e.map_one.symm)
    have hc : (s:K)∈centralizer (D:Set K) := by
      rw [← MulAut.conjNormal_ker_eq_centralizer D]
      exact ha
    have hd : (s:K)∈D := hcent ▸ hc
    exact Subtype.ext (mem_bot.mp (hdis.le_bot ⟨hd,s.property⟩))
  have hQj : Q.map e.toMonoidHom ≤ j.range := by
    rintro _ ⟨q,hq,rfl⟩
    obtain ⟨s,hs⟩ := hQ hq
    exact ⟨s,congrArg e hs⟩
  have hQE : Nonempty ((Q.map e.toMonoidHom) ≃* QuaternionGroup 2) :=
    ⟨(e.subgroupMap Q).symm.trans eQ⟩
  have heq : Q.map e.toMonoidHom = GeneralLinearGroup.threeQuaternion :=
    GeneralLinearGroup.three_quaternion_subgroup_eq _ _ hQE
      ⟨GeneralLinearGroup.threeQuaternionEquiv⟩
  have hQj' : GeneralLinearGroup.threeQuaternion ≤ j.range := heq ▸ hQj
  obtain ⟨f,_,_⟩ := SourceComparison.equiv_affine_of_complement D S hgen hdis c j
    (fun s v => (quaternionLinearized_apply c (a s) v).symm)
  apply lt_of_not_ge
  intro hsmall
  exact quaternion_cubicRatio_not_le_two j hji hQj'
    (ρ.comp f.symm.toMonoidHom) (hf.comp f.symm.injective)
    (BinaryOffender.cubicRatio_comp_equiv_le_two ρ f.symm hsmall)

omit [Finite K] in
/-- A normal odd abelian Hall subgroup is self-centralizing when the two-core
is trivial. The proof uses the specified two-subgroup supplement. -/
theorem centralizer_eq_nine_of_twoCore_eq_bot
    (D S : Subgroup K) [D.Normal] [IsElementaryAbelian 3 D]
    (hS : IsPGroup 2 S) (hgen : D ⊔ S=⊤) (hcore : pCore 2 K=⊥) :
    centralizer (D : Set K)=D := by
  let C := S ⊓ centralizer (D : Set K)
  have hDC : D ≤ centralizer (C : Set K) := le_centralizer_iff.mp inf_le_right
  have hSC : S ≤ normalizer (C : Set K) :=
    (le_inf S.le_normalizer le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  let : C.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← hgen]
    exact sup_le (hDC.trans (centralizer_le_normalizer _)) hSC))
  have hCp : IsPGroup 2 C := hS.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hC : C=⊥ := le_bot_iff.mp ((show C ≤ pCore 2 K from
    le_sSup ⟨inferInstance,hCp⟩).trans_eq hcore)
  have hDcent : D ≤ centralizer (D : Set K) := by
    intro d hd v hv
    exact congrArg D.subtype (mul_comm (⟨v,hv⟩ : D) ⟨d,hd⟩)
  apply le_antisymm ?_ hDcent
  intro x hx
  obtain ⟨d,hd,s,hs,hprod⟩ := mem_sup_of_normal_left.mp (hgen.symm ▸ mem_top x)
  have hsc : s ∈ centralizer (D : Set K) := by
    have hh := (centralizer (D:Set K)).mul_mem
      ((centralizer (D:Set K)).inv_mem (hDcent hd)) hx
    rw [← hprod,inv_mul_cancel_left] at hh
    exact hh
  have hs1 : s=1 := mem_bot.mp (hC ▸ (show s∈C from ⟨hs,hsc⟩))
  rw [← hprod,hs1,mul_one]
  exact hd

/-- The reduced-action form: the two-core calculation discharges the
centralizer premise, while the actual quaternion image remains marked. -/
theorem cubicRatio_gt_two_of_twoCore_eq_bot
    (D S : Subgroup K) [D.Normal] [IsElementaryAbelian 3 D]
    (hD : Nat.card D=9) (hS : IsPGroup 2 S) (hgen : D ⊔ S=⊤)
    (hcore : pCore 2 K=⊥)
    (Q : Subgroup (MulAut D)) (eQ : Q ≃* QuaternionGroup 2)
    (hQ : Q ≤ ((MulAut.conjNormal : K →* MulAut D).comp S.subtype).range)
    (ρ : Representation (ZMod 2) K V) (hf : Function.Injective ρ) :
    2 < BinaryOffender.cubicRatio ρ :=
  cubicRatio_gt_two_of_normal_nine D S hD hS hgen
    (centralizer_eq_nine_of_twoCore_eq_bot D S hS hgen hcore) Q eQ hQ ρ hf

end Representation.AffineNine
