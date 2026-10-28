module
public import Theory.SpecificGroups.PSL3.LinearThreeLocalAffine
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.PGroupCore
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Sylow
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Inner
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
/-!
# A ternary affine subgroup with cyclic Sylow four

The rotation matrix [[0,1],[-1,0]] acts faithfully and irreducibly on the
additive plane over F₃. Its semidirect product E₉:C₄ has a maximal nonnormal
Sylow two-subgroup, trivial two-core, and two-residual E₉. The central
involution of C₄ is retained explicitly.

The existing affine line-local coordinates embed this group in PSL₃(3).
Coefficient transport and projective involution conjugacy place its central
involution at any prescribed involution over any field of order three.
The finite checks cover only the rotation action on the nine-point plane;
subgroup maximality and residual calculations are structural proofs.

This supplies the order-nine solvable local group for the PSL₃(3) branch
of Aschbacher–Smith E.2.17, printed p.230.
-/
public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.TernaryAffineFour
abbrev F := ZMod 3
abbrev C := Multiplicative (ZMod 4)
abbrev V := Multiplicative (Fin 2 → F)
@[expose] def rotation : SL(2,F) := ⟨!![0,1;-1,0], by decide⟩
@[expose] def linear : C →* SL(2,F) where
  toFun c := rotation ^ c.toAdd.val
  map_one' := by decide
  map_mul' := by decide +kernel
@[expose] def action : C →* MulAut V := (SL2.naturalAction F).comp linear
abbrev Local := V ⋊[action] C
instance : Fintype Local := Fintype.ofEquiv (V×C) SemidirectProduct.equivProd.symm
@[expose] def complement : Subgroup Local := (SemidirectProduct.inr : C →* Local).range
@[expose] def plane : Subgroup Local := (SemidirectProduct.inl : V →* Local).range
@[expose] def central : Local := SemidirectProduct.inr (Multiplicative.ofAdd (2:ZMod 4))

private theorem linear_injective : Function.Injective linear := by decide +kernel
private theorem span (v : V) (hv : v≠1) (w : V) :
    ∃ a b : ZMod 3, v^a.val * action (Multiplicative.ofAdd (1:ZMod 4)) v ^ b.val = w := by
  revert v w
  decide +kernel

private theorem faithful (c : C) (hc : ∀v : V, action c v=v) : c=1 := by
  revert c
  decide +kernel

theorem mem_complement_iff (g : Local) : g∈complement ↔ g.left=1 := by
  constructor
  · rintro ⟨c,rfl⟩
    rfl
  · intro h
    refine ⟨g.right,?_⟩
    apply SemidirectProduct.ext
    · exact h.symm
    · rfl

private theorem normal_detects (g : Local) (hg : g.left=1)
    (hn : ∀v : V, ((SemidirectProduct.inl v : Local)*g*(SemidirectProduct.inl v)⁻¹).left=1) :
    g=1 := by
  apply SemidirectProduct.ext hg
  apply faithful g.right
  intro v
  have hx : v*(action g.right v)⁻¹=1 := by simpa [hg] using hn v
  exact (mul_inv_eq_one.mp hx).symm

private theorem normal_eq_bot_of_le_complement (N : Subgroup Local) [N.Normal]
    (hN : N≤complement) : N=⊥ := by
  apply bot_unique
  intro g hg
  rw [mem_bot]
  apply normal_detects g ((mem_complement_iff g).mp (hN hg))
  intro v
  exact (mem_complement_iff _).mp (hN ((inferInstance : N.Normal).conj_mem g hg (SemidirectProduct.inl v)))

theorem complement_normalCore : complement.normalCore=⊥ :=
  normal_eq_bot_of_le_complement _ (normalCore_le _)

theorem card_complement : Nat.card complement=4 := by
  change Nat.card (SemidirectProduct.inr : C →* Local).range=4
  rw [← Nat.card_congr (MonoidHom.ofInjective (show Function.Injective
    (SemidirectProduct.inr : C →* Local) from SemidirectProduct.inr_injective)).toEquiv]
  exact Nat.card_eq_fintype_card.trans (by decide)

theorem card_plane : Nat.card plane=9 := by
  change Nat.card (SemidirectProduct.inl : V →* Local).range=9
  rw [← Nat.card_congr (MonoidHom.ofInjective (show Function.Injective
    (SemidirectProduct.inl : V →* Local) from SemidirectProduct.inl_injective)).toEquiv]
  exact Nat.card_eq_fintype_card.trans (by decide)

private theorem card_local : Nat.card Local=36 := by
  rw [Nat.card_congr SemidirectProduct.equivProd,Nat.card_prod,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  decide

private theorem complement_index : complement.index=9 := by
  have h := complement.index_mul_card
  rw [card_complement,card_local] at h
  omega

@[expose] noncomputable def sylow : Sylow 2 Local :=
  (show IsPGroup 2 complement from IsPGroup.of_card (n:=2) (by rw [card_complement]; decide)).toSylow
    (by rw [complement_index]; decide)

theorem sylow_coe : (sylow : Subgroup Local)=complement := rfl

theorem twoCore : pCore 2 Local=⊥ :=
  normal_eq_bot_of_le_complement _ (pCore_isPGroup.le_sylow_of_normal sylow)

theorem complement_not_normal : ¬complement.Normal := by
  intro h
  let := h
  have he := normal_eq_bot_of_le_complement complement le_rfl
  have hc := card_complement
  rw [he,Nat.card_eq_fintype_card] at hc
  norm_num at hc

theorem complement_isCoatom : IsCoatom complement := by
  apply isCoatom_iff_ge_of_le.mpr ⟨?_,?_⟩
  · intro he
    have hc := card_complement
    rw [he,card_top,card_local] at hc
    omega
  · intro A hA hCA g hg
    apply (mem_complement_iff g).mpr
    by_contra hgn
    apply hA
    have hv : (SemidirectProduct.inl g.left : Local)∈A := by
      have hm := A.mul_mem hg (A.inv_mem (hCA ⟨g.right,rfl⟩))
      have he : g*(SemidirectProduct.inr g.right)⁻¹=SemidirectProduct.inl g.left := by
        exact mul_inv_eq_iff_eq_mul.mpr (SemidirectProduct.inl_left_mul_inr_right g).symm
      rwa [he] at hm
    have hiv : (SemidirectProduct.inl (action (Multiplicative.ofAdd (1:ZMod 4)) g.left) : Local)∈A := by
      rw [SemidirectProduct.inl_aut]
      exact A.mul_mem (A.mul_mem (hCA ⟨_,rfl⟩) hv) (hCA ⟨_,rfl⟩)
    have hplane (w : V) : (SemidirectProduct.inl w : Local)∈A := by
      obtain ⟨a,b,hab⟩ := span g.left hgn w
      rw [←hab,map_mul,map_pow,map_pow]
      exact A.mul_mem (A.pow_mem hv _) (A.pow_mem hiv _)
    apply top_unique
    intro x _
    rw [←SemidirectProduct.inl_left_mul_inr_right x]
    exact A.mul_mem (hplane x.left) (hCA ⟨x.right,rfl⟩)

theorem residual_eq_plane : pResidual 2 Local=plane := by
  have hc : IsPGroup 2 C := IsPGroup.of_card (n:=2) (by rw [Nat.card_eq_fintype_card]; decide)
  have hv : IsPGroup 3 V := IsPGroup.of_card (n:=2) (by rw [Nat.card_eq_fintype_card]; decide)
  have hp : IsPGroup 3 plane := hv.of_surjective
    (SemidirectProduct.inl : V→*Local).rangeRestrict
    (SemidirectProduct.inl : V→*Local).rangeRestrict_surjective
  apply le_antisymm
  · rw [plane,SemidirectProduct.range_inl_eq_ker_rightHom]
    exact pResidual_le_ker_of_isPGroup 2 SemidirectProduct.rightHom hc
  · let q := QuotientGroup.mk' (pResidual 2 Local)
    have hh := IsPGroup.disjoint_of_coprime (hp.map q)
      ((isPGroup_quotient_pResidual 2).to_subgroup ⊤) (by decide : Nat.Coprime 3 2)
    have he : plane.map q=⊥ := by simpa using hh
    have hk := (map_eq_bot_iff plane).mp he
    simpa only [q,QuotientGroup.ker_mk'] using hk

theorem card_residual : Nat.card (pResidual 2 Local)=9 := by
  rw [residual_eq_plane,card_plane]

theorem solvable : Group.IsSolvable Local := by
  apply Group.isSolvable_of_ker_le_range
    (SemidirectProduct.inl : V→*Local) (SemidirectProduct.rightHom : Local→*C)
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]

theorem central_order : orderOf central=2 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

theorem central_mem : central∈complement := ⟨_,rfl⟩
theorem complement_centralizes : complement≤centralizer ({central}:Set Local) := by
  rintro x ⟨c,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  change SemidirectProduct.inr c * SemidirectProduct.inr _ = SemidirectProduct.inr _ * SemidirectProduct.inr c
  rw [←map_mul,←map_mul,mul_comm]

@[expose] def affineEmbedding : Local →* SL2.Affine F :=
  SemidirectProduct.map (MonoidHom.id V) linear (by intro c; rfl)
private theorem affineEmbedding_injective : Function.Injective affineEmbedding := by
  intro x y h
  apply SemidirectProduct.ext
  · exact congrArg (fun z : SL2.Affine F => z.left) h
  · exact linear_injective (congrArg (fun z : SL2.Affine F => z.right) h)

@[expose] noncomputable def projectiveEmbedding : Local →* PSL(3,F) :=
  (LinearThree.lineLocal F).subtype.comp
    ((LinearThree.lineLocalEquivAffine F).symm.toMonoidHom.comp affineEmbedding)
theorem projectiveEmbedding_injective : Function.Injective projectiveEmbedding :=
  Subtype.val_injective.comp ((LinearThree.lineLocalEquivAffine F).symm.injective.comp
    affineEmbedding_injective)
theorem sylow_isCoatom : IsCoatom (sylow : Subgroup Local) := complement_isCoatom
theorem sylow_not_normal : ¬(sylow : Subgroup Local).Normal := complement_not_normal
theorem sylow_centralizes : (sylow : Subgroup Local)≤centralizer ({central}:Set Local) :=
  complement_centralizes

theorem exists_embedding {E : Type*} [Field E] [Finite E] (hE : Nat.card E=3)
    (t : PSL(3,E)) (ht : orderOf t=2) :
    ∃ f : Local→*PSL(3,E), Function.Injective f ∧ f central=t := by
  let : Fintype E := Fintype.ofFinite E
  let e : F≃+*E := ZMod.ringEquivOfPrime E (by decide)
    (by simpa only [←Nat.card_eq_fintype_card] using hE)
  let f := (Atlas.fieldEquivPSL 3 e).toMonoidHom.comp projectiveEmbedding
  have hf : Function.Injective f := (Atlas.fieldEquivPSL 3 e).injective.comp projectiveEmbedding_injective
  have h2 : (2:E)≠0 := by
    intro hh
    have he : e (2:F)=e 0 := by simpa only [map_ofNat,map_zero] using hh
    have h20 := e.injective he
    exact (by decide : (2:F)≠0) h20
  have hz : orderOf (f central)=2 :=
    (orderOf_injective f hf central).trans central_order
  obtain ⟨x,hx,hxz⟩ := OddInvolutionFixed.involution_lift (f central) hz
  obtain ⟨y,hy,hyt⟩ := OddInvolutionFixed.involution_lift t ht
  have hconj : IsConj (f central) t := by
    rw [←hxz,←hyt]
    exact (projection E).map_isConj (SL3.involutions_isConj E x y hx hy h2)
  obtain ⟨g,hg⟩ := isConj_iff.mp hconj
  refine ⟨(MulAut.conj g).toMonoidHom.comp f,(MulAut.conj g).injective.comp hf,?_⟩
  exact hg
end Matrix.PSL3.TernaryAffineFour
