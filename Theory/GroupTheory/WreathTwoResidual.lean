module

public import Theory.GroupTheory.WreathTwoSylowModel
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.PGroupCore
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Residuals and normal Sylow subgroups in the binary-plane wreath group

The two-residual of `SL₂(2) ≀ᵣ C₂` is its cubic base subgroup, with explicit
coordinates identifying it with `C₃ × C₃`. Every nontrivial subgroup normal
in an actual Sylow two-subgroup contains an involution inverting this entire
residual. Consequently its normal closure has the full two-residual, and
the actor has trivial two-core.

The standard Sylow model is dihedral of order eight. Every nonidentity
normal subgroup contains its central involution: a noncentral rotation has
that square, and a reflection has it as a commutator. This also covers a
normal subgroup of order two. Sylow conjugacy transports the assertion to
the specified Sylow subgroup. Only the six-element plane group and the
eight-element dihedral group require finite certificates; the wreath and
residual arguments are structural.

Source: Aschbacher–Smith, Lemma 15.3.7, printed p.1122 (PDF p.1139).
The cubic-base and standard-inverter calculations extend those in
`WreathTwoOddInverter`, without its elementary-four hypothesis.
-/

open Subgroup
namespace Theory.GroupTheory.WreathTwoResidual
private abbrev SL := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
private abbrev C2 := Multiplicative (ZMod 2)
/-- The literal actor of two binary planes. -/
public abbrev Actor := RegularWreathProduct
  (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2))
private abbrev W := Actor
private instance : DecidableEq W := fun a b => decidable_of_iff
  (a.left=b.left ∧ a.right=b.right) RegularWreathProduct.ext_iff.symm

private def C : Subgroup W where
  carrier := {x | x.right = 1 ∧ ∀ i, x.left i ^ 3 = 1}
  one_mem' := by simp
  mul_mem' := by
    have h : ∀ a b : SL, a^3=1 → b^3=1 → (a*b)^3=1 := by decide +kernel
    intro a b ha hb
    exact ⟨by simp [ha.1,hb.1],fun i => h _ _ (ha.2 i) (hb.2 _)⟩
  inv_mem' := by
    intro a ha
    exact ⟨by simp [ha.1],fun i => by simpa using congrArg Inv.inv (ha.2 (a.right*i))⟩

private instance : C.Normal where
  conj_mem x hx g := by
    refine ⟨by simp [hx.1], ?_⟩
    intro i
    have he : (g*x*g⁻¹).left i = g.left i * x.left (g.right⁻¹*i) * (g.left i)⁻¹ := by
      simp [hx.1]
    rw [he,conj_pow,hx.2]
    simp

private theorem card_C : Nat.card C = 9 := by
  let e : C ≃ (C2 → {x : SL // x^3=1}) := {
    toFun := fun x i => ⟨x.val.left i,x.property.2 i⟩
    invFun := fun a => ⟨⟨fun i => (a i).val,1⟩,rfl,fun i => (a i).property⟩
    left_inv := fun x => Subtype.ext (RegularWreathProduct.ext rfl x.property.1.symm)
    right_inv := fun a => rfl }
  rw [Nat.card_congr e,Nat.card_fun]
  have h : Nat.card {x : SL // x^3=1}=3 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  rw [h]
  norm_num [Nat.card_eq_fintype_card]

private theorem card_W : Nat.card W = 72 := by
  rw [RegularWreathProduct.card]
  have h : Nat.card SL = 6 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  rw [h]
  norm_num [Nat.card_eq_fintype_card]

private theorem C_cube (x : W) (hx : x∈C) : x^3=1 := by
  apply RegularWreathProduct.ext
  · funext i
    simpa [pow_succ,hx.1] using hx.2 i
  · simp [pow_succ,hx.1]

private theorem residual_eq_C : pResidual 2 W = C := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨inferInstance, IsPGroup.iff_card.mpr ⟨3, ?_⟩⟩
    have h := C.card_mul_index
    rw [card_C,card_W,Subgroup.index_eq_card] at h
    omega
  · intro x hx
    exact mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one (C_cube x hx)))

private def z : W := wreathTwoDihedralHom (DihedralGroup.r 2)

private theorem z_inverts : orderOf z = 2 ∧ ∀ x : W, x∈C → z*x*z⁻¹=x⁻¹ := by
  let t : SL := ⟨!![1,1;0,1],by decide⟩
  have hi : ∀ x : SL, x^3=1 → t*x*t⁻¹=x⁻¹ := by decide +kernel
  have hz : z = (⟨fun _ => t,1⟩ : W) := by decide +kernel
  constructor
  · have hne : z≠1 := by decide +kernel
    have hpow : z^2=1 := by decide +kernel
    exact orderOf_eq_prime_iff.mpr ⟨hpow,hne⟩
  · intro x hx
    rw [hz]
    apply RegularWreathProduct.ext
    · funext i
      simpa [hx.1] using hi (x.left i) (hx.2 i)
    · simp [hx.1]

private theorem z_mem_normal (R : Subgroup W) (hle : R ≤ (wreathTwoSylow : Subgroup W))
    (hn : (wreathTwoSylow : Subgroup W) ≤ normalizer (R : Set W)) (hne : R≠⊥) : z∈R := by
  have hc : ∀ x : DihedralGroup 4, x≠1 →
      x=DihedralGroup.r 2 ∨ x^2=DihedralGroup.r 2 ∨ ∃ y : DihedralGroup 4, y*x*y⁻¹*x⁻¹=DihedralGroup.r 2 := by
    decide +kernel
  obtain ⟨x,hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨a,ha⟩ := (wreathTwoSylow_coe ▸ hle x.property)
  have hane : a≠1 := by
    intro h
    apply hx
    apply Subtype.ext
    simpa [h] using ha.symm
  rcases hc a hane with he | hs | ⟨b,hb⟩
  · have h := x.property
    simpa only [← ha,he,z] using h
  · have h := R.pow_mem x.property 2
    rwa [← ha,← map_pow,hs] at h
  · have hbmem : wreathTwoDihedralHom b∈(wreathTwoSylow : Subgroup W) := by
      rw [wreathTwoSylow_coe]
      exact ⟨b,rfl⟩
    have hconj := (hn hbmem (x : W)).mp x.property
    have h := R.mul_mem hconj (R.inv_mem x.property)
    simpa only [← ha,← map_inv,← map_mul,hb,z] using h

private theorem exists_inverter (P : Sylow 2 W) (R : Subgroup W)
    (hle : R≤(P : Subgroup W)) (hn : (P : Subgroup W) ≤ normalizer (R : Set W))
    (hne : R≠⊥) : ∃ r : W, r∈R ∧ orderOf r=2 ∧ ∀ x : W, x∈C → r*x*r⁻¹=x⁻¹ := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq W wreathTwoSylow P
  let e : W ≃* W := (MulAut.conj g).symm
  have hP : (P : Subgroup W).map e.toMonoidHom = (wreathTwoSylow : Subgroup W) := by
    apply (map_symm_eq_iff_map_eq (e := MulAut.conj g) (wreathTwoSylow : Subgroup W)).mpr
    exact congrArg (fun Q : Sylow 2 W => (Q : Subgroup W)) hg
  have hC : C.map e.toMonoidHom = C := by
    rw [← residual_eq_C]
    exact map_pResidual 2 e
  let R' := R.map e.toMonoidHom
  have hle' : R'≤(wreathTwoSylow : Subgroup W) := hP ▸ map_mono hle
  have hn' : (wreathTwoSylow : Subgroup W) ≤ normalizer (R' : Set W) := by
    rw [← hP]
    exact (map_mono hn).trans (le_normalizer_map _)
  have hne' : R'≠⊥ := by
    intro hh
    apply hne
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_bot]
    exact hh
  have hz := z_mem_normal R' hle' hn' hne'
  obtain ⟨r,hr,her⟩ := hz
  change e r = z at her
  refine ⟨r,hr, ?_, ?_⟩
  ·
    rw [← e.orderOf_eq r,her]
    exact z_inverts.1
  · intro x hx
    have hxc : e x∈C := hC ▸ (show e x ∈ C.map e.toMonoidHom from ⟨x,hx,rfl⟩)
    apply e.injective
    simp only [map_mul,map_inv,her]
    exact z_inverts.2 (e x) hxc

private def cubic : SL := ⟨!![0,1;1,1],by decide⟩
private def cubicHom : Multiplicative (ZMod 3) →* SL where
  toFun a := cubic ^ a.toAdd.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private theorem cubicHom_injective : Function.Injective cubicHom := by decide +kernel
private theorem cubicHom_coverage : ∀ x : SL, x^3=1 → ∃ a, cubicHom a=x := by decide +kernel
private theorem cubicHom_cube : ∀ a, (cubicHom a)^3=1 := by decide +kernel

private noncomputable def cubeEquiv : C ≃* Multiplicative (Fin 2 → ZMod 3) := by
  let f₀ : (C2 → Multiplicative (ZMod 3)) →* W := {
    toFun := fun a => ⟨fun i => cubicHom (a i),1⟩
    map_one' := by
      apply RegularWreathProduct.ext
      · funext i; exact map_one cubicHom
      · rfl
    map_mul' := by
      intro a b
      apply RegularWreathProduct.ext
      · funext i
        simp
      · simp }
  let f : (C2 → Multiplicative (ZMod 3)) →* C := f₀.codRestrict C
    (fun a => ⟨rfl,fun i => cubicHom_cube (a i)⟩)
  have hfi : Function.Injective f := by
    intro a b h
    funext i
    apply cubicHom_injective
    exact congrArg (fun x : C => x.val.left i) h
  have hfs : Function.Surjective f := by
    intro x
    choose a ha using fun i => cubicHom_coverage (x.val.left i) (x.property.2 i)
    refine ⟨a,Subtype.ext (RegularWreathProduct.ext (funext ha) x.property.1.symm)⟩
  let idx : C2 ≃ Fin 2 := Multiplicative.toAdd.trans (ZMod.finEquiv 2).toEquiv.symm
  exact (MulEquiv.ofBijective f ⟨hfi,hfs⟩).symm.trans
    ((MulEquiv.arrowCongr idx (MulEquiv.refl _)).trans
      (MulEquiv.piMultiplicative (fun _ : Fin 2 => ZMod 3)).symm)

private theorem C_le_normal_of_inverter (N : Subgroup W) [N.Normal]
    (r : W) (hr : r∈N) (hi : ∀ x : W, x∈C → r*x*r⁻¹=x⁻¹) : C ≤ N := by
  intro x hx
  have hconj := (inferInstance : N.Normal).conj_mem r⁻¹ (N.inv_mem hr) x
  have hmem := N.mul_mem hr hconj
  have hpow : x*x*x=1 := by simpa only [pow_succ,pow_zero,one_mul] using C_cube x hx
  have he : x⁻¹*x⁻¹=x := by
    rw [← mul_inv_rev]
    exact inv_eq_of_mul_eq_one_right hpow
  simpa only [← mul_assoc,hi x hx,he] using hmem

private theorem pCore_eq_bot : pCore 2 W = ⊥ := by
  by_contra hne
  let P := wreathTwoSylow
  obtain ⟨r,hr,_,hi⟩ := exists_inverter P (pCore 2 W)
    (pCore_isPGroup.le_sylow_of_normal P) (by rw [normalizer_eq_top]; exact le_top) hne
  have hle := C_le_normal_of_inverter (pCore 2 W) r hr hi
  have hp : IsPGroup 3 C := IsPGroup.of_card (n := 2) card_C
  have hd := IsPGroup.disjoint_of_ne 3 2 (by decide) C (pCore 2 W) hp pCore_isPGroup
  have hz : C=⊥ := disjoint_self.mp (hd.mono_right hle)
  have hcard := Subgroup.card_eq_one.mpr hz
  rw [card_C] at hcard
  omega

private theorem normalClosure_residual (P : Sylow 2 W) (R : Subgroup W)
    (hle : R≤(P : Subgroup W)) (hn : (P : Subgroup W) ≤ normalizer (R : Set W))
    (hne : R≠⊥) :
    (pResidual 2 (normalClosure (R : Set W))).map (normalClosure (R : Set W)).subtype =
      pResidual 2 W := by
  obtain ⟨r,hr,_,hi⟩ := exists_inverter P R hle hn hne
  have hC : C ≤ normalClosure (R : Set W) :=
    C_le_normal_of_inverter _ r (subset_normalClosure hr) hi
  apply le_antisymm (map_pResidual_le 2 _)
  rw [residual_eq_C]
  intro x hx
  refine ⟨⟨x,hC hx⟩,?_,rfl⟩
  apply mem_pResidual_of_orderOf_coprime
  apply (by decide : Nat.Coprime 2 3).of_dvd_right
  apply orderOf_dvd_of_pow_eq_one
  exact (show (⟨x,hC hx⟩ : normalClosure (R : Set W))^3=1 from Subtype.ext (C_cube x hx))

/-- An actual isomorphism of the two-residual with the elementary group of order nine. -/
public theorem residual_equiv_elementaryNine :
    Nonempty ((pResidual 2 Actor) ≃* Multiplicative (Fin 2 → ZMod 3)) :=
  ⟨(MulEquiv.subgroupCongr residual_eq_C).trans cubeEquiv⟩

/-- Every nontrivial normal Sylow subgroup contains a full residual inverter;
no elementary-abelian or order-four premise is needed. -/
public theorem exists_normal_sylow_inverter (P : Sylow 2 Actor) (R : Subgroup Actor)
    (hle : R ≤ (P : Subgroup Actor))
    (hn : (P : Subgroup Actor) ≤ normalizer (R : Set Actor)) (hne : R ≠ ⊥) :
    ∃ r : Actor, r ∈ R ∧ orderOf r = 2 ∧
      ∀ x : Actor, x ∈ pResidual 2 Actor → r*x*r⁻¹ = x⁻¹ := by
  simpa only [residual_eq_C] using exists_inverter P R hle hn hne

/-- The normal closure of a nontrivial normal Sylow subgroup has the full residual. -/
public theorem normalClosure_residual_eq (P : Sylow 2 Actor) (R : Subgroup Actor)
    (hle : R ≤ (P : Subgroup Actor))
    (hn : (P : Subgroup Actor) ≤ normalizer (R : Set Actor)) (hne : R ≠ ⊥) :
    (pResidual 2 (normalClosure (R : Set Actor))).map
      (normalClosure (R : Set Actor)).subtype = pResidual 2 Actor :=
  normalClosure_residual P R hle hn hne

/-- The literal wreath actor has trivial two-core. -/
public theorem twoCore_eq_bot : pCore 2 Actor = ⊥ := pCore_eq_bot

end Theory.GroupTheory.WreathTwoResidual
