module
public import Theory.Representation.BinaryTensorThree.WreathCoordinates
public import Theory.Representation.BinaryTensorThree.FixedCodimension

/-!
# Outer involutions cannot belong to tensor (F−1)-offenders

Conjugate an outer involution in the concrete Sylow wreath square to its
swap. Its square-one centralizer has at most twelve elements, so an elementary
subgroup containing it has rank at most three. Every independent second
involution has common fixed space of codimension at least five. Small
linear left-inverse certificates verify this last calculation on five
basis vectors, rather than enumerating all vectors of the tensor space.
The cyclic case has rank one and displacement three. Thus every elementary
actor with fixed codimension at most its rank plus one lies in the base.

Sylow conjugacy and the factor-interchange quotient transfer this conclusion
to the full tensor action group. The original Chapter 10 automizer application
then identifies that base with the image of its literal component orbit.
Source: Aschbacher--Smith H.4.10(3), printed p.384, used in 8.3.11, p.726.
-/

@[expose] public section
namespace BinaryTensorThree.Small
open BinaryPermutation.FiveTensorSquare
private def outerPivot : Fin 44 → Fin 5 → Fin 9 := ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, 2, 3, 5], ![0, 1, 2, 3, 5], ![0, 1, 2, 3, 5], ![0, 1, 2, 3, 5], ![1, 2, 3, 4, 5], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 5], ![0, 1, 2, 3, 5], ![0, 1, 2, 3, 5], ![0, 1, 2, 3, 5], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 5], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 5], ![0, 1, 2, 3, 5], ![0, 1, 2, 5, 6], ![0, 1, 2, 5, 6], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 5], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 5], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 5], ![0, 1, 2, 3, 5], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 5], ![0, 1, 2, 3, 5], ![0, 1, 2, 3, 5], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 5], ![0, 1, 2, 3, 5], ![0, 1, 2, 3, 4], ![1, 2, 3, 4, 5], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], ![1, 2, 3, 4, 5], ![1, 2, 3, 4, 5]]
private def outerOutput : Fin 44 → Fin 5 → Fin 18 := ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![1, 2, 5, 9, 12], ![1, 2, 5, 10, 13], ![1, 2, 5, 9, 12], ![1, 2, 5, 9, 12], ![1, 2, 5, 9, 12], ![1, 2, 9, 11, 12], ![1, 2, 5, 9, 10], ![1, 2, 5, 9, 10], ![1, 2, 5, 9, 10], ![1, 2, 5, 9, 10], ![1, 2, 9, 10, 12], ![1, 2, 5, 9, 10], ![1, 2, 9, 10, 12], ![1, 2, 9, 10, 13], ![1, 2, 5, 12, 13], ![1, 2, 5, 9, 12], ![1, 2, 5, 10, 13], ![1, 2, 5, 10, 13], ![1, 2, 9, 12, 14], ![1, 2, 5, 9, 12], ![1, 2, 9, 12, 13], ![1, 2, 5, 9, 10], ![1, 2, 9, 10, 11], ![1, 2, 9, 10, 16], ![1, 2, 5, 9, 11], ![1, 2, 5, 9, 11], ![1, 2, 9, 10, 11], ![1, 2, 9, 10, 11], ![1, 2, 5, 9, 10], ![1, 2, 5, 9, 10], ![1, 2, 5, 9, 10], ![1, 2, 9, 10, 12], ![1, 2, 5, 9, 10], ![1, 2, 5, 9, 10], ![1, 2, 9, 10, 12], ![1, 2, 5, 9, 10], ![1, 2, 9, 10, 11], ![1, 2, 9, 10, 13], ![1, 2, 9, 10, 11], ![1, 2, 9, 10, 11], ![1, 2, 5, 9, 10], ![1, 2, 5, 9, 10]]
private def outerInverse : Fin 44 → Fin 5 → Nat := ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![10, 21, 2, 20, 4], ![10, 21, 2, 20, 4], ![25, 17, 2, 16, 4], ![10, 21, 2, 20, 4], ![10, 2, 11, 20, 4], ![29, 19, 2, 18, 10], ![8, 16, 2, 17, 4], ![8, 16, 2, 17, 4], ![8, 22, 2, 23, 4], ![8, 16, 2, 17, 4], ![4, 8, 2, 9, 17], ![8, 16, 2, 17, 4], ![4, 8, 2, 9, 30], ![29, 8, 2, 9, 16], ![8, 16, 2, 17, 4], ![10, 23, 2, 22, 4], ![23, 1, 31, 4, 29], ![23, 1, 28, 4, 30], ![26, 30, 2, 31, 9], ![10, 23, 2, 22, 4], ![30, 6, 2, 7, 18], ![25, 16, 2, 17, 4], ![4, 19, 2, 18, 9], ![26, 31, 2, 30, 9], ![8, 23, 2, 22, 4], ![8, 18, 2, 19, 4], ![4, 19, 2, 18, 27], ![31, 8, 2, 9, 18], ![8, 16, 2, 17, 4], ![8, 16, 2, 17, 4], ![8, 16, 2, 17, 4], ![4, 8, 2, 9, 25], ![8, 16, 2, 17, 4], ![8, 20, 2, 21, 4], ![4, 8, 2, 9, 16], ![9, 2, 8, 16, 4], ![6, 21, 2, 20, 24], ![30, 5, 2, 4, 16], ![9, 21, 2, 20, 24], ![6, 21, 2, 20, 8], ![22, 2, 23, 15, 4], ![16, 2, 17, 15, 4]]
private def outerProbe (w : Fin 44) : (Fin 5 → ZMod 2) →ₗ[ZMod 2] Space where
  toFun c := ∑ i : Fin 5, c i • unit (outerPivot w i)
  map_add' x y := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' a x := by simp [mul_smul,Finset.smul_sum]
private def pairEntry (X : Space × Space) (i : Fin 18) : ZMod 2 :=
  if hi : i.val < 9 then X.1 ⟨i.val/3,by omega⟩ ⟨i.val%3,by omega⟩
  else X.2 ⟨(i.val-9)/3,by omega⟩ ⟨(i.val-9)%3,by omega⟩
private def outerDecode (w : Fin 44) : (Space × Space) →ₗ[ZMod 2] (Fin 5 → ZMod 2) where
  toFun X i := ∑ j : Fin 5, (if (outerInverse w i).testBit j.val then 1 else 0) *
    pairEntry X (outerOutput w j)
  map_add' X Y := by
    ext i
    simp only [Pi.add_apply,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [pairEntry,Prod.fst_add,Prod.snd_add,Matrix.add_apply]
    split_ifs <;> ring
  map_smul' c X := by
    ext i
    simp only [RingHom.id_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [pairEntry,Prod.smul_fst,Prod.smul_snd,Matrix.smul_apply,smul_eq_mul]
    split_ifs <;> ring
private def outerConjugator (a : P) : P := ⟨fun i => if i=1 then 1 else a.left 1,1⟩
private theorem outer_conjugate : ∀ a : P, a*a=1 → a.right≠1 →
    outerConjugator a * a * (outerConjugator a)⁻¹ = vertex 1 := by decide +kernel
private theorem outer_neighbors :
    (Finset.univ.filter (fun w : Fin 44 => vertex 1 * vertex w = vertex w * vertex 1)).card ≤ 12 := by
  decide +kernel
private theorem outer_certificate : ∀ w : Fin 44, w≠0 → w≠1 → ∀ i : Fin 5,
    outerDecode w (displacement 1 (outerProbe w (Pi.single i 1)),
      displacement w (outerProbe w (Pi.single i 1))) = Pi.single i 1 := by
  decide +kernel

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

private theorem actionSmall_apply (g : P) (X : Space) :
    actionSmall g X = action (toTensor g) X := rfl

theorem outer_elementary_rank_le_three (A : Subgroup P) [IsElementaryAbelian 2 A]
    (ha : vertex 1 ∈ A) : rank A ≤ 3 := by
  classical
  let s : Finset (Fin 44) := Finset.univ.filter (fun w => vertex w ∈ A)
  have hc : s.card ≤ 12 := le_trans (Finset.card_le_card (by
    intro w hw
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    exact congrArg (fun x : A => (x : P))
      (mul_comm (⟨vertex 1,ha⟩ : A)
        ⟨vertex w,(Finset.mem_filter.mp hw).2⟩))) outer_neighbors
  let f : s → A := fun w => ⟨vertex w.val,(Finset.mem_filter.mp w.property).2⟩
  have hf : Function.Surjective f := by
    intro b
    have hb : b.val*b.val=1 := by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) b.val b.property
    obtain ⟨w,hw⟩ := vertex_cover b.val hb
    exact ⟨⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw.symm ▸ b.property⟩⟩,
      Subtype.ext hw⟩
  have hcard : Nat.card A ≤ 12 :=
    (Nat.card_le_card_of_surjective f hf).trans (by simpa using hc)
  exact (Nat.log_mono_right hcard).trans (by decide : Nat.log 2 12 ≤ 3)

theorem outer_pair_fixedCodim_ge_five (A : Subgroup P)
    (ha : vertex 1 ∈ A)
    {w : Fin 44} (hb : vertex w ∈ A) (hw : w ≠ 0) (hwa : w ≠ 1) :
    5 ≤ fixedCodim actionSmall A := by
  let δ : Space →ₗ[ZMod 2] Space × Space :=
    (actionSmall (vertex 1) - LinearMap.id).prod
      (actionSmall (vertex w) - LinearMap.id)
  let f := δ.comp (outerProbe w)
  have hleft : (outerDecode w).comp f = LinearMap.id := by
    apply (Pi.basisFun (ZMod 2) (Fin 5)).ext
    intro i
    simpa only [f,δ,LinearMap.comp_apply,Pi.basisFun_apply,LinearMap.id_apply,
      LinearMap.prod_apply,Function.prod_apply,LinearMap.sub_apply,displacement,act_eq,actionSmall_apply]
      using outer_certificate w hw hwa i
  have hf : Function.Injective f := by
    intro x y hxy
    have hh := congrArg (outerDecode w) hxy
    change ((outerDecode w).comp f) x = ((outerDecode w).comp f) y at hh
    simpa only [hleft,LinearMap.id_apply] using hh
  have hle : f.range ≤ δ.range := by
    rintro _ ⟨c,rfl⟩
    exact ⟨outerProbe w c,rfl⟩
  have hr := Submodule.finrank_mono hle
  rw [LinearMap.finrank_range_of_inj hf] at hr
  have hfix : fixedSpace actionSmall A ≤ δ.ker := by
    intro x hx
    exact Prod.ext (sub_eq_zero.mpr (hx ⟨_,ha⟩)) (sub_eq_zero.mpr (hx ⟨_,hb⟩))
  have hk := Submodule.finrank_mono hfix
  have hn := δ.finrank_range_add_finrank_ker
  have hd := fixedCodim_add_finrank actionSmall A
  have hdim : Module.finrank (ZMod 2) (Fin 5 → ZMod 2) = 5 := by simp
  rw [hdim] at hr
  omega

/-- Every elementary actor whose displacement exceeds its rank by at most
one lies in the base. This includes nonquadratic actors. -/
theorem near_offender_right_eq_one (A : Subgroup P) [IsElementaryAbelian 2 A]
    (hbound : fixedCodim actionSmall A ≤ rank A + 1) :
    ∀ a ∈ A, a.right = 1 := by
  intro a ha
  by_contra hout
  have hsq : a*a=1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  let g := outerConjugator a
  let C := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
  have hs : vertex 1 ∈ C := by
    have he := outer_conjugate a hsq hout
    exact ⟨a,ha,he⟩
  have hsmall := outer_elementary_rank_le_three C hs
  have hc : fixedCodim actionSmall C ≤ rank C + 1 := by
    rw [fixedCodim_map_conj,rank_map_conj]
    exact hbound
  have hs2 : orderOf (vertex 1)=2 := orderOf_eq_prime
    (by decide +kernel : vertex 1 ^ 2=1) (by decide +kernel : vertex 1≠1)
  by_cases hcyc : C ≤ zpowers (vertex 1)
  · have hr : rank C ≤ 1 := by
      have hh := Nat.card_le_card_of_injective (inclusion hcyc) (inclusion_injective hcyc)
      rw [Nat.card_zpowers,hs2] at hh
      exact (Nat.log_mono_right hh).trans (by decide : Nat.log 2 2 ≤ 1)
    have hd := involution_fixedCodim (vertex 1) hs2
    have hm := Submodule.finrank_mono (fixedSpace_antitone actionSmall (zpowers_le.mpr hs))
    have h1 := fixedCodim_add_finrank actionSmall C
    have h2 := fixedCodim_add_finrank actionSmall (zpowers (vertex 1))
    omega
  · obtain ⟨b,hb,hba⟩ := SetLike.not_le_iff_exists.mp hcyc
    have hb1 : b ≠ 1 := fun he => hba (he ▸ (zpowers (vertex 1)).one_mem)
    have hbn : b ≠ vertex 1 := fun he => hba (he ▸ mem_zpowers (vertex 1))
    have hbsq : b*b=1 := by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb
    obtain ⟨w,rfl⟩ := vertex_cover b hbsq
    have hd := outer_pair_fixedCodim_ge_five C hs hb
      (fun he => hb1 (he ▸ vertex_zero)) (fun he => hbn (he ▸ rfl))
    omega

end BinaryTensorThree.Small
namespace BinaryTensorThree
open Subgroup Representation.BinaryOffender
open BinaryPermutation.FiveTensorSquare

/-- The factor-interchange quotient of the faithful tensor action. -/
private noncomputable def tensorParity : Group →* C2 :=
  RegularWreathProduct.rightHom.comp
    (MulEquiv.ofBijective wreathHom ⟨wreathHom_injective,wreathHom_surjective⟩).symm.toMonoidHom

private theorem tensorParity_wreathHom (w : Wreath) : tensorParity (wreathHom w) = w.right := by
  let e := MulEquiv.ofBijective wreathHom ⟨wreathHom_injective,wreathHom_surjective⟩
  exact congrArg RegularWreathProduct.right (e.symm_apply_apply w)

private theorem tensorParity_eq_one_iff (g : Group) :
    tensorParity g = 1 ↔ g ∈ baseEmbedding.range := by
  constructor
  · intro hg
    let e := MulEquiv.ofBijective wreathHom ⟨wreathHom_injective,wreathHom_surjective⟩
    let w := e.symm g
    have hw : w.right=1 := hg
    refine ⟨(w.left 1,w.left swapIndex),?_⟩
    have he : wreathHom w = g := e.apply_symm_apply g
    change wreathMap w = g at he
    simpa only [wreathMap,hw,ite_true] using he
  · rintro ⟨a,rfl⟩
    rw [←wreathHom_base,tensorParity_wreathHom]
    rfl

private theorem tensorParity_small (g : Small.P) : tensorParity (Small.toTensorHom g) = g.right := by
  rw [←Small.wreathHom_comp]
  exact tensorParity_wreathHom _

/-- H.4.10(3): every elementary (F−1)-offender lies in the original tensor
base. No quadratic-action hypothesis is needed. -/
theorem near_offender_le_base (A : Subgroup Group) (hA : IsElementaryTwo A)
    (hbound : fixedCodim action A ≤ rank A + 1) : A ≤ baseEmbedding.range := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Group S Small.tensorSylow
  let C := A.map (MulAut.conj g).toMonoidHom
  have hC := hA.map_conj g
  have hCS : C ≤ (Small.tensorSylow : Subgroup Group) :=
    (congrArg Sylow.toSubgroup hg) ▸ map_mono hAS
  let B := C.comap Small.toTensorHom
  have hmap : B.map Small.toTensorHom = C :=
    map_comap_eq_self (hCS.trans Small.tensorSylow_coe.le)
  let : IsElementaryAbelian 2 C := hC.2
  let fC : B →* C := Small.toTensorHom.restrict (fun _ hx => hx)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective fC
    (fun x y h => Subtype.ext (Small.toTensorHom_injective (congrArg Subtype.val h)))
  have hr : rank B = rank A := by
    rw [←rank_map_injective Small.toTensorHom Small.toTensorHom_injective B,hmap,rank_map_conj]
  have hc : fixedCodim Small.actionSmall B = fixedCodim action A := by
    rw [fixedCodim_map_equivariant Small.actionSmall action Small.toTensorHom
      (LinearEquiv.refl (ZMod 2) Space) (fun _ _ => rfl) B,hmap,fixedCodim_map_conj]
  have hB := Small.near_offender_right_eq_one B (by rwa [hc,hr])
  intro a ha
  have hca : (MulAut.conj g) a ∈ C := mem_map_of_mem _ ha
  obtain ⟨b,hb,he⟩ := hmap.ge hca
  have hp : tensorParity ((MulAut.conj g) a) = 1 := by
    rw [←he,tensorParity_small]
    exact hB b hb
  apply (tensorParity_eq_one_iff a).mp
  simpa [MulAut.conj_apply,map_mul,map_inv,mul_comm,mul_left_comm,mul_assoc] using hp

end BinaryTensorThree
