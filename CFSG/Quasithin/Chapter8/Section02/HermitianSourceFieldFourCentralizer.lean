module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourLevi
public import Theory.GroupTheory.CComponent.RadicalKernel
public import Theory.GroupTheory.CComponent.SolvableSupplement
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# The field-four centralizer and its normalizer residual

A determinant-one matrix fixing every Hermitian matrix in the upper
two-by-two corner is a norm-one scalar times the plane radical. Thus the
pointwise stabilizer in the faithful Hermitian image is exactly that
radical. On the original action this identifies C_L(U)/C_L(V) as an
elementary abelian group of order sixteen, with both centralizers retained.

C-component minimality makes the original module kernel solvable. The
plane quotient then makes C_L(U) solvable. Combining this kernel bound
with the full SL₂(4) residual image places N_L(U)^∞ as a C-component
in N_{N_G(L)}(U). The companion Chapter 12 module constructs the canonical
subgroup on both weak-closure branches and applies source 1.2.4 in its
full ambient normalizer.

These results do not identify C_{N_L(U)^∞}(U) with O₂(N_L(U)^∞).
That equality, the zero-closure exclusion and the argument through 8.2.13
remain open. No outer involution is identified with a graph automorphism.
Source: Aschbacher--Smith H.4.6(2), 8.2.6 and the following paragraph,
printed pp.382,717, refs/quasithin.pdf (1 March 2004 manuscript).
-/

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Matrix.PSL3Even.UnipotentGeometry
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
public noncomputable section
private abbrev PlaneFixed := fixedSpace (UnipotentRadicals.ambientAction 1) (UnipotentRadicals.plane 1)
private def diag (i : Fin 3) : Space 1 :=
  ⟨Matrix.single i i 1, by ext a b; simp [adjoint,Matrix.single_apply]⟩
private def sym : Space 1 :=
  ⟨Matrix.single 0 1 1 + Matrix.single 1 0 1, by
    ext a b
    simp [adjoint,Matrix.single_apply,add_comm]⟩
private theorem diag_action (A : Mat 1) (i a b : Fin 3) :
    (A * (diag i).val * adjoint 1 A) a b = A a i * sigma 1 (A b i) := by
  simp [diag,Matrix.mul_apply,Matrix.single_apply,adjoint,ite_and]

private theorem fixing_corner_matrix (a : Cover 1)
    (ha : ∀ X : Space 1, X ∈ PlaneFixed → binaryActionHom 1 a X = X) :
    ∃ c : E 1, c ≠ 0 ∧ c ^ 3 = 1 ∧ c * sigma 1 c = 1 ∧
      a.val = !![c,0,a 0 2; 0,c,a 1 2; 0,0,c] := by
  have hd (i : Fin 2) : diag i.castSucc ∈ PlaneFixed := by
    apply (UnipotentRadicals.mem_plane_fixed_iff 1 _).mpr
    fin_cases i <;> simp [diag]
  have he (i : Fin 2) : a.val * (diag i.castSucc).val * adjoint 1 a.val =
      (diag i.castSucc).val := congrArg Subtype.val (ha _ (hd i))
  have off (i : Fin 2) (j : Fin 3) (hji : j ≠ i.castSucc) : a j i.castSucc = 0 := by
    have hh := congrArg (fun X : Mat 1 => X j j) (he i)
    rw [diag_action] at hh
    have hz : a j i.castSucc * sigma 1 (a j i.castSucc) = 0 := by
      simpa [diag,Matrix.single_apply,hji,Ne.symm hji] using hh
    rcases mul_eq_zero.mp hz with hz | hz
    · exact hz
    · exact (sigma 1).injective (hz.trans (map_zero _).symm)
  have h10 : a 1 0 = 0 := off 0 1 (by decide)
  have h20 : a 2 0 = 0 := off 0 2 (by decide)
  have h01 : a 0 1 = 0 := off 1 0 (by decide)
  have h21 : a 2 1 = 0 := off 1 2 (by decide)
  have hn : a 0 0 * sigma 1 (a 0 0) = 1 := by
    have hh := congrArg (fun X : Mat 1 => X 0 0) (he 0)
    rw [diag_action] at hh
    simpa [diag] using hh
  have hsym : sym ∈ PlaneFixed := by
    apply (UnipotentRadicals.mem_plane_fixed_iff 1 _).mpr
    simp [sym]
  have hs : a 1 1 * sigma 1 (a 0 0) = 1 := by
    have hh := congrArg (fun X : Space 1 => X.val 1 0) (ha sym hsym)
    change (a.val * sym.val * adjoint 1 a.val) 1 0 = sym.val 1 0 at hh
    simpa [sym,Matrix.mul_apply,Fin.sum_univ_three,adjoint,Matrix.single_apply,h10] using hh
  have hc : a 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hn
  have h11 : a 1 1 = a 0 0 :=
    mul_right_cancel₀ (right_ne_zero_of_mul_eq_one hn) (hs.trans hn.symm)
  have hp : (a 0 0) ^ 3 = 1 := by
    let : Fintype (E 1) := Fintype.ofFinite _
    have hh := FiniteField.pow_card_sub_one_eq_one (a 0 0) hc
    have hcard : Fintype.card (E 1) = 4 := by rw [← Nat.card_eq_fintype_card,card_E]; norm_num
    simpa only [hcard] using hh
  have h22 : a 2 2 = a 0 0 := by
    have hdet := a.property
    rw [Matrix.det_fin_three,h10,h20,h01,h21,h11] at hdet
    have hh : (a 0 0) ^ 2 * a 2 2 = (a 0 0) ^ 2 * a 0 0 := by
      calc
        (a 0 0) ^ 2 * a 2 2 = (1 : E 1) := by simpa [pow_two] using hdet
        _ = _ := by simpa [pow_succ] using hp.symm
    exact mul_left_cancel₀ (pow_ne_zero _ hc) hh
  refine ⟨a 0 0,hc,hp,hn,?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10,h20,h01,h21,h11,h22]

private theorem fixing_corner_image (a : Cover 1)
    (ha : ∀ X : Space 1, X ∈ PlaneFixed → binaryActionHom 1 a X = X) :
    binaryActionHom 1 a ∈ UnipotentRadicals.plane 1 := by
  obtain ⟨c,hc,hc3,hcn,ha⟩ := fixing_corner_matrix a ha
  let z : U (E 1) := ⟨0,a 1 2 / c,a 0 2 / c⟩
  let s : Cover 1 := ⟨Matrix.scalar (Fin 3) c,by simpa [Matrix.scalar_apply] using hc3⟩
  have hs : binaryActionHom 1 s = 1 := by
    apply (show s ∈ (binaryActionHom 1).ker → _ from id)
    rw [binaryActionHom_ker_eq,mem_actionHom_ker_iff]
    exact ⟨c,rfl,hc3,hcn⟩
  have heq : a = s * specialLinear (E 1) z := by
    apply Subtype.ext
    change a.val = s.val * matrix (E 1) z
    rw [ha]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [s,z,matrix,Matrix.scalar_apply,Matrix.diagonal_mul, hc, mul_div_cancel₀]
  rw [heq,map_mul,hs,one_mul]
  exact mem_map_of_mem (UnipotentRadicals.unipotentHom 1) ((mem_V₂ (E 1) z).mpr rfl)

theorem field_four_plane_pointwise_stabilizer
    (t : Space 1 ≃ₗ[ZMod 2] Space 1) (ht : t ∈ binaryImage 1) :
    (∀ X : Space 1, X ∈ fixedSpace (UnipotentRadicals.ambientAction 1)
      (UnipotentRadicals.plane 1) → t X = X) ↔ t ∈ UnipotentRadicals.plane 1 := by
  constructor
  · obtain ⟨a,rfl⟩ := ht
    exact fixing_corner_image a
  · intro ht X hX
    exact hX ⟨t,ht⟩
open ChapterE
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem component_fixes_subgroup_iff
    (V L U : Subgroup G) [IsElementaryAbelian 2 V]
    (hUV : U ≤ V) (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1) (q : L →* binaryImage 1)
    (he : ∀ (l : L) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v) = (q l).val (e v))
    (l : L) : (l : G) ∈ centralizer (U : Set G) ↔
      ∀ v : Additive V, (v.toMul : G) ∈ U → (q l).val (e v) = e v := by
  constructor
  · intro hc v hv
    rw [←he]
    apply congrArg e
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G) * (v.toMul : G) * (l : G)⁻¹ = (v.toMul : G)
    rw [←hc _ hv,mul_assoc,mul_inv_cancel,mul_one]
  · intro hf u hu
    let v : Additive V := Additive.ofMul ⟨u,hUV hu⟩
    have hv := e.injective ((he l v).trans (hf v hu))
    have hh := congrArg (fun z : Additive V => (z.toMul : G)) hv
    change (l : G) * u * (l : G)⁻¹ = u at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm

omit [Finite G] in
/-- The relative centralizer in the original component has precisely the
plane action on V. Its full kernel is the original centralizer of V. -/
theorem field_four_fixed_centralizer_quotient
    (V L U : Subgroup G) [IsElementaryAbelian 2 V]
    (hUV : U ≤ V) (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (q : L →* binaryImage 1) (hq : Function.Surjective q)
    (he : ∀ (l : L) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v) = (q l).val (e v))
    (hU : ∀ v : Additive V, (v.toMul : G) ∈ U ↔
      e v ∈ fixedSpace (UnipotentRadicals.ambientAction 1) (UnipotentRadicals.plane 1)) :
    let C := L ⊓ centralizer (U : Set G)
    ∃ _hK : ((centralizer (V : Set G)).subgroupOf C).Normal,
      Nonempty ((C ⧸ (centralizer (V : Set G)).subgroupOf C) ≃* UnipotentRadicals.plane 1) ∧
      IsElementaryAbelian 2 (C ⧸ (centralizer (V : Set G)).subgroupOf C) ∧
      Nat.card (C ⧸ (centralizer (V : Set G)).subgroupOf C) = 16 := by
  let C := L ⊓ centralizer (U : Set G)
  have hfix (l : L) : (l : G) ∈ centralizer (U : Set G) ↔
      (q l).val ∈ UnipotentRadicals.plane 1 := by
    rw [field_four_plane_pointwise_stabilizer _ (q l).property |>.symm]
    rw [component_fixes_subgroup_iff V L U hUV hLN e q he l]
    constructor
    · intro hf X hX
      obtain ⟨v,rfl⟩ := e.surjective X
      exact hf v ((hU v).mpr hX)
    · intro hf v hv
      exact hf (e v) ((hU v).mp hv)
  let f : C →* UnipotentRadicals.plane 1 :=
    (((binaryImage 1).subtype.comp q).comp (inclusion (show C ≤ L from inf_le_left))).codRestrict
      _ (fun x => (hfix ⟨x,x.property.1⟩).mp x.property.2)
  have hf : Function.Surjective f := by
    intro t
    have ht : t.val ∈ binaryImage 1 := by
      obtain ⟨z,hz,hzt⟩ := t.property
      exact hzt ▸ ⟨specialLinear (E 1) z,rfl⟩
    obtain ⟨l,hl⟩ := hq ⟨t.val,ht⟩
    have hlC : (l : G) ∈ centralizer (U : Set G) := (hfix l).mpr (by rw [hl]; exact t.property)
    refine ⟨⟨l,l.property,hlC⟩,?_⟩
    apply Subtype.ext
    change (q l).val = t.val
    exact congrArg Subtype.val hl
  have hk : f.ker = (centralizer (V : Set G)).subgroupOf C := by
    ext x
    change f x = 1 ↔ (x : G) ∈ centralizer (V : Set G)
    rw [component_fixes_subgroup_iff V L V le_rfl hLN e q he ⟨x,x.property.1⟩]
    constructor
    · intro hx v _
      have ht : (q ⟨x,x.property.1⟩).val = 1 := congrArg Subtype.val hx
      rw [ht]
      rfl
    · intro hx
      apply Subtype.ext
      apply LinearEquiv.ext
      intro X
      obtain ⟨v,rfl⟩ := e.surjective X
      exact hx v v.toMul.property
  have hK : ((centralizer (V : Set G)).subgroupOf C).Normal := hk ▸ inferInstance
  let := hK
  let a := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  let : IsElementaryAbelian 2 (UnipotentRadicals.plane 1) :=
    IsElementaryAbelian.map (UnipotentRadicals.unipotentHom 1)
  refine ⟨hK,⟨a⟩,IsElementaryAbelian.of_injective a.toMonoidHom a.injective,?_⟩
  rw [Nat.card_congr a.toEquiv]
  change Nat.card ((V₂ (E 1)).map (UnipotentRadicals.unipotentHom 1)) = 16
  rw [Nat.card_congr ((V₂ (E 1)).equivMapOfInjective _
    (UnipotentRadicals.unipotentHom_injective 1)).toEquiv.symm,card_V₂,card_E]
  norm_num

/-- Solvability of the whole component centralizer follows with its original
module kernel retained. -/
theorem field_four_fixed_centralizer_solvable
    (V L U : Subgroup G) [IsElementaryAbelian 2 V]
    (hL : (⊤ : Subgroup L).IsCComponent)
    (hUV : U ≤ V) (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (q : L →* binaryImage 1) (hq : Function.Surjective q)
    (he : ∀ (l : L) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v) = (q l).val (e v))
    (hU : ∀ v : Additive V, (v.toMul : G) ∈ U ↔
      e v ∈ fixedSpace (UnipotentRadicals.ambientAction 1) (UnipotentRadicals.plane 1)) :
    Group.IsSolvable (L ⊓ centralizer (U : Set G) : Subgroup G) := by
  let C := L ⊓ centralizer (U : Set G)
  let K := (centralizer (V : Set G)).subgroupOf C
  have hproper : q.ker ≠ ⊤ := by
    intro htop
    let z : Matrix.PSL3Even.UnipotentGeometry.U (E 1) := ⟨0,1,0⟩
    obtain ⟨l,hl⟩ := hq ⟨UnipotentRadicals.unipotentHom 1 z,
      ⟨specialLinear (E 1) z,rfl⟩⟩
    have hk : q l = 1 := (show l ∈ q.ker from htop.symm ▸ mem_top l)
    have hz : UnipotentRadicals.unipotentHom 1 z = 1 :=
      congrArg Subtype.val (hl.symm.trans hk)
    have hz1 := UnipotentRadicals.unipotentHom_injective 1 (hz.trans (map_one _).symm)
    have h01 := congrArg (fun a : Matrix.PSL3Even.UnipotentGeometry.U (E 1) => a.y) hz1
    exact one_ne_zero h01
  have hker := kernel_le_solvableRadical_of_top_isCComponent hL q hproper
  let : Group.IsSolvable q.ker :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hker)
  let k : K →* q.ker :=
    { toFun := fun x => ⟨⟨x.val.val,x.val.property.1⟩,by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro X
        obtain ⟨v,rfl⟩ := e.surjective X
        exact (component_fixes_subgroup_iff V L V le_rfl hLN e q he
          ⟨x.val.val,x.val.property.1⟩).mp
          (show (x.val : G) ∈ centralizer (V : Set G) from x.property) v v.toMul.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hk : Function.Injective k := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun a : q.ker => ((a : L) : G)) hxy))
  let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective hk
  obtain ⟨hK,_,hE,_⟩ := field_four_fixed_centralizer_quotient V L U hUV hLN e q hq he hU
  let := hK
  let : IsElementaryAbelian 2 (C ⧸ K) := hE
  let : Group.IsSolvable (C ⧸ K) := Group.isSolvable_of_comm (fun a b => mul_comm a b)
  exact Group.isSolvable_of_ker_le_range K.subtype (QuotientGroup.mk' K) (by simp)

/-- The residual of the original component normalizer is a C-component
of that normalizer. Its pointwise kernel is proved solvable. -/
theorem field_four_fixed_normalizer_residual_component
    (V L U : Subgroup G) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 U]
    (hL : (⊤ : Subgroup L).IsCComponent)
    (hUV : U ≤ V) (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (q : L →* binaryImage 1) (hq : Function.Surjective q)
    (he : ∀ (l : L) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v) = (q l).val (e v))
    (hU : ∀ v : Additive V, (v.toMul : G) ∈ U ↔
      e v ∈ fixedSpace (UnipotentRadicals.ambientAction 1) (UnipotentRadicals.plane 1)) :
    (solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).IsCComponent := by
  let H := L ⊓ normalizer (U : Set G)
  let R := solvableResidual H
  let C := L ⊓ centralizer (U : Set G)
  let : Group.IsSolvable C := field_four_fixed_centralizer_solvable V L U hL hUV hLN e q hq he hU
  obtain ⟨_,f,hf,hrange,_⟩ := field_four_fixed_subgroup_sl2_action V L U hUV hLN e q hq he hU
  let a : R →* Automizer U := U.normalizerMonoidHom.rangeRestrict.comp
    ((inclusion (show H ≤ normalizer (U : Set G) from inf_le_right)).comp R.subtype)
  have ha : a.range = f.range := by
    rw [hrange]
    apply le_antisymm
    · rintro _ ⟨x,rfl⟩
      exact mem_map_of_mem U.normalizerMonoidHom.rangeRestrict
        (mem_map_of_mem H.subtype x.property)
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨y,hy,hyx⟩ := hx
      refine ⟨⟨y,hy⟩,?_⟩
      exact congrArg U.normalizerMonoidHom.rangeRestrict (Subtype.ext hyx)
  let k : a.ker →* C :=
    { toFun := fun x => ⟨x.val.val.val,x.val.val.property.1,by
        have hh := x.property
        change (inclusion (show H ≤ normalizer (U : Set G) from inf_le_right)) x.val.val ∈
          U.normalizerMonoidHom.rangeRestrict.ker at hh
        rw [MonoidHom.ker_rangeRestrict,Subgroup.normalizerMonoidHom_ker] at hh
        exact hh⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hk : Function.Injective k := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun x : C => (x : G)) hxy)))
  let : Group.IsSolvable a.ker := Group.isSolvable_of_isSolvable_injective hk
  let : Group.IsSolvable a.rangeRestrict.ker := by rwa [MonoidHom.ker_rangeRestrict]
  let : Group.IsPerfect SL(2,E 1) :=
    ⟨OrthogonalFourMinus.HermitianEquiv.sl2_commutator_eq_top 1⟩
  let : IsQuasisimple SL(2,E 1) :=
    ⟨Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [card_E]; norm_num)⟩
  let : IsQuasisimple a.range := IsQuasisimple.of_mulEquiv
    ((MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr ha.symm))
  have hs : (solvableResidual a.range).IsCComponent := by
    rw [solvableResidual_eq_top]
    exact (show IsComponent a.range ⊤ from
      ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  have hR := residual_isCComponent_of_surjective a.rangeRestrict a.rangeRestrict_surjective hs
  rw [solvableResidual_eq_top] at hR
  have hm := hR.map_subtype (inferInstance : R.Normal).isSubnormal
  simpa only [←MonoidHom.range_eq_map,range_subtype] using hm

/-- The source residual is a C-component in the relative normalizer
N_{N_G(L)}(U), retaining the original ambient embeddings. -/
theorem field_four_fixed_residual_relative_component
    (V L U : Subgroup G) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 U]
    (hL : (⊤ : Subgroup L).IsCComponent)
    (hUV : U ≤ V) (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (q : L →* binaryImage 1) (hq : Function.Surjective q)
    (he : ∀ (l : L) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v) = (q l).val (e v))
    (hU : ∀ v : Additive V, (v.toMul : G) ∈ U ↔
      e v ∈ fixedSpace (UnipotentRadicals.ambientAction 1) (UnipotentRadicals.plane 1)) :
    (((solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).map
      (L ⊓ normalizer (U : Set G)).subtype).subgroupOf
        (normalizer (L : Set G) ⊓ normalizer (U : Set G))).IsCComponent := by
  let H := L ⊓ normalizer (U : Set G)
  let M := normalizer (L : Set G) ⊓ normalizer (U : Set G)
  have hHM : H ≤ M := inf_le_inf_right _ L.le_normalizer
  have hMH : M ≤ normalizer (H : Set G) :=
    (le_inf inf_le_left (inf_le_right.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  let : (H.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hMH
  let eH := (subgroupOfEquivOfLe hHM).symm
  have hR := field_four_fixed_normalizer_residual_component V L U hL hUV hLN e q hq he hU
  have hm := (hR.map_equiv eH).map_subtype (inferInstance : (H.subgroupOf M).Normal).isSubnormal
  have heq : ((solvableResidual H).map eH.toMonoidHom).map (H.subgroupOf M).subtype =
      ((solvableResidual H).map H.subtype).subgroupOf M := by
    ext x
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      exact mem_map_of_mem H.subtype hz
    · rintro ⟨z,hz,hzx⟩
      refine ⟨eH z,mem_map_of_mem eH.toMonoidHom hz,?_⟩
      exact Subtype.ext hzx
  rwa [heq] at hm

end
end CFSG.Quasithin.Chapter8.Section02.HermitianSource
