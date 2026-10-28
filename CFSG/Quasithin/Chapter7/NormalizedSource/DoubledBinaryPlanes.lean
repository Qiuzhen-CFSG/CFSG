module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySpans
public import CFSG.Quasithin.Chapter7.Section01To05.FixedSpaceSpan
public import CFSG.Quasithin.ChapterE.Section06.Obstructions

/-!
# Paired-plane reduction for the binary natural–dual orbit

Every five-space contains pure natural and dual vectors of pairing one.
A four-space fixed by a nonidentity automizer also contains such a pair:
outer operators fix at most three dimensions, while a nonidentity inner
operator fixing four dimensions has exactly two fixed dimensions on each
constituent. The annihilator dimension formula gives the required pairing.

A splitting along a vector and the kernel of its dual functional proves
transitivity on all these pairs. Transport through the original component
action therefore reduces their ambient centralizers to one paired plane.
Hyperplanes give r ≥ 2; the exact maximal-obstruction action premise from
E.6.11 then gives r ≥ 3 using E.6.12.

The chosen-module application is in NonFFSourceDoubledBinaryPlanes.
The one-plane centralizer containment and the E.6.11 structural input remain
with the final assembly owner qt-d-1222-nonff-doubled. This module does not
assert the unconditional source 7.7.1 or its 7.7.3 input.
Source: Aschbacher–Smith, H.4.1 and 7.7.1, printed pp.380 and703–704.
-/

public noncomputable section
open Representation Representation.BinaryOffender Subgroup
open BinaryLinearThree BinaryLinearThree.NaturalDual
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlanes

section

private theorem dim_vector : Module.finrank (ZMod 2) Vector = 3 := by
  simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
private theorem dim_space : Module.finrank (ZMod 2) Space = 6 := by
  simp [Space,Module.finrank_prod,BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]

private theorem plane_pair (P : Submodule (ZMod 2) Vector)
    (Q : Submodule (ZMod 2) (Module.Dual (ZMod 2) Vector))
    (hP : 2 ≤ Module.finrank (ZMod 2) P) (hQ : 2 ≤ Module.finrank (ZMod 2) Q) :
    ∃ v ∈ P, ∃ f ∈ Q, f v = 1 := by
  have hn : ¬ Q ≤ P.dualAnnihilator := by
    intro h
    have hle := Submodule.finrank_mono h
    have hsum := Subspace.finrank_add_finrank_dualAnnihilator_eq P
    rw [dim_vector] at hsum
    omega
  obtain ⟨f,hf,hfP⟩ := SetLike.not_le_iff_exists.mp hn
  have hn' : ¬ ∀ v ∈ P, f v = 0 := by
    simpa only [Submodule.mem_dualAnnihilator] using hfP
  push Not at hn'
  obtain ⟨v,hv,hfv⟩ := hn'
  exact ⟨v,hv,f,hf,by
    have ht : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact ht _ hfv⟩

private theorem inl_dimension (U : Submodule (ZMod 2) Space) :
    Module.finrank (ZMod 2) U ≤ 3 +
      Module.finrank (ZMod 2) (U.comap (LinearMap.inl (ZMod 2) Vector _)) := by
  let q := U.mkQ.comp (LinearMap.inl (ZMod 2) Vector (Module.Dual (ZMod 2) Vector))
  have he : q.ker = U.comap (LinearMap.inl (ZMod 2) Vector _) := by
    ext v
    simp [q]
  have hs := q.finrank_range_add_finrank_ker
  have hle := q.range.finrank_le
  rw [he,dim_vector] at hs
  have hdim := U.finrank_quotient_add_finrank
  rw [dim_space] at hdim
  omega

private theorem inr_dimension (U : Submodule (ZMod 2) Space) :
    Module.finrank (ZMod 2) U ≤ 3 +
      Module.finrank (ZMod 2) (U.comap (LinearMap.inr (ZMod 2) Vector _)) := by
  let q := U.mkQ.comp (LinearMap.inr (ZMod 2) Vector (Module.Dual (ZMod 2) Vector))
  have he : q.ker = U.comap (LinearMap.inr (ZMod 2) Vector _) := by
    ext v
    simp [q]
  have hs := q.finrank_range_add_finrank_ker
  have hle := q.range.finrank_le
  rw [he,Subspace.dual_finrank_eq,dim_vector] at hs
  have hdim := U.finrank_quotient_add_finrank
  rw [dim_space] at hdim
  omega

theorem hyperplane_pair (U : Submodule (ZMod 2) Space)
    (hU : 5 ≤ Module.finrank (ZMod 2) U) :
    ∃ v : Vector, ∃ f : Module.Dual (ZMod 2) Vector,
      (v,0) ∈ U ∧ (0,f) ∈ U ∧ f v = 1 := by
  obtain ⟨v,hv,f,hf,hfv⟩ := plane_pair
    (U.comap (LinearMap.inl (ZMod 2) Vector _))
    (U.comap (LinearMap.inr (ZMod 2) Vector _))
    (by have := inl_dimension U; omega) (by have := inr_dimension U; omega)
  exact ⟨v,f,hv,hf,hfv⟩

end

section
private theorem natural_faithful : Function.Injective W := by
  intro g h he
  apply Subtype.ext
  apply Matrix.toLin'.injective
  exact he

private theorem natural_fixed_le_two (g : Group) (hg : g ≠ 1) :
    Module.finrank (ZMod 2) (fixedSpace W (zpowers g)) ≤ 2 := by
  have hn : fixedSpace W (zpowers g) ≠ ⊤ := by
    intro hh
    apply hg
    apply natural_faithful
    apply LinearMap.ext
    intro v
    have hv : v ∈ fixedSpace W (zpowers g) := hh ▸ Submodule.mem_top
    simpa only [map_one, Module.End.one_apply] using (mem_fixedSpace_zpowers_iff W g v).mp hv
  have hlt := Submodule.finrank_lt hn
  rw [dim_vector] at hlt
  omega

private theorem inner_fixed_le_four (g : Group) (hg : g ≠ 1) :
    Module.finrank (ZMod 2) (fixedSpace action (zpowers g)) ≤ 4 := by
  have hn := fixedCodim_add_finrank W (zpowers g)
  have hp := fixedCodim_add_finrank action (zpowers g)
  change fixedCodim (W.prod W.dual) (zpowers g) + _ = _ at hp
  rw [fixedCodim_prod,fixedCodim_zpowers_dual,dim_space] at hp
  rw [dim_vector] at hn
  have hle := natural_fixed_le_two g hg
  omega

private theorem fixed_four_pair (g : Group) (hg : g ≠ 1)
    (U : Submodule (ZMod 2) Space) (hU : 4 ≤ Module.finrank (ZMod 2) U)
    (hfix : ∀ u ∈ U, action g u = u) :
    ∃ v : Vector, ∃ f : Module.Dual (ZMod 2) Vector,
      (v,0) ∈ U ∧ (0,f) ∈ U ∧ f v = 1 := by
  have hle : U ≤ fixedSpace action (zpowers g) := by
    intro u hu
    exact (mem_fixedSpace_zpowers_iff action g u).mpr (hfix u hu)
  have he : U = fixedSpace action (zpowers g) :=
    Submodule.eq_of_le_of_finrank_le hle ((inner_fixed_le_four g hg).trans hU)
  have hdim : Module.finrank (ZMod 2) (fixedSpace action (zpowers g)) = 4 := by
    exact le_antisymm (inner_fixed_le_four g hg) (he ▸ hU)
  have hn := fixedCodim_add_finrank W (zpowers g)
  have hd := fixedCodim_add_finrank W.dual (zpowers g)
  have hp := fixedCodim_add_finrank action (zpowers g)
  change fixedCodim (W.prod W.dual) (zpowers g) + _ = _ at hp
  rw [fixedCodim_prod,fixedCodim_zpowers_dual,hdim,dim_space] at hp
  rw [dim_vector] at hn
  rw [fixedCodim_zpowers_dual,Subspace.dual_finrank_eq,dim_vector] at hd
  obtain ⟨v,hv,f,hf,hfv⟩ := plane_pair (fixedSpace W (zpowers g))
    (fixedSpace W.dual (zpowers g)) (by omega) (by omega)
  refine ⟨v,f,?_,?_,hfv⟩
  · rw [he,mem_fixedSpace_zpowers_iff]
    exact Prod.ext ((mem_fixedSpace_zpowers_iff W g v).mp hv) (map_zero (W.dual g))
  · rw [he,mem_fixedSpace_zpowers_iff]
    exact Prod.ext (map_zero (W g)) ((mem_fixedSpace_zpowers_iff W.dual g f).mp hf)
end

section

private theorem outer_fixed_le_three (α : MulAut Group) (e : Space ≃ₗ[ZMod 2] Space)
    (he : ∀ g x, e (action g x) = action (α g) (e x))
    (hα : α ∉ MulAut.innerSubgroup Group)
    (U : Submodule (ZMod 2) Space) (hfix : ∀ u ∈ U, e u = u) :
    Module.finrank (ZMod 2) U ≤ 3 := by
  have hswap := (outer_swaps α e he hα).2
  have hs (v : U) : v.val.2 = (e (v.val.1,0)).2 := by
    have hh := congrArg Prod.snd (hfix v.val v.property)
    have hadd : v.val = (v.val.1,0) + (0,v.val.2) := by simp
    conv_lhs at hh => rw [hadd,map_add,Prod.snd_add,hswap,add_zero]
    exact hh.symm
  let p : U →ₗ[ZMod 2] Vector := (LinearMap.fst (ZMod 2) Vector _).comp U.subtype
  have hi : Function.Injective p := by
    intro v w hvw
    apply Subtype.ext
    apply Prod.ext hvw
    change v.val.2 = w.val.2
    rw [hs v,hs w]
    change v.val.1 = w.val.1 at hvw
    rw [hvw]
  exact (LinearMap.finrank_le_finrank_of_injective hi).trans_eq dim_vector

theorem large_fixed_pair (α : MulAut Group) (e : Space ≃ₗ[ZMod 2] Space)
    (he : ∀ g x, e (action g x) = action (α g) (e x))
    (hne : e ≠ LinearEquiv.refl _ _)
    (U : Submodule (ZMod 2) Space) (hU : 4 ≤ Module.finrank (ZMod 2) U)
    (hfix : ∀ u ∈ U, e u = u) :
    ∃ v : Vector, ∃ f : Module.Dual (ZMod 2) Vector,
      (v,0) ∈ U ∧ (0,f) ∈ U ∧ f v = 1 := by
  have hα : α ∈ MulAut.innerSubgroup Group := by
    by_contra hh
    have := outer_fixed_le_three α e he hh U hfix
    omega
  obtain ⟨g,rfl⟩ := inner_operator α e he hα
  have hg : g ≠ 1 := by
    rintro rfl
    apply hne
    apply LinearEquiv.ext
    intro x
    change action 1 x = x
    rw [map_one]
    rfl
  exact fixed_four_pair g hg U hU hfix
end

section
/-- The span of a natural vector and a dual vector. Pairing one selects the source planes. -/
def pairedPlane (v : Vector) (f : Module.Dual (ZMod 2) Vector) : Submodule (ZMod 2) Space :=
  Submodule.span (ZMod 2) {(v,0),(0,f)}

theorem pairedPlane_le_iff (v : Vector) (f : Module.Dual (ZMod 2) Vector)
    (U : Submodule (ZMod 2) Space) :
    pairedPlane v f ≤ U ↔ (v,0) ∈ U ∧ (0,f) ∈ U := by
  simp [pairedPlane,Submodule.span_le,Set.insert_subset_iff,Set.singleton_subset_iff]

open CFSG.Quasithin.Chapter7 CFSG.Quasithin.ChapterE
open scoped IsMulCommutative
variable {G : Type*} [_root_.Group G] (W₀ : Subgroup G)
  [IsElementaryAbelian 2 W₀]

private def coordinateSubspace (E : Additive W₀ ≃ₗ[ZMod 2] Space) (U : Subgroup G) :
    Submodule (ZMod 2) Space := ((moduleSubgroup W₀).symm (U.subgroupOf W₀)).map E.toLinearMap

private theorem coordinate_mem (E : Additive W₀ ≃ₗ[ZMod 2] Space) (U : Subgroup G)
    (w : Additive W₀) : E w ∈ coordinateSubspace W₀ E U ↔ (w.toMul : G) ∈ U := by
  rw [coordinateSubspace,Submodule.mem_map_equiv]
  change (E.symm (E w)).toMul ∈ U.subgroupOf W₀ ↔ _
  rw [E.symm_apply_apply]
  rfl

private theorem coordinate_corank [Finite G] (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (U : Subgroup G) (hU : U ≤ W₀) :
    subgroupCorank W₀ U + Module.finrank (ZMod 2) (coordinateSubspace W₀ E U) = 6 := by
  let P := (moduleSubgroup W₀).symm (U.subgroupOf W₀)
  have hP : ambientSubmodule W₀ P = U := by
    change ((moduleSubgroup W₀) ((moduleSubgroup W₀).symm (U.subgroupOf W₀))).map W₀.subtype = U
    rw [OrderIso.apply_symm_apply]
    exact Subgroup.map_subgroupOf_eq_of_le hU
  have he : Module.finrank (ZMod 2) (coordinateSubspace W₀ E U) = Module.finrank (ZMod 2) P :=
    (Submodule.equivMapOfInjective E.toLinearMap E.injective P).finrank_eq.symm
  rw [he,← hP,ambientSubmodule_corank]
  rw [P.finrank_quotient_add_finrank,E.finrank_eq,dim_space]

def ambientPlane (E : Additive W₀ ≃ₗ[ZMod 2] Space) (v : Vector)
    (f : Module.Dual (ZMod 2) Vector) : Subgroup G :=
  ambientSubmodule W₀ ((pairedPlane v f).comap E.toLinearMap)

private theorem ambientPlane_le (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (U : Subgroup G)
    (h : pairedPlane v f ≤ coordinateSubspace W₀ E U) : ambientPlane W₀ E v f ≤ U := by
  rintro x ⟨w,hw,rfl⟩
  exact (coordinate_mem W₀ E U (Additive.ofMul w)).mp (h hw)


/-- The literal ambient plane is generated by the two pure coordinate vectors. -/
theorem ambientPlane_le_iff (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (U : Subgroup G) :
    ambientPlane W₀ E v f ≤ U ↔
      ((E.symm (v,0)).toMul : G) ∈ U ∧ ((E.symm (0,f)).toMul : G) ∈ U := by
  constructor
  · intro h
    constructor
    · apply h
      refine ⟨(E.symm (v,0)).toMul,?_,rfl⟩
      change E (E.symm (v,0)) ∈ pairedPlane v f
      rw [E.apply_symm_apply]
      exact Submodule.subset_span (by simp)
    · apply h
      refine ⟨(E.symm (0,f)).toMul,?_,rfl⟩
      change E (E.symm (0,f)) ∈ pairedPlane v f
      rw [E.apply_symm_apply]
      exact Submodule.subset_span (by simp)
  · rintro ⟨hv,hf⟩
    apply ambientPlane_le W₀ E v f U
    rw [pairedPlane_le_iff]
    constructor
    · have he := (coordinate_mem W₀ E U (E.symm (v,0))).mpr hv
      rwa [E.apply_symm_apply] at he
    · have he := (coordinate_mem W₀ E U (E.symm (0,f))).mpr hf
      rwa [E.apply_symm_apply] at he

/-- The plane lies inside the original orbit subgroup. -/
theorem ambientPlane_le_orbit (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) : ambientPlane W₀ E v f ≤ W₀ :=
  ambientSubmodule_le W₀ _

theorem ambient_hyperplane_pair [Finite G] (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (U : Subgroup G) (hU : U ≤ W₀) (hc : subgroupCorank W₀ U ≤ 1) :
    ∃ v f, f v = 1 ∧ ambientPlane W₀ E v f ≤ U := by
  have hd := coordinate_corank W₀ E U hU
  obtain ⟨v,f,hv,hf,hfv⟩ := hyperplane_pair (coordinateSubspace W₀ E U) (by omega)
  exact ⟨v,f,hfv,ambientPlane_le W₀ E v f U ((pairedPlane_le_iff _ _ _).mpr ⟨hv,hf⟩)⟩

variable (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (a : Automizer W₀ ≃* MulAut Group)
    (hcov : ∀ b g w, E (automizerRepresentation W₀ b (E.symm (action g (E w)))) =
      action (a b g) (E (automizerRepresentation W₀ b w)))

private def coordinateOperator (n : normalizer (W₀ : Set G)) : Space ≃ₗ[ZMod 2] Space :=
  E.symm.trans ((LinearMap.GeneralLinearGroup.toLinearEquiv
    ((automizerRepresentation W₀).asGroupHom (W₀.normalizerMonoidHom.rangeRestrict n))).trans E)

include hcov in
private theorem operator_covariance (n : normalizer (W₀ : Set G)) (g : Group) (x : Space) :
    coordinateOperator W₀ E n (action g x) =
      action (a (W₀.normalizerMonoidHom.rangeRestrict n) g) (coordinateOperator W₀ E n x) := by
  have hh := hcov (W₀.normalizerMonoidHom.rangeRestrict n) g (E.symm x)
  change E (automizerRepresentation W₀ (W₀.normalizerMonoidHom.rangeRestrict n) (E.symm (action g x))) =
    action (a (W₀.normalizerMonoidHom.rangeRestrict n) g)
      (E (automizerRepresentation W₀ (W₀.normalizerMonoidHom.rangeRestrict n) (E.symm x)))
  simpa only [E.apply_symm_apply] using hh

private theorem operator_fixed (n : normalizer (W₀ : Set G)) (U : Subgroup G)
    (hn : (n : G) ∈ centralizer (U : Set G)) :
    ∀ x ∈ coordinateSubspace W₀ E U, coordinateOperator W₀ E n x = x := by
  intro x hx
  obtain ⟨w,rfl⟩ := E.surjective x
  have hw := (coordinate_mem W₀ E U w).mp hx
  change E (automizerRepresentation W₀ (W₀.normalizerMonoidHom.rangeRestrict n)
    (E.symm (E w))) = E w
  rw [E.symm_apply_apply]
  apply congrArg E
  apply Additive.toMul.injective
  apply Subtype.ext
  change (n : G) * (w.toMul : G) * (n : G)⁻¹ = (w.toMul : G)
  rw [← hn _ hw,mul_inv_cancel_right]

include a hcov in
/-- In corank at most two, either a paired plane is present or the full
normalizer has exactly the same pointwise centralizer as for the whole orbit. -/
theorem ambient_four_alternative [Finite G] (U : Subgroup G) (hU : U ≤ W₀)
    (hc : subgroupCorank W₀ U ≤ 2) :
    (∃ v f, f v = 1 ∧ ambientPlane W₀ E v f ≤ U) ∨
      normalizer (W₀ : Set G) ⊓ centralizer (U : Set G) = centralizer (W₀ : Set G) := by
  classical
  by_cases hp : ∃ v f, f v = 1 ∧ ambientPlane W₀ E v f ≤ U
  · exact Or.inl hp
  right
  apply le_antisymm
  · rintro n ⟨hn,hnU⟩
    let n' : normalizer (W₀ : Set G) := ⟨n,hn⟩
    have he : coordinateOperator W₀ E n' = LinearEquiv.refl _ _ := by
      by_contra hne
      have hd := coordinate_corank W₀ E U hU
      obtain ⟨v,f,hv,hf,hfv⟩ := large_fixed_pair _ (coordinateOperator W₀ E n')
        (operator_covariance W₀ E a hcov n') hne (coordinateSubspace W₀ E U)
        (by omega) (operator_fixed W₀ E n' U hnU)
      exact hp ⟨v,f,hfv,ambientPlane_le W₀ E v f U ((pairedPlane_le_iff _ _ _).mpr ⟨hv,hf⟩)⟩
    intro w hw
    have hh := congrArg (fun e : Space ≃ₗ[ZMod 2] Space => e (E (Additive.ofMul ⟨w,hw⟩))) he
    change E (automizerRepresentation W₀ (W₀.normalizerMonoidHom.rangeRestrict n')
      (E.symm (E (Additive.ofMul ⟨w,hw⟩)))) = E (Additive.ofMul ⟨w,hw⟩) at hh
    rw [E.symm_apply_apply] at hh
    have hv := congrArg (fun z : Additive W₀ => (z.toMul : G)) (E.injective hh)
    change n*w*n⁻¹=w at hv
    exact (mul_inv_eq_iff_eq_mul.mp hv).symm
  · exact le_inf (Subgroup.centralizer_le_normalizer _) (centralizer_le hU)
end

section
private def split (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hv : f v = 1) :
    Vector ≃ₗ[ZMod 2] (ZMod 2 × f.ker) where
  toFun x := (f x, ⟨x - f x • v, by simp [hv]⟩)
  invFun p := p.1 • v + p.2.val
  left_inv x := by dsimp; abel
  right_inv p := by
    apply Prod.ext
    · simp [hv]
    · apply Subtype.ext
      simp [hv]
  map_add' x y := by
    apply Prod.ext (f.map_add x y)
    apply Subtype.ext
    change (x+y) - f (x+y) • v = (x-f x • v) + (y-f y • v)
    rw [map_add,add_smul]
    abel
  map_smul' c x := by
    apply Prod.ext (f.map_smul c x)
    apply Subtype.ext
    simp [smul_sub,smul_smul]

private theorem split_self (v : Vector) (f : Module.Dual (ZMod 2) Vector)
    (hv : f v = 1) : split v f hv v = (1,0) := by
  apply Prod.ext hv
  apply Subtype.ext
  simp [split,hv]

/-- SL₃(2) is transitive on the actual vector–functional pairs of pairing one. -/
theorem paired_transitive (v₀ v : Vector) (f₀ f : Module.Dual (ZMod 2) Vector)
    (h₀ : f₀ v₀ = 1) (h : f v = 1) :
    ∃ g : Group, W g v₀ = v ∧ W.dual g f₀ = f := by
  have hn₀ : f₀ ≠ 0 := by intro he; simp [he] at h₀
  have hn : f ≠ 0 := by intro he; simp [he] at h
  have hd₀ := Module.Dual.finrank_ker_add_one_of_ne_zero hn₀
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  let b : f₀.ker ≃ₗ[ZMod 2] f.ker := LinearEquiv.ofFinrankEq _ _ (by omega)
  let e := (split v₀ f₀ h₀).trans
    (((LinearEquiv.refl (ZMod 2) (ZMod 2)).prodCongr b).trans (split v f h).symm)
  have he (x : Vector) : f (e x) = f₀ x := by
    have hh := (split v f h).apply_symm_apply
      (((LinearEquiv.refl (ZMod 2) (ZMod 2)).prodCongr b) (split v₀ f₀ h₀ x))
    exact congrArg Prod.fst hh
  have hev : e v₀ = v := by
    apply (split v f h).injective
    change split v f h ((split v f h).symm
      (((LinearEquiv.refl (ZMod 2) (ZMod 2)).prodCongr b) (split v₀ f₀ h₀ v₀))) = _
    rw [LinearEquiv.apply_symm_apply,split_self,split_self]
    simp
  have hdet : (LinearMap.toMatrix' e.toLinearMap).det = 1 := by
    rw [LinearMap.det_toMatrix']
    exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ e.isUnit_det'.ne_zero
  let g : Group := ⟨LinearMap.toMatrix' e.toLinearMap,hdet⟩
  have hg (x : Vector) : W g x = e x := by
    change Matrix.toLin' (LinearMap.toMatrix' e.toLinearMap) x = e x
    rw [Matrix.toLin'_toMatrix']
    rfl
  refine ⟨g,(hg v₀).trans hev,?_⟩
  apply LinearMap.ext
  intro x
  change f₀ (W g⁻¹ x) = f x
  rw [← he (W g⁻¹ x),← hg,Representation.self_inv_apply]
end

section
open CFSG.Quasithin.Chapter7 CFSG.Quasithin.ChapterE
open scoped IsMulCommutative
variable {G : Type*} [_root_.Group G] (W₀ L : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hLN : L ≤ normalizer (W₀ : Set G))
    (E : Additive W₀ ≃ₗ[ZMod 2] Space) (q : L →* Group)
    (hE : ∀ l w, E (automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) = action (q l) (E w))

include hLN hE in
private theorem map_ambient (l : L) (U : Submodule (ZMod 2) Space) :
    (ambientSubmodule W₀ (U.comap E.toLinearMap)).map (MulAut.conj (l : G)).toMonoidHom =
      ambientSubmodule W₀ ((U.map (action (q l))).comap E.toLinearMap) := by
  let b := W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)
  let ρ := automizerRepresentation W₀
  apply le_antisymm
  · rintro _ ⟨x,⟨w,hw,rfl⟩,rfl⟩
    refine ⟨(ρ b (Additive.ofMul w)).toMul,?_,rfl⟩
    change E (ρ b (Additive.ofMul w)) ∈ U.map (action (q l))
    rw [hE]
    exact Submodule.mem_map_of_mem hw
  · rintro _ ⟨w,hw,rfl⟩
    change E (Additive.ofMul w) ∈ U.map (action (q l)) at hw
    obtain ⟨v,hv,hv'⟩ := hw
    let w₀ := (E.symm v).toMul
    have he : ρ b (Additive.ofMul w₀) = Additive.ofMul w := by
      apply E.injective
      rw [hE]
      change action (q l) (E (E.symm v)) = _
      rw [E.apply_symm_apply]
      exact hv'
    refine ⟨(w₀ : G),⟨w₀,?_,rfl⟩,?_⟩
    · change E (E.symm v) ∈ U
      rwa [E.apply_symm_apply]
    · exact congrArg (fun z : Additive W₀ => (z.toMul : G)) he

private theorem pairedPlane_map (g : Group) (v : Vector) (f : Module.Dual (ZMod 2) Vector) :
    (pairedPlane v f).map (action g) = pairedPlane (W g v) (W.dual g f) := by
  rw [pairedPlane,Submodule.map_span]
  simp only [Set.image_insert_eq,Set.image_singleton]
  change Submodule.span (ZMod 2) {(W g v,W.dual g 0),(W g 0,W.dual g f)} = _
  rw [map_zero,map_zero]
  rfl

include hE in
/-- All paired planes on the original orbit are conjugate by the original component. -/
theorem ambientPlane_transitive (hq : Function.Surjective q)
    (v₀ v : Vector) (f₀ f : Module.Dual (ZMod 2) Vector)
    (h₀ : f₀ v₀ = 1) (h : f v = 1) :
    ∃ l : L, (ambientPlane W₀ E v₀ f₀).map (MulAut.conj (l : G)).toMonoidHom =
      ambientPlane W₀ E v f := by
  obtain ⟨g,hg,hgf⟩ := paired_transitive v₀ v f₀ f h₀ h
  obtain ⟨l,rfl⟩ := hq g
  refine ⟨l,?_⟩
  rw [ambientPlane,map_ambient W₀ L hLN E q hE,pairedPlane_map,hg,hgf]
  rfl
end

section
open CFSG.Quasithin.Chapter7 CFSG.Quasithin.ChapterE
open scoped IsMulCommutative
variable {G : Type*} [_root_.Group G] (W₀ L : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hLN : L ≤ normalizer (W₀ : Set G))
    (E : Additive W₀ ≃ₗ[ZMod 2] Space) (q : L →* Group)
    (hE : ∀ l w, E (automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) = action (q l) (E w))

include hE in
/-- One paired-plane centralizer suffices, with conjugation by the literal component. -/
theorem all_plane_centralizers (hq : Function.Surjective q)
    (v₀ : Vector) (f₀ : Module.Dual (ZMod 2) Vector) (h₀ : f₀ v₀ = 1)
    (hC : centralizer (ambientPlane W₀ E v₀ f₀ : Set G) ≤ normalizer (W₀ : Set G)) :
    ∀ v f, f v = 1 →
      centralizer (ambientPlane W₀ E v f : Set G) ≤ normalizer (W₀ : Set G) := by
  intro v f hfv
  obtain ⟨l,hl⟩ := ambientPlane_transitive W₀ L hLN E q hE hq v₀ v f₀ f h₀ hfv
  let c := MulAut.conj (l : G)
  have hcent : (centralizer (ambientPlane W₀ E v₀ f₀ : Set G)).map c.toMonoidHom =
      centralizer (ambientPlane W₀ E v f : Set G) := by
    rw [← hl]
    apply le_antisymm (Subgroup.map_centralizer_le_centralizer_image _ _)
    intro x hx
    refine ⟨c.symm x,?_,c.apply_symm_apply x⟩
    intro y hy
    apply c.injective
    simpa only [map_mul,c.apply_symm_apply] using hx (c y) (mem_map_of_mem _ hy)
  rw [← hcent]
  apply le_trans (Subgroup.map_mono hC)
  exact (Subgroup.map_le_iff_le_comap).mpr
    (fun n hn => (mem_normalizer_iff.mp
      ((normalizer (W₀ : Set G)).le_normalizer (hLN l.property)) n).mp hn)

variable [Finite G]

/-- Hyperplanes contain a paired plane, so their centralizers are controlled. -/
theorem two_le_globalR_of_planes
    (hC : ∀ v f, f v = 1 →
      centralizer (ambientPlane W₀ E v f : Set G) ≤ normalizer (W₀ : Set G)) :
    2 ≤ globalR W₀ := by
  apply le_iInf
  intro U
  apply le_iInf
  rintro ⟨hU,hn⟩
  by_cases hc : 2 ≤ subgroupCorank W₀ U
  · exact_mod_cast hc
  obtain ⟨v,f,hfv,hp⟩ := ambient_hyperplane_pair W₀ E U hU (by omega)
  exact (hn ((Subgroup.centralizer_le hp).trans (hC v f hfv))).elim
end

section
open CFSG.Quasithin.Chapter7 CFSG.Quasithin.ChapterE
open scoped IsMulCommutative
variable {G : Type*} [_root_.Group G] [Finite G] (W₀ : Subgroup G) [IsElementaryAbelian 2 W₀]
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (a : Automizer W₀ ≃* MulAut Group)
    (hcov : ∀ b g w, E (automizerRepresentation W₀ b (E.symm (action g (E w)))) =
      action (a b g) (E (automizerRepresentation W₀ b w)))

include a hcov in
/-- The paired-plane geometry supplies the full r ≥ 3 reduction. The only
remaining structural premise is the exact maximal-obstruction action in E.6.11. -/
theorem three_le_globalR_of_planes
    {K : CFSG.Quasithin.GroupClass} {T : Sylow 2 G}
    (h61 : Section06.HypothesisE61 K T (normalizer (W₀ : Set G)) W₀)
    (hact : ∀ U ∈ Section06.obstructionFamily (normalizer (W₀ : Set G)) W₀,
      (∀ X : Subgroup G, U < X → X ≤ W₀ → centralizer (X : Set G) ≤ normalizer (W₀ : Set G)) →
      1 < subgroupCorank W₀ U →
      ∃ x ∈ normalizer (W₀ : Set G) ⊓ centralizer (U : Set G), x ∉ centralizer (W₀ : Set G))
    (hC : ∀ v f, f v = 1 →
      centralizer (ambientPlane W₀ E v f : Set G) ≤ normalizer (W₀ : Set G)) :
    3 ≤ globalR W₀ := by
  have hr := two_le_globalR_of_planes W₀ E hC
  apply le_iInf
  intro U
  apply le_iInf
  rintro ⟨hU,hn⟩
  by_cases hc : 3 ≤ subgroupCorank W₀ U
  · exact_mod_cast hc
  obtain ⟨v,f,hfv,hp⟩ | hfix := ambient_four_alternative W₀ E a hcov U hU (by omega)
  · exact (hn ((Subgroup.centralizer_le hp).trans (hC v f hfv))).elim
  · have hUb : U ≠ ⊥ := by
      rintro rfl
      rw [Section06.corank_bot,E.finrank_eq,dim_space] at hc
      omega
    have he : normalizer (W₀ : Set G) ⊓ centralizer (U : Set G) =
        normalizer (W₀ : Set G) ⊓ centralizer (W₀ : Set G) := by
      rwa [inf_eq_right.mpr (Subgroup.centralizer_le_normalizer _)]
    obtain ⟨_,_,_,_,_,heR⟩ := h61.hyperplane_escape_of_maximal_action hact hUb hU he hn
    rw [heR] at hr
    norm_num at hr
end

section
/-- A paired plane is genuinely two-dimensional. -/
theorem pairedPlane_finrank (v : Vector) (f : Module.Dual (ZMod 2) Vector) (h : f v = 1) :
    Module.finrank (ZMod 2) (pairedPlane v f) = 2 := by
  have hv : v ≠ 0 := by intro he; simp [he] at h
  have hf : f ≠ 0 := by intro he; simp [he] at h
  have hnot : (0,f) ∉ Submodule.span (ZMod 2) ({(v,0)} : Set Space) := by
    rintro hh
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hh
    have hh' := congrArg Prod.snd hc
    change c • (0 : Module.Dual (ZMod 2) Vector) = f at hh'
    rw [smul_zero] at hh'
    exact hf hh'.symm
  rw [pairedPlane,Submodule.span_insert,Submodule.finrank_sup_span_singleton hnot,
    finrank_span_singleton (show (v,0) ≠ (0 : Space) from
      fun he => hv (congrArg Prod.fst he))]

open CFSG.Quasithin.Chapter7 CFSG.Quasithin.ChapterE
open scoped IsMulCommutative
variable {G : Type*} [_root_.Group G] [Finite G] (W₀ : Subgroup G) [IsElementaryAbelian 2 W₀]

theorem ambientPlane_rank (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (h : f v = 1) :
    rank (ambientPlane W₀ E v f) = 2 := by
  change Nat.log 2 (Nat.card (ambientPlane W₀ E v f)) = 2
  rw [ambientPlane,ambientSubmodule_log_card,Submodule.comap_equiv_eq_map_symm]
  rw [← (Submodule.equivMapOfInjective E.symm.toLinearMap E.symm.injective
    (pairedPlane v f)).finrank_eq]
  exact pairedPlane_finrank v f h
end

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlanes
