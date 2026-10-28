module
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus
public import Mathlib.GroupTheory.NoncommCoprod
public import Theory.GroupTheory.SymmetricThreeTwoCore
/-!
# Order-twelve subgroups meeting the binary plus-space factor swap

For a subgroup H of S₃ wr C₂ of order twelve meeting the swapping coset,
the base kernel has order six. Swapping conjugates its two projection images,
so their orders agree; injectivity into their product forces both projections
to be onto S₃. Thus the base kernel is a normal S₃. Since every automorphism
of S₃ is inner and its center is trivial, the actual swapping map splits H
as S₃×C₂. The second coordinate remains the original wreath projection.
Consequently O₂(H) has order two and its nonidentity element swaps factors.

This is precisely the model branch required by Aschbacher–Smith 13.9.8,
printed p.972; no enumeration of subgroup lattices or quotient classifier
is assumed.
-/
public section
open Subgroup
namespace BinaryFourPlus
local notation "S3" => Equiv.Perm (Fin 3)
open Theory.GroupTheory.NormalSymmetricThreePairRank

private noncomputable def s3AutEquiv : S3 ≃* MulAut S3 :=
  MulEquiv.ofBijective MulAut.conj ⟨by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro g hg
    apply mem_bot.mpr
    apply symmetricThree_center_trivial
    intro x
    have hh := DFunLike.congr_fun hg x
    change g*x*g⁻¹ = x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm,
    fun a => by obtain ⟨g,hg⟩ := symmetricThree_aut_inner a; exact ⟨g,hg.symm⟩⟩

private theorem split_s3_kernel {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 12) (f : H →* C2) (e : f.ker ≃* S3) :
    ∃ j : H ≃* (S3 × C2), ∀ h, (j h).2 = f h := by
  let r : H →* S3 := s3AutEquiv.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : H →* MulAut f.ker))
  let j := r.prod f
  have hi : Function.Injective j := by
    apply (injective_iff_map_eq_one j).mpr
    intro h hh
    have hf : f h = 1 := congrArg Prod.snd hh
    have hr : r h = 1 := congrArg Prod.fst hh
    have ha : (MulAut.conjNormal h : MulAut f.ker) = 1 := by
      apply (MulAut.congr e).injective
      apply s3AutEquiv.symm.injective
      simpa only [map_one] using (show s3AutEquiv.symm ((MulAut.congr e) (MulAut.conjNormal h)) = 1 from hr)
    change ((⟨h,hf⟩ : f.ker) : H) = ((1 : f.ker) : H)
    apply congrArg (fun x : f.ker => (x : H))
    apply e.injective
    rw [map_one]
    apply symmetricThree_center_trivial
    intro x
    have hc := DFunLike.congr_fun ha (e.symm x)
    have hd := congrArg Subtype.val hc
    change h*(e.symm x:H)*h⁻¹ = (e.symm x:H) at hd
    have hcomm : e.symm x * (⟨h,hf⟩:f.ker) = ⟨h,hf⟩ * e.symm x :=
      Subtype.ext (mul_inv_eq_iff_eq_mul.mp hd).symm
    simpa only [map_mul,e.apply_symm_apply] using congrArg e hcomm
  have hc : Nat.card H = Nat.card (S3 × C2) := by
    rw [hH,Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial,C2]
  let e' := MulEquiv.ofBijective j ((Nat.bijective_iff_injective_and_card j).mpr ⟨hi,hc⟩)
  exact ⟨e',fun _ => rfl⟩

private theorem range_card_eq_six_of_pair {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 6) (f g : K →* S3)
    (hi : Function.Injective (f.prod g))
    (hc : Nat.card f.range = Nat.card g.range) : Nat.card f.range = 6 := by
  have h6 : Nat.card S3 = 6 := by simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hd : Nat.card f.range ∣ 6 := h6 ▸ f.range.card_subgroup_dvd_card
  let j := f.rangeRestrict.prod g.rangeRestrict
  have hj : Function.Injective j := by
    intro x y h
    apply hi
    exact Prod.ext (congrArg (fun a : f.range × g.range => (a.1:S3)) h)
      (congrArg (fun a : f.range × g.range => (a.2:S3)) h)
  have hdiv := card_dvd_of_injective j hj
  rw [hK,Nat.card_prod,← hc] at hdiv
  have hh := Nat.mem_divisors.mpr ⟨hd,by decide⟩
  have he : (6:ℕ).divisors = {1,2,3,6} := by decide
  rw [he] at hh
  simp only [Finset.mem_insert,Finset.mem_singleton] at hh
  rcases hh with hh | hh | hh | hh <;> simp_all


private def turn : C2 := BinaryFourPlus.swapIndex
private theorem two_coordinates : ∀ i : C2, i = 1 ∨ i = turn := by decide

def parity (H : Subgroup Wreath) : H →* C2 :=
  RegularWreathProduct.rightHom.comp H.subtype

private def baseCoordinate (H : Subgroup Wreath) (i : C2) : (parity H).ker →* S3 where
  toFun x := x.val.val.left i
  map_one' := rfl
  map_mul' x y := by
    have hx : x.val.val.right = 1 := x.property
    simp only [Subgroup.coe_mul,RegularWreathProduct.mul_left,hx,inv_one,one_mul,Pi.mul_apply]

private theorem coordinate_pair_injective (H : Subgroup Wreath) :
    Function.Injective ((baseCoordinate H 1).prod (baseCoordinate H turn)) := by
  intro x y hh
  apply Subtype.ext
  apply Subtype.ext
  apply RegularWreathProduct.ext
  · funext i
    rcases two_coordinates i with rfl | rfl
    · exact congrArg Prod.fst hh
    · exact congrArg Prod.snd hh
  · exact x.property.trans y.property.symm

private theorem conjugation_coordinate (g x : Wreath) (hx : x.right = 1) (i : C2) :
    (g*x*g⁻¹).left i = g.left i * x.left (g.right⁻¹*i) * (g.left i)⁻¹ := by
  simp [RegularWreathProduct.mul_left,RegularWreathProduct.inv_left,hx,mul_assoc]

private theorem coordinate_range_card (H : Subgroup Wreath) (g : H)
    (hg : g.val.right ≠ 1) :
    Nat.card (baseCoordinate H 1).range = Nat.card (baseCoordinate H turn).range := by
  let a : MulAut (parity H).ker := MulAut.conjNormal g
  let c : MulAut S3 := MulAut.conj (g.val.left 1)
  have hg' : g.val.right = turn := (two_coordinates g.val.right).resolve_left hg
  have hcomp : (baseCoordinate H 1).comp a.toMonoidHom =
      c.toMonoidHom.comp (baseCoordinate H turn) := by
    apply MonoidHom.ext
    intro x
    change (g.val*x.val.val*g.val⁻¹).left 1 =
      g.val.left 1 * x.val.val.left turn * (g.val.left 1)⁻¹
    have hx : x.val.val.right = 1 := x.property
    have hh := conjugation_coordinate g.val x.val.val hx 1
    rw [hg'] at hh
    simpa only [turn,swapIndex_inv,one_mul,mul_one] using hh
  have hr : ((baseCoordinate H 1).comp a.toMonoidHom).range =
      (baseCoordinate H 1).range := by
    have ha : a.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr a.surjective
    rw [MonoidHom.range_comp,ha,← MonoidHom.range_eq_map]
  rw [← hr,hcomp,MonoidHom.range_comp,card_map_of_injective c.injective]

/-- The kernel of the swapping coordinate in an order-twelve subgroup
meeting that coset is an actual symmetric-three group. -/
theorem swapping_kernel_model (H : Subgroup Wreath) (hH : Nat.card H = 12)
    (g : H) (hg : g.val.right ≠ 1) :
    Nonempty ((parity H).ker ≃* S3) := by
  have hf : Function.Surjective (parity H) := by
    intro x
    rcases two_coordinates x with rfl | rfl
    · exact ⟨1,map_one _⟩
    · exact ⟨g,(two_coordinates g.val.right).resolve_left hg⟩
  have hK : Nat.card (parity H).ker = 6 := by
    have hh := (parity H).ker.card_mul_index
    rw [index_ker,MonoidHom.range_eq_top.mpr hf,card_top,hH] at hh
    have h2 : Nat.card C2 = 2 := by simp [C2,Nat.card_eq_fintype_card]
    rw [h2] at hh
    omega
  let f := baseCoordinate H 1
  have hF : Nat.card f.range = 6 := range_card_eq_six_of_pair hK f
    (baseCoordinate H turn) (coordinate_pair_injective H) (coordinate_range_card H g hg)
  have h6 : Nat.card S3 = 6 := by simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have htop : f.range = ⊤ := eq_of_le_of_card_ge le_top (by rw [card_top,hF,h6])
  have hfs : Function.Surjective f := MonoidHom.range_eq_top.mp htop
  exact ⟨MulEquiv.ofBijective f (hfs.bijective_of_nat_card_le (by rw [hK,h6]))⟩

/-- Every order-twelve subgroup meeting the swapping coset is S₃×C₂;
the second coordinate is the original wreath swap projection. -/
theorem swapping_twelve_equiv (H : Subgroup Wreath) (hH : Nat.card H = 12)
    (g : H) (hg : g.val.right ≠ 1) :
    ∃ e : H ≃* (S3 × C2), ∀ h : H, (e h).2 = h.val.right := by
  obtain ⟨e⟩ := swapping_kernel_model H hH g hg
  exact split_s3_kernel hH (parity H) e


/-- The actual two-core has order two, and its nonidentity element swaps
the factors in the original wreath coordinates. -/
theorem swapping_twelve_twoCore (H : Subgroup Wreath) (hH : Nat.card H = 12)
    (g : H) (hg : g.val.right ≠ 1) :
    Nat.card (pCore 2 H) = 2 ∧
      ∀ x : H, x ∈ pCore 2 H → x ≠ 1 → x.val.right ≠ 1 := by
  obtain ⟨e,he⟩ := swapping_twelve_equiv H hH g hg
  let f : H →* S3 := (MonoidHom.fst S3 C2).comp e.toMonoidHom
  have hf : Function.Surjective f := fun a => ⟨e.symm (a,1),by simp [f]⟩
  have hc : Nat.card f.ker = 2 := by
    have hh := f.ker.card_mul_index
    rw [index_ker,MonoidHom.range_eq_top.mpr hf,card_top,hH] at hh
    have h6 : Nat.card S3 = 6 := by simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    rw [h6] at hh
    omega
  have hk := ker_eq_twoCore_of_surjective_perm_three f hf
    (IsPGroup.of_card (n := 1) (by simpa using hc))
  refine ⟨hk ▸ hc,?_⟩
  intro x hx hx1 hxright
  apply hx1
  apply e.injective
  rw [map_one]
  apply Prod.ext
  · have hf : x ∈ f.ker := hk.symm ▸ hx
    exact hf
  · exact (he x).trans hxright

end BinaryFourPlus
