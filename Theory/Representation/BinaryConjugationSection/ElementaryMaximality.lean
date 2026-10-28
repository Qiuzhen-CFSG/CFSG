module
public import Theory.Representation.InvertedCubicTensor.CubicPairing
public import Theory.GroupAction.QuotientCommutatorPairing
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Elementary maximality in a central extension of two natural planes

The actual cross commutator descends through the two marked coordinate maps.
Cubic equivariance and a fixed-free central kernel make every nonzero pair
have nonzero commutator. Hence the square-one elements are precisely in the
union of the two elementary factors, and every elementary subgroup belongs
to one of them. Source: Aschbacher--Smith 14.3.18(4), printed p.996.
-/

@[expose] public noncomputable section
open Subgroup InvertedCubicTensor
open scoped IsMulCommutative commutatorElement Pointwise
namespace Representation.BinaryConjugationSection

private theorem descend_pairing
    {A B X Y Z : Type*} [Group A] [Group B] [Group X] [Group Y] [CommGroup Z]
    (a : A →* X) (b : B →* Y) (ha : Function.Surjective a) (hb : Function.Surjective b)
    (f : A →* (B →* Z)) (hka : a.ker≤f.ker) (hkb : ∀x,b.ker≤(f x).ker) :
    ∃k : X →* (Y →* Z),∀x y,k (a x) (b y)=f x y := by
  let g := a.liftOfSurjective ha ⟨f,hka⟩
  have hg (x : A) : g (a x)=f x := by simp [g,MonoidHom.liftOfSurjective]
  have hk (x : X) : b.ker≤(g x).ker := by
    obtain ⟨x,rfl⟩ := ha x
    rw [hg]
    exact hkb x
  let k : X →* (Y →* Z) := {
    toFun x := b.liftOfSurjective hb ⟨g x,hk x⟩
    map_one' := by
      ext y
      obtain ⟨y,rfl⟩ := hb y
      simp [MonoidHom.liftOfSurjective]
    map_mul' x z := by
      ext y
      obtain ⟨y,rfl⟩ := hb y
      simp [MonoidHom.liftOfSurjective] }
  refine ⟨k,?_⟩
  intro x y
  change (b.liftOfSurjective hb ⟨g (a x),hk (a x)⟩) (b y)=f x y
  simp [MonoidHom.liftOfSurjective,hg]

variable {G : Type*} [Group G] {H R V A B : Subgroup G}
  (π : H →* S₃)
  (a : BinaryConjugationSection H A V
    ((BinaryPermutation.coreRepresentation (Fin 3)).comp π))
  (b : BinaryConjugationSection H B V
    ((BinaryPermutation.coreRepresentation (Fin 3)).comp π))

include a b in
/-- A nonzero lift from each marked plane cannot commute in a nonabelian
central extension with cubic-fixed-free kernel. -/
theorem marked_natural_planes_noncommute
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hπ : Function.Surjective π) (hi : A⊓B=V) (hs : A⊔B=R)
    (hc : V≤centralizer (R:Set G)) (hn : ¬IsMulCommutative R)
    (hfree : ∀h:H,π h=cubic→∀v∈V,(h:G)*v*(h:G)⁻¹=v→v=1)
    (x : A) (y : B) (hx : (x:G)∉V) (hy : (y:G)∉V) :
    ¬ Commute (x:G) (y:G) := by
  classical
  let : CommGroup V := IsMulCommutative.instCommGroup
  have hAR : A≤R := hs ▸ le_sup_left
  have hBR : B≤R := hs ▸ le_sup_right
  have hHV : H≤normalizer (V:Set G) := by
    rw [←hi]
    exact (le_inf a.normalized b.normalized).trans inf_normalizer_le_normalizer_inf
  have hAV : A≤centralizer (V:Set G) := by
    intro x hx v hv
    exact (hc hv x (hAR hx)).symm
  have hAB : ⁅A,B⁆≤V := by
    rw [←hi]
    exact le_inf
      (le_normalizer_iff_commutator_le_left.mp (b.section_le.trans a.normalized))
      (le_normalizer_iff_commutator_le_right.mp (a.section_le.trans b.normalized))
  have hVB : ⁅V,B⁆≤⊥ := by
    apply commutator_le.mpr
    intro v hv z hz
    rw [mem_bot,commutatorElement_eq_one_iff_mul_comm]
    exact (hc hv z (hBR hz)).symm
  have hbot : (⊥:Subgroup G).subgroupOf V=(⊥:Subgroup V) := by ext v; simp
  let : ((⊥:Subgroup G).subgroupOf V).Normal := hbot.symm ▸ inferInstance
  let e0 : (V⧸(⊥:Subgroup G).subgroupOf V)≃*V :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  let f : A →* (B →* V) :=
    (centralQuotientCommutatorPairing A B V ⊥ a.kernel_le hAV hAB hVB).compr₂ e0.toMonoidHom
  have hf (x:A) (y:B) : (f x y:G)=⁅(x:G),(y:G)⁆ := by
    dsimp only [f]
    rw [MonoidHom.compr₂_apply,centralQuotientCommutatorPairing_apply]
    rfl
  have hka : a.coordinates.ker≤f.ker := by
    intro x hx
    apply MonoidHom.ext
    intro y
    apply Subtype.ext
    rw [hf]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      ((hc ((a.coordinates_eq_one_iff x).mp hx) y (hBR y.property)).symm)
  have hkb (x:A) : b.coordinates.ker≤(f x).ker := by
    intro y hy
    apply Subtype.ext
    rw [hf]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (hc ((b.coordinates_eq_one_iff y).mp hy) x (hAR x.property))
  obtain ⟨k,hk⟩ := descend_pairing a.coordinates b.coordinates a.onto b.onto f hka hkb
  obtain ⟨h,hh⟩ := hπ cubic
  let α : MulAut V := V.normalizerMonoidHom ⟨h,hHV h.property⟩
  let αA : MulAut A := A.normalizerMonoidHom ⟨h,a.normalized h.property⟩
  let αB : MulAut B := B.normalizerMonoidHom ⟨h,b.normalized h.property⟩
  have hcoordA (z:A) : a.coordinates (αA z)=Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 3) cubic (a.coordinates z).toAdd) := by
    apply Multiplicative.toAdd.injective
    change (a.coordinates ⟨(h:G)*(z:G)*(h:G)⁻¹,_⟩).toAdd = _
    simpa only [MonoidHom.comp_apply,hh,toAdd_ofAdd] using a.equivariant h z
  have hcoordB (z:B) : b.coordinates (αB z)=Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 3) cubic (b.coordinates z).toAdd) := by
    apply Multiplicative.toAdd.injective
    change (b.coordinates ⟨(h:G)*(z:G)*(h:G)⁻¹,_⟩).toAdd = _
    simpa only [MonoidHom.comp_apply,hh,toAdd_ofAdd] using b.equivariant h z
  have hconj (z:A) (w:B) : f (αA z) (αB w)=α (f z w) := by
    apply Subtype.ext
    rw [hf]
    change ⁅(h:G)*(z:G)*(h:G)⁻¹,(h:G)*(w:G)*(h:G)⁻¹⁆=
      (h:G)*(f z w:G)*(h:G)⁻¹
    rw [hf]
    exact (conjugate_commutatorElement (z:G) (w:G) (h:G)).symm
  let β : NaturalPlane→NaturalPlane→Additive V :=
    fun u v=>Additive.ofMul (k (Multiplicative.ofAdd u) (Multiplicative.ofAdd v))
  have heq (u v:NaturalPlane) :
      β (BinaryPermutation.coreRepresentation (Fin 3) cubic u)
        (BinaryPermutation.coreRepresentation (Fin 3) cubic v)=
      Additive.ofMul (α (β u v).toMul) := by
    obtain ⟨z,hz⟩ := a.onto (Multiplicative.ofAdd u)
    obtain ⟨w,hw⟩ := b.onto (Multiplicative.ofAdd v)
    have hz' : a.coordinates (αA z)=Multiplicative.ofAdd
        (BinaryPermutation.coreRepresentation (Fin 3) cubic u) := by rw [hcoordA,hz]; rfl
    have hw' : b.coordinates (αB w)=Multiplicative.ofAdd
        (BinaryPermutation.coreRepresentation (Fin 3) cubic v) := by rw [hcoordB,hw]; rfl
    change Additive.ofMul (k _ _)=Additive.ofMul (α (k _ _))
    rw [←hz',←hw',hk,←hz,←hw,hk,hconj]
  intro hxy
  have hzero : β (a.coordinates x).toAdd (b.coordinates y).toAdd=0 := by
    change k (a.coordinates x) (b.coordinates y)=1
    rw [hk]
    apply Subtype.ext
    rw [hf]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hxy
  have hu : (a.coordinates x).toAdd≠0 := fun he=>hx ((a.coordinates_eq_one_iff x).mp he)
  have hv : (b.coordinates y).toAdd≠0 := fun he=>hy ((b.coordinates_eq_one_iff y).mp he)
  have hall : ∀u v,β u v=0 := natural_cubic_pairing_zero_of_zero β
    (fun z=>Additive.ofMul (α z.toMul))
    (by intros; change k _ _=k _ _*k _ _; rw [ofAdd_add,map_mul]; rfl)
    (by intros; change k _ _=k _ _*k _ _; rw [ofAdd_add,map_mul])
    ⟨by intro z; change k 1 _=1; simp,by intro z; change k _ 1=1; simp⟩
    (show α 1=1 from map_one α)
    (by
      intro z hz
      apply Additive.toMul.injective
      apply Subtype.ext
      exact hfree h hh z.toMul z.toMul.property (congrArg (fun z:Additive V=>(z.toMul:G)) hz))
    heq _ _ hu hv hzero
  have hcomm : A≤centralizer (B:Set G) := by
    intro z hz w hw
    have he := hall (a.coordinates ⟨z,hz⟩).toAdd (b.coordinates ⟨w,hw⟩).toAdd
    change k (a.coordinates ⟨z,hz⟩) (b.coordinates ⟨w,hw⟩)=1 at he
    rw [hk] at he
    have he' := congrArg Subtype.val he
    rw [hf] at he'
    exact (commutatorElement_eq_one_iff_mul_comm.mp he').symm
  apply hn
  rw [←hs]
  apply le_centralizer_iff_isMulCommutative.mp
  apply sup_le
  · exact le_centralizer_iff.mpr (sup_le A.le_centralizer (le_centralizer_iff.mp hcomm))
  · exact le_centralizer_iff.mpr (sup_le hcomm B.le_centralizer)
include a b in
/-- The square-one elements of the actual central product lie in one of its
marked elementary factors. -/
theorem marked_square_one_mem_union
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hπ : Function.Surjective π) (hi : A⊓B=V) (hs : A⊔B=R)
    (hc : V≤centralizer (R:Set G)) (hn : ¬IsMulCommutative R)
    (hfree : ∀h:H,π h=cubic→∀v∈V,(h:G)*v*(h:G)⁻¹=v→v=1)
    (z : G) (hz : z∈R) (hzsq : z^2=1) : z∈A ∨ z∈B := by
  have hABN : A≤normalizer (B:Set G) := a.section_le.trans b.normalized
  rw [←hs,←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right A B hABN] at hz
  obtain ⟨x,hx,y,hy,rfl⟩ := hz
  by_cases hxV : x∈V
  · exact Or.inr (B.mul_mem (b.kernel_le hxV) hy)
  by_cases hyV : y∈V
  · exact Or.inl (A.mul_mem hx (a.kernel_le hyV))
  exfalso
  apply marked_natural_planes_noncommute π a b hπ hi hs hc hn hfree
    ⟨x,hx⟩ ⟨y,hy⟩ hxV hyV
  have hxi : x⁻¹=x := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) x hx)
  have hyi : y⁻¹=y := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) y hy)
  have hxyi : (x*y)⁻¹=x*y := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hzsq)
  rw [mul_inv_rev,hxi,hyi] at hxyi
  exact hxyi.symm

include a b in
/-- Every elementary subgroup of the original group R is contained in one of
the two marked natural-plane factors. -/
theorem marked_elementary_le_factor
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hπ : Function.Surjective π) (hi : A⊓B=V) (hs : A⊔B=R)
    (hc : V≤centralizer (R:Set G)) (hn : ¬IsMulCommutative R)
    (hfree : ∀h:H,π h=cubic→∀v∈V,(h:G)*v*(h:G)⁻¹=v→v=1)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : E≤R) : E≤A ∨ E≤B := by
  apply SubgroupClass.subset_union.mp
  intro z hz
  exact marked_square_one_mem_union π a b hπ hi hs hc hn hfree z (hE hz)
    (elemPow_eq_one_of_isElementaryAbelian (p:=2) z hz)

end Representation.BinaryConjugationSection
