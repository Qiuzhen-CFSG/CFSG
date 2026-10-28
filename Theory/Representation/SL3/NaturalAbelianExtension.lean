module
public import Theory.Representation.SL3OddNaturalNormalizer.Semilinear
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.NoncommRing

/-!
# Abelian natural lifts of a central SL₃ cover

In an exact abelian extension of two natural modules at one marking, a
central covering-kernel element has scalar displacement. Every lift of a
root transvection therefore acts with square one: its scalar square is
detected on a third coordinate fixed by that root. Lifts in one root group
consequently commute.

If a nonidentity central cubic scalar lifts with order three, this excludes
an exponent-four lift whose squaring map identifies its natural layers.
Writing T for the cubic action and U,V for displacements of root parameters
1,a, the map D=V-TU kills the lower layer and has image in that layer.
Thus D²=2D=0. The commuting involutions and T²+T+1=0 imply 2U=0,
contrary to the nontrivial natural action on squares. No elementary
abelianity, splitting, or injectivity of the central cover is assumed.

The intrinsic application is the canonical Ω₂(Z(Q)) obstruction in
Aschbacher–Smith C.1.34, printed pp.136–137. The argument here is elementary
endomorphism algebra and applies independently of the MS hypotheses.
-/

public noncomputable section
open Representation
open scoped MatrixGroups
namespace Representation.NaturalAbelianExtension
private theorem ring_obstruction {B : Type*} [Ring B]
    (T U V : B) (hfour : (4 : B) = 0) (hT : T^2+T+1=0)
    (hU : U^2 = -2*U) (hV : V^2 = -2*V)
    (hTU : Commute T U) (hTV : Commute T V) (hUV : Commute U V)
    (hD : (V-T*U)^2=0) (h2D : 2*(V-T*U)=0) : 2*U=0 := by
  let D := V-T*U
  have hBD : Commute (T*U) D := (hTV.mul_left hUV).sub_right (Commute.refl _)
  have he : V = T*U+D := by dsimp [D]; abel
  have hcross : 2*(T*U)*D=0 := by
    calc
      _ = (T*U)*(2*D) := by noncomm_ring
      _ = 0 := by rw [h2D,mul_zero]
  have hv : V^2 = -2*T^2*U := by
    rw [he,hBD.add_sq,hD,add_zero,hcross,add_zero,hTU.mul_pow,hU]
    noncomm_ring
  have hh : 2*T^2*U = 2*T*U := by
    have hvv := hv.symm.trans hV
    have hvd : 2*V = 2*T*U := by
      exact sub_eq_zero.mp (by simpa only [mul_sub,mul_assoc] using h2D)
    have hh' : -(2*T^2*U) = -(2*V) := by simpa only [neg_mul] using hvv
    exact (neg_injective hh').trans hvd
  have hT' : T^2 = -T-1 := by
    have hh := eq_neg_of_add_eq_zero_left hT
    exact (eq_sub_of_add_eq hh).trans (by abel)
  have ht : 2*T^2*U = -2*T*U-2*U := by rw [hT']; noncomm_ring
  rw [ht] at hh
  have hzero : 4*T*U+2*U=0 := by
    calc
      _ = -((-2*T*U-2*U)-(2*T*U)) := by noncomm_ring
      _ = 0 := by rw [hh,sub_self,neg_zero]
  simpa only [hfour,zero_mul,zero_add] using hzero

variable {X A F : Type*} [Group X] [AddCommGroup A] [Field F]
local notation "W" => (Fin 3 → F)

/-- An exact abelian extension of two copies of the same marked natural module.
No exponent or additive splitting is assumed. -/
structure Data (π : X →* SL(3,F)) (ρ : Representation ℤ X A) where
  incl : W →+ A
  proj : A →+ W
  incl_injective : Function.Injective incl
  proj_surjective : Function.Surjective proj
  exact : ∀ x, proj x = 0 ↔ ∃ v, incl v = x
  incl_equivariant : ∀ g v, ρ g (incl v) = incl (specialLinearNatural 3 (π g) v)
  proj_equivariant : ∀ g x, proj (ρ g x) = specialLinearNatural 3 (π g) (proj x)

variable {π : X →* SL(3,F)} {ρ : Representation ℤ X A} (d : Data π ρ)

private theorem proj_incl (v : W) : d.proj (d.incl v) = 0 :=
  (d.exact _).mpr ⟨v,rfl⟩

/-- Every central element in the covering kernel has scalar displacement
from the top natural layer to the bottom natural layer. -/
theorem kernel_scalar (hπ : Function.Surjective π) (z : X)
    (hz : π z = 1) (hc : ∀ g, Commute (ρ z) (ρ g)) :
    ∃ c : F, ∀ x : A, ρ z x - x = d.incl (c • d.proj x) := by
  have hex (x : A) : ∃ v, d.incl v = ρ z x - x := by
    apply (d.exact _).mp
    rw [map_sub,d.proj_equivariant,hz,map_one,Module.End.one_apply,sub_self]
  choose f hf using hex
  let D : A →+ W := {
    toFun := f
    map_zero' := d.incl_injective (by simp only [hf,map_zero,sub_zero])
    map_add' x y := d.incl_injective (by simp only [hf,map_add]; abel) }
  have hD (x : A) : d.incl (D x) = ρ z x - x := hf x
  have hker : d.proj.ker ≤ D.ker := by
    intro x hx
    obtain ⟨v,rfl⟩ := (d.exact x).mp hx
    apply d.incl_injective
    rw [hD,d.incl_equivariant,hz,map_one,Module.End.one_apply,sub_self,map_zero]
  let δ : W →+ W := d.proj.liftOfSurjective d.proj_surjective ⟨D,hker⟩
  have hδ (x : A) : δ (d.proj x) = D x :=
    d.proj.liftOfRightInverse_comp_apply _ _ _ x
  have hδi (x : A) : d.incl (δ (d.proj x)) = ρ z x - x := by rw [hδ,hD]
  obtain ⟨c,hc⟩ := SL3OddNaturalNormalizer.centralizer_scalar δ (by
    intro g v
    obtain ⟨k,rfl⟩ := hπ g
    obtain ⟨x,rfl⟩ := d.proj_surjective v
    apply d.incl_injective
    rw [←d.proj_equivariant,hδi,←d.incl_equivariant,hδi,map_sub]
    congr 1
    exact LinearMap.congr_fun (hc k).eq x)
  exact ⟨c,fun x => (hδi x).symm.trans (congrArg d.incl (hc _))⟩

variable [CharP F 2]

omit [CharP F 2] in
private theorem root_apply {i j : Fin 3} (hij : i ≠ j) (a : F) (v : W) :
    specialLinearNatural 3 (Matrix.SpecialLinearGroup.transvection hij a) v =
      v + Pi.single i (a*v j) := by
  change ((1 : Matrix (Fin 3) (Fin 3) F) + Matrix.single i j a).mulVec v = _
  simp only [Matrix.add_mulVec,Matrix.one_mulVec,Matrix.single_mulVec_eq]
  congr 1
  funext k
  by_cases hk : k = i <;> simp [hk]

include d in
/-- In an abelian natural self-extension of a central SL₃ cover, every
lift of a root transvection acts with square one. The field-four kernel is retained. -/
theorem root_lift_square (hπ : Function.Surjective π)
    (hcentral : ∀ z, π z=1 → ∀ g, Commute (ρ z) (ρ g))
    {i j : Fin 3} (hij : i ≠ j) (a : F) (g : X)
    (hg : π g = Matrix.SpecialLinearGroup.transvection hij a) :
    ρ g ^ 2 = 1 := by
  have hgg : π (g^2) = 1 := by
    rw [map_pow,hg,pow_two,←Matrix.SpecialLinearGroup.transvection_add]
    have ha : a+a=0 := CharTwo.add_self_eq_zero a
    rw [ha]
    ext u v
    simp
  obtain ⟨c,hc⟩ := kernel_scalar d hπ (g^2) hgg (hcentral (g^2) hgg)
  obtain ⟨k,hki,hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> first | contradiction | decide
  obtain ⟨x,hx⟩ := d.proj_surjective (Pi.single k 1)
  have hδ : d.proj (ρ g x-x) = 0 := by
    rw [map_sub,d.proj_equivariant,hg,root_apply,hx]
    simp [Ne.symm hkj]
  obtain ⟨v,hv⟩ := (d.exact _).mp hδ
  have hv' : ρ g x = d.incl v + x := (eq_sub_iff_add_eq.mp hv).symm
  have he : d.incl (c • Pi.single k 1) =
      d.incl (specialLinearNatural 3 (π g) v + v) := by
    rw [←hx,←hc,map_pow,pow_two,Module.End.mul_apply,hv',map_add,d.incl_equivariant,map_add,hv']
    abel
  have hk := congrFun (d.incl_injective he) k
  rw [hg,root_apply] at hk
  have hc0 : c = 0 := by
    simpa [hki,CharTwo.add_self_eq_zero] using hk
  apply LinearMap.ext
  intro y
  have he := hc y
  rw [hc0,zero_smul,map_zero,sub_eq_zero] at he
  simpa only [map_pow,Module.End.one_apply] using he

include d in
/-- Lifts of two members of one root group commute on the extension. -/
theorem root_lifts_commute (hπ : Function.Surjective π)
    (hcentral : ∀ z, π z=1 → ∀ g, Commute (ρ z) (ρ g))
    {i j : Fin 3} (hij : i ≠ j) (a b : F) (g h : X)
    (hg : π g = Matrix.SpecialLinearGroup.transvection hij a)
    (hh : π h = Matrix.SpecialLinearGroup.transvection hij b) :
    Commute (ρ g) (ρ h) := by
  have hA := root_lift_square d hπ hcentral hij a g hg
  have hB := root_lift_square d hπ hcentral hij b h hh
  have hAB : (ρ g*ρ h)^2=1 := by
    rw [←map_mul]
    apply root_lift_square d hπ hcentral hij (a+b) (g*h)
    rw [map_mul,hg,hh,Matrix.SpecialLinearGroup.transvection_add]
  change ρ g*ρ h=ρ h*ρ g
  calc
    ρ g*ρ h = ρ g*1*ρ h := by rw [mul_one]
    _ = ρ g*((ρ g*ρ h)^2)*ρ h := by rw [hAB]
    _ = (ρ g*ρ g)*ρ h*ρ g*(ρ h*ρ h) := by noncomm_ring
    _ = ρ h*ρ g := by rw [←pow_two,hA,←pow_two,hB,one_mul,mul_one]

include d in
/-- A nontrivial central cubic scalar rules out an exponent-four natural
lift whose squaring map identifies the two natural layers. -/
theorem no_square_extension (hπ : Function.Surjective π)
    (hcentral : ∀ z, π z=1 → ∀ g, Commute (ρ z) (ρ g))
    (hdouble : ∀ x : A, x+x=d.incl (d.proj x))
    (s : X) (hs : ∀ g, Commute (ρ s) (ρ g)) (hs3 : s^3=1)
    (a : F) (ha : a ≠ 1)
    (hscalar : ∀ v : W, specialLinearNatural 3 (π s) v = a • v) : False := by
  let T := ρ s
  have hscalar_fixed (v : W) (hv : a • v=v) : v=0 := by
    have hh : (a-1) • v=0 := by rw [sub_smul,one_smul,hv,sub_self]
    exact (smul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr ha)
  have hfix (x : A) (hx : T x=x) : x=0 := by
    have hqx : d.proj x=0 := hscalar_fixed _ (by
      rw [←hscalar,←d.proj_equivariant]
      exact congrArg d.proj hx)
    obtain ⟨v,rfl⟩ := (d.exact _).mp hqx
    have hv : v=0 := hscalar_fixed v (d.incl_injective (by
      rw [←hscalar,←d.incl_equivariant]
      exact hx))
    rw [hv,map_zero]
  have hT : T^2+T+1=0 := by
    apply LinearMap.ext
    intro x
    change T (T x)+T x+x=0
    apply hfix
    have ht3 : T (T (T x))=x := by
      have he := LinearMap.congr_fun (show T^3=1 from by
        dsimp [T]; rw [←map_pow,hs3,map_one]) x
      simpa only [pow_succ,pow_two,pow_zero,Module.End.mul_apply,mul_one,Module.End.one_apply] using he
    rw [map_add,map_add,ht3]
    abel
  obtain ⟨g,hg⟩ := hπ (Matrix.SpecialLinearGroup.transvection (show (0:Fin 3) ≠ 1 by decide) (1:F))
  obtain ⟨h,hh⟩ := hπ (Matrix.SpecialLinearGroup.transvection (show (0:Fin 3) ≠ 1 by decide) a)
  let U := ρ g-1
  let V := ρ h-1
  let D := V-T*U
  have hTU : Commute T U := by
    apply Commute.sub_right _ (Commute.one_right _)
    exact hs g
  have hTV : Commute T V := by
    apply Commute.sub_right _ (Commute.one_right _)
    exact hs h
  have hUV : Commute U V := by
    apply Commute.sub_right _ (Commute.one_right _)
    apply Commute.sub_left _ (Commute.one_left _)
    exact root_lifts_commute d hπ hcentral (by decide) 1 a g h hg hh
  have hU : U^2 = -2*U := by
    have he := root_lift_square d hπ hcentral (by decide) 1 g hg
    calc
      U^2 = (ρ g)^2-1-2*U := by dsimp [U]; noncomm_ring
      _ = -2*U := by rw [he,sub_self,zero_sub]; noncomm_ring
  have hV : V^2 = -2*V := by
    have he := root_lift_square d hπ hcentral (by decide) a h hh
    calc
      V^2 = (ρ h)^2-1-2*V := by dsimp [V]; noncomm_ring
      _ = -2*V := by rw [he,sub_self,zero_sub]; noncomm_ring
  have hDq (x : A) : d.proj (D x)=0 := by
    change d.proj ((ρ h x-x)-ρ s (ρ g x-x))=0
    rw [map_sub,map_sub,d.proj_equivariant,d.proj_equivariant,
      map_sub,d.proj_equivariant,hscalar,hg,hh,root_apply,root_apply]
    ext k
    by_cases hk : k=0 <;> simp [hk]
  have hDi (v : W) : D (d.incl v)=0 := by
    change (ρ h (d.incl v)-d.incl v)-ρ s (ρ g (d.incl v)-d.incl v)=0
    rw [d.incl_equivariant,d.incl_equivariant,←map_sub,←map_sub,d.incl_equivariant,
      hscalar,←map_sub]
    apply (map_eq_zero_iff d.incl d.incl_injective).mpr
    rw [hg,hh,root_apply,root_apply]
    ext k
    by_cases hk : k=0 <;> simp [hk]
  have hD2 : D^2=0 := by
    apply LinearMap.ext
    intro x
    obtain ⟨v,hv⟩ := (d.exact _).mp (hDq x)
    change D (D x)=0
    rw [←hv,hDi]
  have h2D : 2*D=0 := by
    apply LinearMap.ext
    intro x
    rw [two_mul]
    change D x+D x=0
    rw [hdouble,hDq,map_zero]
  have hfour : (4 : Module.End ℤ A)=0 := by
    have he : (4 : Module.End ℤ A)=(1+1)+(1+1) := by norm_num
    rw [he]
    apply LinearMap.ext
    intro x
    change (x+x)+(x+x)=0
    rw [hdouble,map_add]
    have hz : d.proj x+d.proj x=0 := by ext k; exact CharTwo.add_self_eq_zero _
    rw [hz,map_zero]
  have h2U := ring_obstruction T U V hfour hT hU hV hTU hTV hUV hD2 h2D
  obtain ⟨x,hx⟩ := d.proj_surjective (Pi.single 1 1)
  have hz : d.proj (U x)=0 := by
    apply d.incl_injective
    have he := LinearMap.congr_fun h2U x
    rw [two_mul] at he
    change U x+U x=0 at he
    rw [hdouble] at he
    simpa only [map_zero] using he
  change d.proj (ρ g x-x)=0 at hz
  rw [map_sub,d.proj_equivariant,hg,root_apply,hx] at hz
  have he := congrFun hz 0
  simp at he

end Representation.NaturalAbelianExtension
