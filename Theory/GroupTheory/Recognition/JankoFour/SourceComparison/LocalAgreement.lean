module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapAutomorphisms
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.PointFlags

/-!
# Compatible original point and plane isomorphisms

Restrict the separately constructed local isomorphisms to the literal common
intersection. Its proved automorphism factorization expresses their discrepancy
as an inner automorphism and the actual Todd and plane twists. Correcting the
point and plane maps on their original domains makes their restrictions agree.
The plane correction fixes the six-cover pointwise, preserving its explicit
normalizer-conjugated restriction, the cubic scalar and marked involution.
The point correction retains a single explicit M24 quotient conjugator.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.2)–(8.4), pp.606–607.
This constructs the maps and their common-intersection equation. The full
edge-reversal equation and resulting global recognition remain to be proved.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups Sporadic.Mathieu
open scoped Pointwise
variable {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
variable {z : G} {z' : G'} {h : IsTypeJ4 z} {h' : IsTypeJ4 z'}
variable (a : SourceIncidence.LocalData h) (a' : SourceIncidence.LocalData h')

private def overlapPointHom : PlaneOverlap a →* a.P.M where
  toFun x := ⟨x.val.val,x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private noncomputable def restrictPlane (E : centralizer z ≃* centralizer z')
    (hE : (PlaneOverlap a).map E.toMonoidHom=PlaneOverlap a') : PlaneOverlap a ≃* PlaneOverlap a' :=
  ((PlaneOverlap a).equivMapOfInjective E.toMonoidHom E.injective).trans
    (MulEquiv.subgroupCongr hE)

private noncomputable def restrictPoint (E : a.P.M ≃* a'.P.M)
    (hE : (pointOverlap a).map E.toMonoidHom=pointOverlap a') : PlaneOverlap a ≃* PlaneOverlap a' :=
  (overlapPlacement a).symm.trans
    (((pointOverlap a).equivMapOfInjective E.toMonoidHom E.injective).trans
      ((MulEquiv.subgroupCongr hE).trans (overlapPlacement a')))

private theorem involutory_bool_power {J : Type*} [Group J] (x : J) (hx : x^2=1) (b : Bool) :
    x^b.toNat*x^b.toNat=1 := by
  cases b
  · simp only [Bool.toNat_false,pow_zero,one_mul]
  · simpa only [Bool.toNat_true,pow_one,←pow_two] using hx

private theorem factorization_bool (f : MulAut (PlaneOverlap a)) :
    ∃ (x : PlaneOverlap a) (b c : Bool),
      f=MulAut.conj x*planeOverlapToddTwist a (cubicFixedWord a)^b.toNat*
        overlapPlaneTwist a^c.toNat := by
  obtain ⟨x,hx⟩ := overlap_automorphism_factorization a f
  refine ⟨x,?_⟩
  rcases hx with hx | hx | hx | hx
  · exact ⟨false,false,by simpa only [Bool.toNat_false,pow_zero,mul_one] using hx⟩
  · exact ⟨false,true,by simpa only [Bool.toNat_false,Bool.toNat_true,pow_zero,pow_one,mul_one] using hx⟩
  · exact ⟨true,false,by simpa only [Bool.toNat_false,Bool.toNat_true,pow_zero,pow_one,mul_one] using hx⟩
  · exact ⟨true,true,by simpa only [Bool.toNat_true,pow_one] using hx⟩

/-- Correct two local identifications by the actual source twists and one
inner point correction. The new maps agree on the literal ambient overlap. -/
private theorem align_local_equivs
    (H : centralizer z ≃* centralizer z')
    (hH : (PlaneOverlap a).map H.toMonoidHom=PlaneOverlap a')
    (M : a.P.M ≃* a'.P.M)
    (hM : (pointOverlap a).map M.toMonoidHom=pointOverlap a') :
    ∃ (x : PlaneOverlap a) (b c : Bool),
      ∀ i : PlaneOverlap a,
        (M ((MulAut.conj (overlapPointHom a x)*pointTwist a (cubicFixedWord a)^b.toNat)
          (overlapPointHom a i))).val =
        (H (((planeTwist h a.e)^c.toNat) i.val)).val := by
  let u := restrictPlane a a' H hH
  let v := restrictPoint a a' M hM
  let f := u.trans v.symm
  obtain ⟨x,b,c,he⟩ := factorization_bool a f
  let α := overlapPlaneTwist a^c.toNat
  let β := planeOverlapToddTwist a (cubicFixedWord a)^b.toNat
  have hα (i : PlaneOverlap a) : (α i).val=((planeTwist h a.e)^c.toNat) i.val := by
    cases c <;> simp only [α,Bool.toNat_false,Bool.toNat_true,pow_zero,pow_one,
      MulAut.one_apply,overlapPlaneTwist_coe]
  have hβ (i : PlaneOverlap a) : overlapPointHom a (β i)=
      (pointTwist a (cubicFixedWord a)^b.toNat) (overlapPointHom a i) := by
    cases b
    · rfl
    · apply Subtype.ext
      exact planeOverlapToddTwist_coe a (cubicFixedWord a) i
  have hprod (i : PlaneOverlap a) :
      overlapPointHom a ((MulAut.conj x*β) i)=
        (MulAut.conj (overlapPointHom a x)*pointTwist a (cubicFixedWord a)^b.toNat)
          (overlapPointHom a i) := by
    change overlapPointHom a (x*β i*x⁻¹)=_
    rw [map_mul,map_mul,map_inv,hβ]
    rfl
  have hf : f*α=MulAut.conj x*β := by
    rw [he,mul_assoc,show overlapPlaneTwist a^c.toNat*α=1 from
      involutory_bool_power _ (overlapPlaneTwist_sq a) c,mul_one]
  refine ⟨x,b,c,fun i => ?_⟩
  have hv : v (f (α i))=u (α i) := v.apply_symm_apply _
  rw [show f (α i)=(MulAut.conj x*β) i from MulEquiv.congr_fun hf i] at hv
  have hh := congrArg (fun j : PlaneOverlap a' => j.val.val) hv
  change (M (overlapPointHom a ((MulAut.conj x*β) i))).val = (H (α i).val).val at hh
  rwa [hprod,hα] at hh

/-- Construct both local maps and their exact overlap agreement, retaining
the marked center, scalar cubic, and explicit six-cover restriction. -/
theorem exists_compatible_local_equivs (d : CubicNormalizerData a) (d' : CubicNormalizerData a') :
    ∃ (C : cubicCentralizerInH a.e a.X ≃* cubicCentralizerInH a'.e a'.X)
      (n : cubicNormalizerInH a'.e a'.X) (g : M24)
      (φM : a.P.M ≃* a'.P.M) (φH : centralizer z ≃* centralizer z'),
      (∀ c, cubicNativeProjection h' a'.e a'.X (C c)=cubicNativeProjection h a.e a.X c) ∧
      φH planeMarker=planeMarker ∧
      (∀ c : cubicCentralizerInH a.e a.X,
        φH c.val=(cubicNormalizerAction a'.e a'.X n (C c)).val) ∧
      (core z).map φH.toMonoidHom=core z' ∧
      (cubicSylowImage a.e a.X).map φH.toMonoidHom=cubicSylowImage a'.e a'.X ∧
      (∀ m, a'.P.projection (φM m)=g*a.P.projection m*g⁻¹) ∧
      (∀ (k : G) (hkM : k ∈ a.P.M) (hkH : k ∈ centralizer z),
        (φM ⟨k,hkM⟩ : G')=(φH ⟨k,hkH⟩ : G')) := by
  obtain ⟨_,C,n,H,_,_,hC,hz,hHC,_,hA,_,_,hHI,_,_,_⟩ := exists_plane_flag_equiv a a' d d'
  obtain ⟨g₀,M,_,_,hMp,_,hMI,_,_⟩ := exists_point_flag_equiv a a'
  obtain ⟨x,b,c,hagree⟩ := align_local_equivs a a' H hHI M hMI
  let α := (planeTwist h a.e)^c.toNat
  let β := pointTwist a (cubicFixedWord a)^b.toNat
  let φH := α.trans H
  let φM := (MulAut.conj (overlapPointHom a x)*β).trans M
  have hfix (q : cubicCentralizerInH a.e a.X) : α q.val=q.val := by
    cases c
    · rfl
    · exact planeTwist_fixes_cubicCentralizer h a.e a.X q
  have hzα : α planeMarker=planeMarker :=
    hfix ⟨planeMarker,center_le_centralizer _ planeMarker_central⟩
  have hαA : (cubicSylowImage a.e a.X).map α.toMonoidHom=cubicSylowImage a.e a.X := by
    have hf (k) (hk : k ∈ cubicSylowImage a.e a.X) : α k=k :=
      hfix ⟨k,cubicSylowImage_le_centralizer h a.e a.X hk⟩
    ext k
    constructor
    · rintro ⟨y,hy,rfl⟩
      change α y ∈ cubicSylowImage a.e a.X
      rwa [hf y hy]
    · intro hk
      exact ⟨k,hk,hf k hk⟩
  have hφA : (cubicSylowImage a.e a.X).map φH.toMonoidHom=cubicSylowImage a'.e a'.X := by
    change (cubicSylowImage a.e a.X).map (H.toMonoidHom.comp α.toMonoidHom)=_
    rw [←map_map,hαA,hA]
  have hβp (m : a.P.M) : a.P.projection (β m)=a.P.projection m := by
    cases b
    · rfl
    · exact pointTwist_projection a (cubicFixedWord a) m
  refine ⟨C,n,g₀*a.P.projection (overlapPointHom a x),φM,φH,hC,?_,?_,
    planeEquiv_core_map h h' φH,hφA,?_,?_⟩
  · change H (α planeMarker)=planeMarker
    rw [hzα,hz]
  · intro q
    change H (α q.val)=_
    rw [hfix,hHC]
  · intro m
    change a'.P.projection (M ((MulAut.conj (overlapPointHom a x)*β) m))=_
    rw [hMp]
    change g₀*a.P.projection (overlapPointHom a x*β m*(overlapPointHom a x)⁻¹)*g₀⁻¹=_
    rw [map_mul,map_mul,map_inv,hβp]
    group
  · intro k hkM hkH
    exact hagree ⟨⟨k,hkH⟩,hkM⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
