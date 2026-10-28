module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.SextetCentralizer

/-!
# Native kernel shears in the sextet branch

Four explicitly checked elements of the original Mathieu kernel act on every
sextet lift by either fixing an element or multiplying it by the fixed-tetrad
involution. For each element outside the kernel, one of these shears performs
the latter action. The orthogonal kernel E8 has just one 2A involution: the
same tetrad involution. When it belongs to X, its orbit under the whole N(X),
together with identity, is therefore a subgroup. This constructs a nontrivial
pure-2A subgroup normalized by the whole ambient normalizer, directly in the
native model, without an extraspecial-core placement hypothesis.

The source application transports through the literal residual quotient and
its coordinate conjugator. If the original kernel intersection has order at
least eight, the checked upper bound makes it the full E8 and supplies the
tetrad involution. In particular this holds for every sextet lift of order 128.
The exhaustive M22 image split consequently reduces every order-128 zero-form
group containing the original 2B seed to native E/F normalizer coverage or a
strictly smaller pure-2A subgroup with a larger normalizer. The exceptional
image is excluded by its already proved order sixteen. Maximal-TWO-local and
arbitrary-radical applications retain the actual normalizer and core maps.

This proves the indicated sextet subcase of the reducibility step in
Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Proposition 2.2.3,
p.491. Smaller kernel intersections without the tetrad involution, the pure-2A
normalizer classification, and the other source branches remain necessary for
the full four-local cover. The finite action uses the imported native M22
marking and ATLAS kernel coordinates, with their original source attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.SextetShears
open Cardinality QuotientCount.Image KernelCount
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
open LinearFive InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
open M23Geometry FusionCertificate ElementarySylow SextetKernel SextetCentralizer
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel basis

private def action (i : Fin 16) (j : Fin 24) : Fin 24 :=
  StarOrderCertificate.relabel.symm
    (CommonFour.extendPoint (pointTable (candidateIndex 0 i))
      (StarOrderCertificate.relabel j))

private def actionMask (i : Fin 16) (m : ℕ) : ℕ :=
  maskImage (fun j => pairLabel (action i (basisPair j).1) (action i (basisPair j).2)) m

private def shearMask : Fin 4 → ℕ := ![31,32,79,1027]
private def shearChoice : Fin 16 → Fin 4 := ![0,1,0,0,0,0,3,1,2,1,0,0,0,0,2,1]

private theorem shear_cases : ∀ (i : Fin 4) (j : Fin 16),
    actionMask j (shearMask i) = shearMask i ∨
      actionMask j (shearMask i) = Nat.xor (shearMask i) 335 := by decide +kernel

private theorem shear_moves : ∀ j : Fin 16, j ≠ 0 →
    actionMask j (shearMask (shearChoice j)) = Nat.xor (shearMask (shearChoice j)) 335 := by
  decide +kernel

private theorem kernel_action (x : M) (i : Fin 16) (hx : projection x = imageElement i)
    (m : ℕ) : x * kernelValue m * x⁻¹ = kernelValue (actionMask i m) := by
  rw [KernelAction.kernel_conjugation]
  apply congrArg kernelValue
  change maskImage _ m = maskImage _ m
  apply congrArg (fun r : Fin 11 → ℕ => maskImage r m)
  funext j
  rw [KernelAction.star_points x _ hx, KernelAction.star_points x _ hx]
  rfl

private theorem kernel_square (m : ℕ) : kernelValue m * kernelValue m = 1 := by
  rw [← kernelValue_xor]
  change kernelValue (m ^^^ m) = 1
  rw [Nat.xor_self,kernelValue_zero]

private theorem conjugate_of_kernel_action (x : M) (m n : ℕ)
    (h : x * kernelValue m * x⁻¹ = kernelValue (Nat.xor m n)) :
    kernelValue m * x * (kernelValue m)⁻¹ = kernelValue n * x := by
  have hm : (kernelValue m)⁻¹ = kernelValue m := inv_eq_of_mul_eq_one_left (kernel_square m)
  rw [hm]
  have he := congrArg (fun z : M => kernelValue m * z * x) h
  simpa only [kernelValue_xor, mul_assoc, inv_mul_cancel, mul_one,
    ← mul_assoc (kernelValue m) (kernelValue m), kernel_square, one_mul] using he

private theorem conjugation_cases (x : M) (j : Fin 16) (hx : projection x = imageElement j)
    (i : Fin 4) :
    kernelValue (shearMask i) * x * (kernelValue (shearMask i))⁻¹ = x ∨
      kernelValue (shearMask i) * x * (kernelValue (shearMask i))⁻¹ = kernelValue 335 * x := by
  rcases shear_cases i j with h | h
  · left
    have he := kernel_action x j hx (shearMask i)
    rw [h] at he
    rw [← mul_inv_eq_iff_eq_mul.mp he,mul_inv_cancel_right]
  · exact Or.inr (conjugate_of_kernel_action x _ _ (by rw [kernel_action x j hx,h]))

private theorem image_element_of_mem {p : M24} (hp : p ∈ imageGroup) :
    ∃ i : Fin 16, imageElement i = p := by
  obtain ⟨q,⟨i,hi⟩,hqp⟩ := hp
  refine ⟨i,?_⟩
  rw [imageElement,show sylowElement (candidateIndex 0 i) = q from Subtype.ext hi]
  exact hqp

private theorem imageElement_zero : imageElement 0 = 1 := by
  change pointEmbedding (sylowElement 0) = 1
  rw [show sylowElement 0 = 1 from Subtype.ext initial,map_one]

/-- Four explicit native kernel elements normalize any subgroup with sextet
image containing the tetrad involution. -/
private theorem kernel_shears_normalize (X : Subgroup Model) (hXM : X ≤ M)
    (himage : (X.subgroupOf M).map projection ≤ imageGroup)
    (ht : centralInvolution ∈ X) (i : Fin 4) :
    (kernelValue (shearMask i) : Model) ∈ normalizer (X : Set Model) := by
  have forward (x : Model) (hx : x ∈ X) :
      (kernelValue (shearMask i) : Model) * x * (kernelValue (shearMask i) : Model)⁻¹ ∈ X := by
    let x0 : M := ⟨x,hXM hx⟩
    obtain ⟨j,hj⟩ := image_element_of_mem (himage (mem_map_of_mem projection
      (show x0 ∈ X.subgroupOf M from hx)))
    rcases conjugation_cases x0 j hj.symm i with he | he
    · change ((kernelValue (shearMask i) * x0 * (kernelValue (shearMask i))⁻¹ : M) : Model) ∈ X
      rw [he]
      exact hx
    · change ((kernelValue (shearMask i) * x0 * (kernelValue (shearMask i))⁻¹ : M) : Model) ∈ X
      rw [he]
      exact X.mul_mem ht hx
  intro x
  constructor
  · exact forward x
  · intro hx
    have he := forward _ hx
    have hm : (kernelValue (shearMask i) : Model)⁻¹ = kernelValue (shearMask i) :=
      congrArg (fun x : M => (x : Model)) (inv_eq_of_mul_eq_one_left (kernel_square _))
    change x ∈ X
    have hs : (kernelValue (shearMask i) : Model) * kernelValue (shearMask i) = 1 :=
      congrArg (fun x : M => (x : Model)) (kernel_square _)
    have hi : (kernelValue (shearMask i) : Model) *
        ((kernelValue (shearMask i) : Model) * x * (kernelValue (shearMask i) : Model)⁻¹) *
          (kernelValue (shearMask i) : Model)⁻¹ = x := by
      rw [hm]
      calc
        _ = ((kernelValue (shearMask i) : Model) * kernelValue (shearMask i)) * x *
            ((kernelValue (shearMask i) : Model) * kernelValue (shearMask i)) := by
          simp only [mul_assoc]
        _ = x := by rw [hs,one_mul,mul_one]
    rwa [hi] at he

/-- Every element outside the original kernel has the required literal shear. -/
theorem outside_kernel_shear (X : Subgroup Model) (hXM : X ≤ M)
    (himage : (X.subgroupOf M).map projection ≤ imageGroup)
    (ht : centralInvolution ∈ X) (x : Model) (hx : x ∈ X) (hxE : x ∉ E) :
    ∃ g ∈ normalizer (X : Set Model), g * x * g⁻¹ = centralInvolution * x := by
  let x0 : M := ⟨x,hXM hx⟩
  obtain ⟨j,hj⟩ := image_element_of_mem (himage (mem_map_of_mem projection
    (show x0 ∈ X.subgroupOf M from hx)))
  have hj0 : j ≠ 0 := by
    intro he
    have hp : projection x0 = 1 := hj.symm.trans (he ▸ imageElement_zero)
    apply hxE
    exact ⟨x0,by rw [← MathieuHallActors.projection_ker]; change MathieuHallActors.projection x0 = 1; exact hp,rfl⟩
  refine ⟨kernelValue (shearMask (shearChoice j)),kernel_shears_normalize X hXM himage ht _,?_⟩
  exact congrArg (fun y : M => (y : Model)) (conjugate_of_kernel_action x0 _ _
    (by rw [kernel_action x0 j hj.symm,shear_moves j hj0]))

private theorem elementary_square {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (x : V) : x * x = 1 := by
  simpa only [pow_two] using
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) x

private theorem orbit_subgroup_of_shears {H V : Type*} [Group H] [Group V]
    [IsElementaryAbelian 2 V] (ρ : H →* MulAut V) (z : V)
    (hshear : ∀ x : V, (∃ h : H, ρ h z = x) → x ≠ 1 → x ≠ z →
      ∃ h : H, ρ h x = z * x) :
    ∃ W : Subgroup V,
      (∀ x, x ∈ W ↔ x = 1 ∨ ∃ h : H, ρ h z = x) ∧
      ∀ h : H, ∀ x ∈ W, ρ h x ∈ W := by
  let S : Set V := {x | x = 1 ∨ ∃ h : H, ρ h z = x}
  have hmul {x y : V} (hx : x ∈ S) (hy : y ∈ S) : x * y ∈ S := by
    rcases hx with rfl | ⟨g, rfl⟩
    · simpa only [one_mul] using hy
    rcases hy with rfl | ⟨h, rfl⟩
    · exact Or.inr ⟨g, by simp⟩
    by_cases he : ρ g z = ρ h z
    · exact Or.inl (by rw [he, elementary_square])
    let x := ρ g⁻¹ (ρ h z)
    have hxz : x ≠ z := by
      intro hh
      apply he
      have hh' := congrArg (ρ g) hh
      simpa only [x, map_inv, MulAut.apply_inv_self] using hh'.symm
    by_cases hx1 : x = 1
    · have hh := congrArg (ρ g) hx1
      have hy1 : ρ h z = 1 := by
        simpa only [x, map_inv, MulAut.apply_inv_self, map_one] using hh
      exact Or.inr ⟨g, by rw [hy1, mul_one]⟩
    have hxorb : ∃ k : H, ρ k z = x := ⟨g⁻¹ * h, by simp only [x,map_mul,MulAut.mul_apply]⟩
    obtain ⟨k, hk⟩ := hshear x hxorb hx1 hxz
    refine Or.inr ⟨g * k * (g⁻¹ * h), ?_⟩
    calc
      ρ (g * k * (g⁻¹ * h)) z = ρ g (ρ k x) := by
        simp only [x, map_mul, MulAut.mul_apply]
      _ = ρ g (z * x) := congrArg (ρ g) hk
      _ = ρ g z * ρ h z := by
        simp only [map_mul, x, map_inv, MulAut.apply_inv_self]
  let W : Subgroup V :=
    { carrier := S
      one_mem' := Or.inl rfl
      mul_mem' := hmul
      inv_mem' := fun {x} hx => by
        have hi : x⁻¹ = x := inv_eq_of_mul_eq_one_left (elementary_square x)
        rwa [hi] }
  refine ⟨W, fun _ => Iff.rfl, ?_⟩
  intro h x hx
  rcases hx with rfl | ⟨g, rfl⟩
  · exact Or.inl (map_one _)
  · exact Or.inr ⟨h * g, by simp only [map_mul, MulAut.mul_apply]⟩

private theorem pair_not_first (u v : Fin 24) (huv : u ≠ v) :
    ¬ IsConj a (kernelValue (pairLabel u v) : Model) := by
  have hn : kernelValue (pairLabel u v) ≠ 1 := by
    intro he
    exact huv ((pairLabel_eq_zero_iff u v).mp (kernelValue_injective
      (pairLabel_lt u v) (by decide) (he.trans kernelValue_zero.symm)))
  obtain ⟨g,hg | hg⟩ := kernel_nonidentity_orbits matrixA_mul_self matrixB_pow_four
    (kernelValue (pairLabel u v)) (maskValue _ _ _).property hn
  · intro hf
    apply first_not_isConj_second
    apply hf.trans
    exact isConj_iff.mpr ⟨(g : Model),congrArg (fun x : M => (x : Model)) hg.symm⟩
  · have he : kernelValue (pairLabel ((starHom g).val u) ((starHom g).val v)) = kernelValue 3 :=
      (congrArg Subtype.val (starHom_pair g u v)).symm.trans
        (hg.symm.trans (maskValue_three _ _).symm)
    have hl := kernelValue_injective (pairLabel_lt _ _) (by decide) he
    have hh : ∀ i j : Fin 24, pairLabel i j ≠ 3 := by decide +kernel
    exact (hh _ _ hl).elim

/-- The fixed tetrad's even-subset group has exactly one first-class involution. -/
theorem kernelEight_unique_first (x : Model) (hx : x ∈ kernelEight)
    (ha : IsConj a x) : x = centralInvolution := by
  obtain ⟨j,rfl⟩ := hx
  have hj : j = 0 ∨ j = 7 ∨ ∃ u v : Fin 24, u ≠ v ∧ pairLabel u v = goodMask j := by
    have hh : ∀ j : Fin 8, j = 0 ∨ j = 7 ∨
        ∃ u v : Fin 24, u ≠ v ∧ pairLabel u v = goodMask j := by decide +kernel
    exact hh j
  rcases hj with rfl | rfl | ⟨u,v,huv,he⟩
  · have he : (kernelValue (goodMask 0) : Model) = 1 :=
      congrArg (fun x : M => (x : Model)) kernelValue_zero
    change IsConj a (kernelValue (goodMask 0) : Model) at ha
    rw [he] at ha
    have ha1 := isConj_one_left.mp ha
    have ho := orderOf_a
    rw [ha1,orderOf_one] at ho
    contradiction
  · rfl
  · exact (pair_not_first u v huv (he.symm ▸ ha)).elim

/-- The normalizer orbit of the tetrad involution, together with identity,
is a nontrivial pure-2A subgroup. Only the actual kernel shears are used;
extraspecial-core placement is not assumed. -/
theorem pure_reduction (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXM : X ≤ M) (himage : (X.subgroupOf M).map projection ≤ imageGroup)
    (k : Fin 30)
    (hpair : ∀ d : Fin 2, imageElement (nonOctadPair k d) ∈ (X.subgroupOf M).map projection)
    (hzero : intrinsicElementaryForm X = 0) (ht : centralInvolution ∈ X) :
    ∃ Y : Subgroup Model, Y ≠ ⊥ ∧ Y ≤ X ∧ IsElementaryAbelian 2 Y ∧
      normalizer (X : Set Model) ≤ normalizer (Y : Set Model) ∧
      ∀ y ∈ Y, y ≠ 1 → IsConj a y := by
  let z : X := ⟨centralInvolution,ht⟩
  have hs : ∀ x : X, (∃ g : normalizer (X : Set Model), X.normalizerMonoidHom g z = x) →
      x ≠ 1 → x ≠ z → ∃ g : normalizer (X : Set Model),
        X.normalizerMonoidHom g x = z * x := by
    intro x hx _ hxz
    obtain ⟨g,hg⟩ := hx
    have hclass : IsConj a (x : Model) := centralInvolution_first.trans
      (isConj_iff.mpr ⟨g,congrArg Subtype.val hg⟩)
    have hxE : (x : Model) ∉ E := by
      intro he
      exact hxz (Subtype.ext (kernelEight_unique_first _
        (kernel_intersection_le X k hpair hzero ⟨x.property,he⟩) hclass))
    obtain ⟨u,hu,he⟩ := outside_kernel_shear X hXM himage ht x x.property hxE
    exact ⟨⟨u,hu⟩,Subtype.ext he⟩
  obtain ⟨W,hW,hWi⟩ := orbit_subgroup_of_shears X.normalizerMonoidHom z hs
  let Y := W.map X.subtype
  have hzY : centralInvolution ∈ Y :=
    mem_map_of_mem X.subtype ((hW z).mpr (Or.inr ⟨1,by simp⟩))
  have hpure : ∀ y ∈ Y, y ≠ 1 → IsConj a y := by
    rintro y ⟨x,hx,rfl⟩ hx1
    rcases (hW x).mp hx with rfl | ⟨g,hg⟩
    · exact (hx1 rfl).elim
    · exact centralInvolution_first.trans (isConj_iff.mpr ⟨g,congrArg Subtype.val hg⟩)
  have hN : normalizer (X : Set Model) ≤ normalizer (Y : Set Model) := by
    have forward (g : normalizer (X : Set Model)) {x : Model} (hx : x ∈ Y) :
        (g : Model) * x * (g : Model)⁻¹ ∈ Y := by
      obtain ⟨y,hy,rfl⟩ := hx
      exact mem_map_of_mem X.subtype (hWi g y hy)
    intro g hg x
    constructor
    · exact forward ⟨g,hg⟩
    · intro hx
      change x ∈ Y
      have hh := forward (⟨g,hg⟩⁻¹) hx
      simpa only [Subgroup.coe_inv,inv_inv,mul_assoc,inv_mul_cancel_left,
        inv_mul_cancel,mul_one] using hh
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective W.subtype W.subtype_injective
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map X.subtype
  exact ⟨Y,fun he => centralInvolution_ne_one (mem_bot.mp (he ▸ hzY)),
    map_subtype_le _,inferInstance,hN,hpure⟩

/-- A maximal two-local in this native sextet subcase is the whole normalizer
of a pure-2A group, with the original subgroup embedding retained. -/
theorem maximal_pure_reduction (X H : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXM : X ≤ M) (himage : (X.subgroupOf M).map projection ≤ imageGroup)
    (k : Fin 30)
    (hpair : ∀ d : Fin 2, imageElement (nonOctadPair k d) ∈ (X.subgroupOf M).map projection)
    (hzero : intrinsicElementaryForm X = 0) (ht : centralInvolution ∈ X)
    (hH : IsMaximalTwoLocal H) (hHX : H = normalizer (X : Set Model)) :
    ∃ Y : Subgroup Model, Y ≠ ⊥ ∧ Y ≤ X ∧ IsElementaryAbelian 2 Y ∧
      H = normalizer (Y : Set Model) ∧ ∀ y ∈ Y, y ≠ 1 → IsConj a y := by
  obtain ⟨Y,hY,hYX,hYe,hN,hpure⟩ := pure_reduction X hXM himage k hpair hzero ht
  let := hYe
  exact ⟨Y,hY,hYX,hYe,hH.eq_of_le ⟨Y,hY,IsElementaryAbelian.isPGroup 2 Y,rfl⟩
    (hHX ▸ hN),hpure⟩

private theorem conjugate_comp (X : Subgroup Model) (g h : Model) :
    (X.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      X.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem conjugate_one (X : Subgroup Model) :
    X.map (MulAut.conj (1 : Model)).toMonoidHom = X :=
  mem_normalizer_iff_map_conj_eq.mp (normalizer (X : Set Model)).one_mem

/-- The full source E8 kernel forces the marked central involution into X.
The original residual inclusion, quotient and ambient conjugator are retained. -/
theorem sextetLift_normalizer_or_pure_of_full_kernel (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hX : X ≤ residualLift M22ChapterH.Sextet.innerTranslations)
    (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hcard : 8 ≤ Nat.card (X ⊓ embeddedKernel : Subgroup Model)) :
    (∃ g : Model,
      normalizer (X : Set Model) ≤ M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom) ∨
    (∃ Y : Subgroup Model, Y ≠ ⊥ ∧ Y < X ∧ IsElementaryAbelian 2 Y ∧
      normalizer (X : Set Model) ≤ normalizer (Y : Set Model) ∧
      ∀ y ∈ Y, y ≠ 1 → IsConj a y) := by
  obtain ⟨s,hYM,hYi⟩ := sextetLift_coordinates X hX
  let e := MulAut.conj (s : Model)
  let Y := X.map e.toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hzY := intrinsicForm_zero_map X Y e rfl hzero
  have hback : Y.map (MulAut.conj (s : Model)⁻¹).toMonoidHom = X := by
    change (X.map (MulAut.conj (s : Model)).toMonoidHom).map
      (MulAut.conj (s : Model)⁻¹).toMonoidHom = X
    rw [conjugate_comp,inv_mul_cancel,conjugate_one]
  rcases SextetImages.subgroup_octad_or_pair ((Y.subgroupOf M).map projection) hYi with
      ⟨i,hi⟩ | ⟨k,hk⟩
  · obtain ⟨t,ht,ht2,hnt,_⟩ := nonpure_contains_second X hn
    have hntY : ¬ IsConj a (e t) := by
      intro h
      exact hnt (h.trans (isConj_iff.mpr ⟨(s : Model)⁻¹,by simp [e,mul_assoc]⟩))
    obtain ⟨g,hg⟩ := mathieu_octad_image_normalizer_cover Y hYM (SextetImages.octad i) hi
      hzY (e t) (mem_map_of_mem _ ht) ((e.orderOf_eq t).trans ht2) hntY
    left
    refine ⟨(s : Model)⁻¹*g,?_⟩
    have transfer (H : Subgroup Model)
        (h : normalizer (Y : Set Model) ≤ H.map (MulAut.conj g).toMonoidHom) :
        normalizer (X : Set Model) ≤ H.map (MulAut.conj ((s : Model)⁻¹*g)).toMonoidHom := by
      have hm := map_mono (f := (MulAut.conj (s : Model)⁻¹).toMonoidHom) h
      rwa [map_equiv_normalizer_eq,hback,conjugate_comp] at hm
    exact hg.imp (transfer _) (transfer _)
  · have hE : embeddedKernel.map e.toMonoidHom = embeddedKernel := by
      apply mem_normalizer_iff_map_conj_eq.mp
      rw [embedded_localKernel_normalizer_eq_max1]
      exact s.property
    have hi : (X ⊓ embeddedKernel).map e.toMonoidHom = Y ⊓ E := by
      rw [map_inf _ _ _ e.injective,hE]
    have hc : 8 ≤ Nat.card (Y ⊓ E : Subgroup Model) := by
      rw [← hi,card_map_of_injective e.injective]
      exact hcard
    have hker : Y ⊓ E = kernelEight := eq_of_le_of_card_ge
      (kernel_intersection_le Y k hk hzY) (kernelEight_card ▸ hc)
    have htY : centralInvolution ∈ Y := by
      exact ((hker.symm ▸ (show centralInvolution ∈ kernelEight from ⟨7,rfl⟩)) :
        centralInvolution ∈ Y ⊓ E).1
    obtain ⟨Z,hZ,hZY,hZe,hNZ,hpure⟩ := pure_reduction Y hYM hYi k hk hzY htY
    let : IsElementaryAbelian 2 Z := hZe
    let Z0 := Z.map (MulAut.conj (s : Model)⁻¹).toMonoidHom
    have hZ0 : Z0 ≠ ⊥ := by
      intro he
      exact hZ ((map_eq_bot_iff_of_injective _ (MulAut.conj (s : Model)⁻¹).injective).mp he)
    have hZ0X : Z0 ≤ X := hback ▸ map_mono hZY
    have hN : normalizer (X : Set Model) ≤ normalizer (Z0 : Set Model) := by
      have hm := map_mono (f := (MulAut.conj (s : Model)⁻¹).toMonoidHom) hNZ
      rwa [map_equiv_normalizer_eq,map_equiv_normalizer_eq,hback] at hm
    have hp : ∀ z ∈ Z0, z ≠ 1 → IsConj a z := by
      rintro z ⟨u,hu,rfl⟩ hz
      have hu1 : u ≠ 1 := by
        intro he
        apply hz
        rw [he,map_one]
      exact (hpure u hu hu1).trans (isConj_iff.mpr ⟨(s : Model)⁻¹,rfl⟩)
    have hlt : Z0 < X := lt_of_le_of_ne hZ0X (fun he => hn (he ▸ hp))
    exact Or.inr ⟨Z0,hZ0,hlt,IsElementaryAbelian.map _,hN,hp⟩

/-- In particular every source sextet lift of order 128 is now reduced to
native E/F normalizer coverage or a smaller pure-2A whole normalizer. -/
theorem sextetLift_order128_normalizer_or_pure (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hX : X ≤ residualLift M22ChapterH.Sextet.innerTranslations)
    (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x) (hcard : Nat.card X = 128) :
    (∃ g : Model,
      normalizer (X : Set Model) ≤ M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom) ∨
    (∃ Y : Subgroup Model, Y ≠ ⊥ ∧ Y < X ∧ IsElementaryAbelian 2 Y ∧
      normalizer (X : Set Model) ≤ normalizer (Y : Set Model) ∧
      ∀ y ∈ Y, y ≠ 1 → IsConj a y) := by
  apply sextetLift_normalizer_or_pure_of_full_kernel X hX hzero hn
  have hXR : X ≤ residualInclusion.range := hX.trans (map_le_range _ _)
  have hXi : (X.comap residualInclusion).map residualProjection ≤ M22ChapterH.Sextet.innerTranslations := by
    rintro _ ⟨r,hr,rfl⟩
    obtain ⟨q,hq,hqr⟩ := hX hr
    exact residualInclusion_injective hqr ▸ hq
  have hc : Nat.card ((X.comap residualInclusion).map residualProjection) ≤ 16 := by
    have hh := card_le_of_le hXi
    rwa [M22ChapterH.Quintet.innerTranslations_eq_core,M22ChapterH.Quintet.inner_core_card] at hh
  have he := residual_image_card X hXR
  have hbound := Nat.mul_le_mul_right (Nat.card (X ⊓ embeddedKernel : Subgroup Model)) hc
  rw [← he,hcard] at hbound
  omega

/-- The actual arbitrary-radical restriction in the marked sextet subcase,
including equality of the full normalizer and its embedded two-core. -/
theorem radical_pure_local (P X : Subgroup Model) (hP : P.IsPRadical 2)
    [IsElementaryAbelian 2 X] (hXM : X ≤ M)
    (himage : (X.subgroupOf M).map projection ≤ imageGroup) (k : Fin 30)
    (hpair : ∀ d : Fin 2, imageElement (nonOctadPair k d) ∈ (X.subgroupOf M).map projection)
    (hzero : intrinsicElementaryForm X = 0) (ht : centralInvolution ∈ X)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    ∃ Y H : Subgroup Model, Y ≠ ⊥ ∧ IsElementaryAbelian 2 Y ∧ Y ≤ P ∧
      (∀ y ∈ Y, y ≠ 1 → IsConj a y) ∧ H = normalizer (Y : Set Model) ∧ IsTwoLocal H ∧
      normalizer (P : Set Model) ≤ H ∧ P ≤ H ∧
      (normalizer (P.subgroupOf H : Set H)).map H.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf H).IsPRadical 2 ∧
      (normalizer (P.subgroupOf H : Set H)).pCoreIn 2 = P.subgroupOf H ∧
      ((normalizer (P.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = P := by
  obtain ⟨Y,hY,_,hYe,hNY,hpure⟩ := pure_reduction X hXM himage k hpair hzero ht
  let := hYe
  let H := normalizer (Y : Set Model)
  have hNH : normalizer (P : Set Model) ≤ H := hNX.trans hNY
  have hPH := P.le_normalizer.trans hNH
  have hYP : Y ≤ P := le_of_normalizer_le_normalizer_of_pCore_normalizer_le
    P Y hP.isPGroup (IsElementaryAbelian.isPGroup 2 Y) hP.2.le hNH
  have hn := hNH.trans H.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf H hPH hn
  refine ⟨Y,H,hY,hYe,hYP,hpure,rfl,⟨Y,hY,IsElementaryAbelian.isPGroup 2 Y,rfl⟩,
    hNH,hPH,?_,hP.subgroupOf_of_normalizer_normalizes H hPH hn,hcore,?_⟩
  · rw [← subgroupOf_normalizer_eq hPH,map_subgroupOf_eq_of_le hNH]
  · rw [hcore,map_subgroupOf_eq_of_le hPH]

/-- Maximality among two-locals converts the full-kernel sextet reduction
into equality with a native local or with a smaller pure-2A normalizer. -/
theorem maximal_sextetLift_full_kernel (X H : Subgroup Model)
    [IsElementaryAbelian 2 X] (hX : X ≤ residualLift M22ChapterH.Sextet.innerTranslations)
    (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hcard : 8 ≤ Nat.card (X ⊓ embeddedKernel : Subgroup Model))
    (hH : IsMaximalTwoLocal H) (hHX : H = normalizer (X : Set Model)) :
    (∃ g : Model, H = M_F.map (MulAut.conj g).toMonoidHom ∨
      H = max1.map (MulAut.conj g).toMonoidHom) ∨
    (∃ Y : Subgroup Model, Y ≠ ⊥ ∧ Y < X ∧ IsElementaryAbelian 2 Y ∧
      H = normalizer (Y : Set Model) ∧ ∀ y ∈ Y, y ≠ 1 → IsConj a y) := by
  rcases sextetLift_normalizer_or_pure_of_full_kernel X hX hzero hn hcard with
      ⟨g,hg | hg⟩ | ⟨Y,hY,hYX,hYe,hNY,hpure⟩
  · exact Or.inl ⟨g,Or.inl (hH.eq_of_le
      (nativeF_generated_isTwoLocal.map_equiv (MulAut.conj g)) (hHX ▸ hg))⟩
  · exact Or.inl ⟨g,Or.inr (hH.eq_of_le
      (embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj g)) (hHX ▸ hg))⟩
  · let := hYe
    exact Or.inr ⟨Y,hY,hYX,hYe,hH.eq_of_le
      ⟨Y,hY,IsElementaryAbelian.isPGroup 2 Y,rfl⟩ (hHX ▸ hNY),hpure⟩

/-- Full-kernel sextet source application to an arbitrary radical. In the
remaining pure branch the new invariant subgroup lies in the same P; both
literal normalizer and full local core inclusions are preserved. -/
theorem radical_sextetLift_full_kernel (P X : Subgroup Model) (hP : P.IsPRadical 2)
    [IsElementaryAbelian 2 X] (hX : X ≤ residualLift M22ChapterH.Sextet.innerTranslations)
    (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hcard : 8 ≤ Nat.card (X ⊓ embeddedKernel : Subgroup Model))
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    ∃ H : Subgroup Model, IsTwoLocal H ∧
      ((∃ g : Model, H = M_F.map (MulAut.conj g).toMonoidHom ∨
          H = max1.map (MulAut.conj g).toMonoidHom) ∨
        ∃ Y : Subgroup Model, Y ≠ ⊥ ∧ Y < X ∧ IsElementaryAbelian 2 Y ∧ Y ≤ P ∧
          (∀ y ∈ Y, y ≠ 1 → IsConj a y) ∧ H = normalizer (Y : Set Model)) ∧
      normalizer (P : Set Model) ≤ H ∧ P ≤ H ∧
      (normalizer (P.subgroupOf H : Set H)).map H.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf H).IsPRadical 2 ∧
      (normalizer (P.subgroupOf H : Set H)).pCoreIn 2 = P.subgroupOf H ∧
      ((normalizer (P.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = P := by
  obtain ⟨H,hH,hrow,hNH⟩ : ∃ H : Subgroup Model, IsTwoLocal H ∧
      ((∃ g : Model, H = M_F.map (MulAut.conj g).toMonoidHom ∨
          H = max1.map (MulAut.conj g).toMonoidHom) ∨
        ∃ Y : Subgroup Model, Y ≠ ⊥ ∧ Y < X ∧ IsElementaryAbelian 2 Y ∧ Y ≤ P ∧
          (∀ y ∈ Y, y ≠ 1 → IsConj a y) ∧ H = normalizer (Y : Set Model)) ∧
      normalizer (P : Set Model) ≤ H := by
    rcases sextetLift_normalizer_or_pure_of_full_kernel X hX hzero hn hcard with
        ⟨g,hg | hg⟩ | ⟨Y,hY,hYX,hYe,hNY,hpure⟩
    · exact ⟨_,nativeF_generated_isTwoLocal.map_equiv (MulAut.conj g),
        Or.inl ⟨g,Or.inl rfl⟩,hNX.trans hg⟩
    · exact ⟨_,embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj g),
        Or.inl ⟨g,Or.inr rfl⟩,hNX.trans hg⟩
    · let := hYe
      have hNP : normalizer (P : Set Model) ≤ normalizer (Y : Set Model) := hNX.trans hNY
      have hYP : Y ≤ P := le_of_normalizer_le_normalizer_of_pCore_normalizer_le
        P Y hP.isPGroup (IsElementaryAbelian.isPGroup 2 Y) hP.2.le hNP
      exact ⟨_,⟨Y,hY,IsElementaryAbelian.isPGroup 2 Y,rfl⟩,
        Or.inr ⟨Y,hY,hYX,hYe,hYP,hpure,rfl⟩,hNP⟩
  have hPH := P.le_normalizer.trans hNH
  have hN := hNH.trans H.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf H hPH hN
  refine ⟨H,hH,hrow,hNH,hPH,?_,hP.subgroupOf_of_normalizer_normalizes H hPH hN,hcore,?_⟩
  · rw [← subgroupOf_normalizer_eq hPH,map_subgroupOf_eq_of_le hNH]
  · rw [hcore,map_subgroupOf_eq_of_le hPH]

/-- The order-128 sextet branch is stable under every actual ambient
conjugator; the pure subgroup is transported back into the original X. -/
theorem conjugate_sextet_order128 (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (g : Model)
    (hX : X ≤ (residualLift M22ChapterH.Sextet.innerTranslations).map (MulAut.conj g).toMonoidHom)
    (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x) (hcard : Nat.card X = 128) :
    (∃ k : Model,
      normalizer (X : Set Model) ≤ M_F.map (MulAut.conj k).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj k).toMonoidHom) ∨
    (∃ Y : Subgroup Model, Y ≠ ⊥ ∧ Y < X ∧ IsElementaryAbelian 2 Y ∧
      normalizer (X : Set Model) ≤ normalizer (Y : Set Model) ∧
      ∀ y ∈ Y, y ≠ 1 → IsConj a y) := by
  let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hY : Y ≤ residualLift M22ChapterH.Sextet.innerTranslations := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hX
    rwa [conjugate_comp,inv_mul_cancel,conjugate_one] at hh
  have hback : Y.map (MulAut.conj g).toMonoidHom = X := by
    change (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = X
    rw [conjugate_comp,mul_inv_cancel,conjugate_one]
  have hnY : ¬ ∀ y ∈ Y, y ≠ 1 → IsConj a y := by
    intro hp
    apply hn
    intro x hx hx1
    have hy1 : (MulAut.conj g⁻¹) x ≠ 1 := fun he => hx1
      ((MulAut.conj g⁻¹).injective (he.trans (map_one _).symm))
    exact (hp _ (mem_map_of_mem _ hx) hy1).trans
      (isConj_iff.mpr ⟨g,by simp [mul_assoc]⟩)
  have hcY : Nat.card Y = 128 := (card_map_of_injective (MulAut.conj g⁻¹).injective).trans hcard
  rcases sextetLift_order128_normalizer_or_pure Y hY
      (intrinsicForm_zero_map X Y (MulAut.conj g⁻¹) rfl hzero) hnY hcY with
      ⟨k,hk⟩ | ⟨Z,hZ,hZY,hZe,hNZ,hpure⟩
  · left
    refine ⟨g*k,?_⟩
    have transfer (H : Subgroup Model)
        (h : normalizer (Y : Set Model) ≤ H.map (MulAut.conj k).toMonoidHom) :
        normalizer (X : Set Model) ≤ H.map (MulAut.conj (g*k)).toMonoidHom := by
      have hm := map_mono (f := (MulAut.conj g).toMonoidHom) h
      rwa [map_equiv_normalizer_eq,hback,conjugate_comp] at hm
    exact hk.imp (transfer _) (transfer _)
  · let := hZe
    let Z0 := Z.map (MulAut.conj g).toMonoidHom
    have hZ0 : Z0 ≠ ⊥ := fun he => hZ
      ((map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp he)
    have hZ0X : Z0 ≤ X := hback ▸ map_mono hZY.le
    have hp : ∀ z ∈ Z0, z ≠ 1 → IsConj a z := by
      rintro z ⟨u,hu,rfl⟩ hz
      have hu1 : u ≠ 1 := by intro he; apply hz; rw [he,map_one]
      exact (hpure u hu hu1).trans (isConj_iff.mpr ⟨g,rfl⟩)
    have hN : normalizer (X : Set Model) ≤ normalizer (Z0 : Set Model) := by
      have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hNZ
      rwa [map_equiv_normalizer_eq,map_equiv_normalizer_eq,hback] at hm
    exact Or.inr ⟨Z0,hZ0,lt_of_le_of_ne hZ0X (fun he => hn (he ▸ hp)),
      IsElementaryAbelian.map _,hN,hp⟩

/-- The exhaustive M22 image theorem now discharges the sextet branch for
all order-128 zero-form groups with the original second-class seed.
The exceptional image has order sixteen and is therefore impossible here. -/
theorem zero_form_seed_order128_normalizer_or_pure (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hzero : intrinsicElementaryForm X = 0)
    (hseed : (seed : Model) ∈ X) (hcard : Nat.card X = 128) :
    (∃ k : Model,
      normalizer (X : Set Model) ≤ M_F.map (MulAut.conj k).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj k).toMonoidHom) ∨
    (∃ Y : Subgroup Model, Y ≠ ⊥ ∧ Y < X ∧ IsElementaryAbelian 2 Y ∧
      normalizer (X : Set Model) ≤ normalizer (Y : Set Model) ∧
      ∀ y ∈ Y, y ≠ 1 → IsConj a y) := by
  rcases zero_form_seed_normalizer_or_exceptional X hzero hseed with
      h | ⟨n,hn⟩ | ⟨he,_⟩
  · exact Or.inl h
  · have hp : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x := by
      intro hh
      apply first_not_isConj_second
      apply hh _ hseed
      intro he
      have ho := seed_order
      rw [he,orderOf_one] at ho
      contradiction
    exact conjugate_sextet_order128 X (residualInclusion n) hn hzero hp hcard
  · omega

end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.SextetShears
