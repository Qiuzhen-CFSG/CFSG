module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularAdjacent
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularLinearCommute
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularNextTransforms
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularShortCompletion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.GaussEquations
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.LinearMixedCoefficient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.MixedTorusTable

/-!
# The mixed linear angular equation

The source Frattini support and the rank-one braid relation determine the
parameter-one commutator. Carter coordinate uniqueness removes its endpoint
Omega factor, and conjugating twice by the simple linear involution removes
the remaining Omega factor. Linear torus transport and the Suzuki reflection
then determine both linear coefficients for every field, including q = 2.
The literal native coefficient vector gives the angular equation at (1,7).

Source: Fong--Seitz II (1974), Section 10, (10.18)--(10.22), pp.226--227.
The braid calculation uses the already proved source Gauss equation and avoids
introducing the additional natural section used in the printed argument.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory ReeF4
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition WeylPresentation SignedGeometry
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)
local notation "L" i:max a:max => synchronizedPositivePoint Q split c (Sum.inl i) a
local notation "S" i:max a:max b:max => synchronizedPositivePoint Q split c (Sum.inr i) (a,b)
local notation "W" s:max => (sourceSimpleReflection Q split c s : X ⧸ Q.D)

private theorem batch_pair_reflection (s : Bool) (i : Fin 4)
    (h : (step false s (true,i)).1 = true) (a : CoefficientField m) :
    MulAut.conj (W s) (L i a) = L (next false s i) a := by
  have hh := signedWordPoint_reflection (synchronizedWeylPoint Q split c) false s (true,i)
    (synchronizedLinearChart Q split c (.ofAdd a) : X ⧸ Q.D)
    (synchronizedLinear_perpendicularReflection Q split c a)
  rw [show step false s (true,i) = (true,next false s i) from Prod.ext h rfl] at hh
  simpa only [signedWordPoint,signedRootWord, Bool.false_eq_true,
    Bool.true_eq_false, ↓reduceIte,mul_one,synchronizedWeylPoint_simple,
    ←synchronizedPositivePoint_pair_word,MulAut.conj_apply] using hh

private theorem batch_quartet_reflection (s : Bool) (i : Fin 4)
    (h : (step true s (true,i)).1 = true) (a b : CoefficientField m) :
    MulAut.conj (W s) (S i a b) = S (next true s i) a b := by
  have hh := signedWordPoint_reflection (synchronizedWeylPoint Q split c) true s (true,i)
    (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)
    (synchronizedSuzuki_perpendicularReflection Q split c a b)
  rw [show step true s (true,i) = (true,next true s i) from Prod.ext h rfl] at hh
  simpa only [signedWordPoint,signedRootWord,↓reduceIte,mul_one,synchronizedWeylPoint_simple,
    ←synchronizedPositivePoint_quartet_word,MulAut.conj_apply] using hh

private theorem omega_point_mem (i : Fin 4) (b : CoefficientField m) :
    synchronizedPositivePoint Q split c (.inr i) (0,b) ∈
      omegaOneAmbient (positiveRoot Q split (.inr i)) := by
  apply (omegaOneAmbient_le_iff _ _).mp le_rfl _
    (synchronizedPositiveChart Q split c (.inr i) (0,b)).property
  change synchronizedPositivePoint Q split c (.inr i) (0,b) ^ 2 = 1
  rw [pow_two,synchronizedPositivePoint_quartet_mul]
  simpa only [zero_add,map_zero,zero_mul,add_zero,CharTwo.add_self_eq_zero] using
    synchronizedPositivePoint_quartet_zero Q split c i

private def omegaChartHom (i : Fin 4) : Multiplicative (CoefficientField m) →*
    omegaOneAmbient (positiveRoot Q split (.inr i)) where
  toFun a := ⟨synchronizedPositivePoint Q split c (.inr i) (0,a.toAdd),omega_point_mem Q split c i _⟩
  map_one' := Subtype.ext (synchronizedPositivePoint_quartet_zero Q split c i)
  map_mul' a b := by
    apply Subtype.ext
    change synchronizedPositivePoint Q split c (.inr i) (0,a.toAdd+b.toAdd) =
      synchronizedPositivePoint Q split c (.inr i) (0,a.toAdd) *
      synchronizedPositivePoint Q split c (.inr i) (0,b.toAdd)
    symm
    simpa only [zero_add,map_zero,zero_mul,add_zero] using
      synchronizedPositivePoint_quartet_mul Q split c i 0 a.toAdd 0 b.toAdd

private theorem omegaChartHom_bijective (i : Fin 4) : Function.Bijective (omegaChartHom Q split c i) := by
  apply Function.Injective.bijective_of_nat_card_le
  · intro a b h
    have hv : synchronizedPositivePoint Q split c (.inr i) (0,a.toAdd) =
        synchronizedPositivePoint Q split c (.inr i) (0,b.toAdd) :=
      congrArg (fun z : omegaOneAmbient (positiveRoot Q split (.inr i)) => (z : X ⧸ Q.D)) h
    have h' := (synchronizedPositiveChart Q split c (.inr i)).injective (Subtype.ext hv)
    exact Multiplicative.toAdd.injective (congrArg Prod.snd h')
  · rw [omega_positiveRoot_card Q split c i,
      Nat.card_congr Multiplicative.toAdd,GaloisField.card 2 (2*m+1) (by omega)]


private theorem point_simple_linear (a : CoefficientField m) :
    L 0 a = (synchronizedLinearChart Q split c (.ofAdd a) : X ⧸ Q.D) := by
  rw [synchronizedPositivePoint_pair_word]
  simp only [positiveWord,Matrix.cons_val_zero,map_one,inv_one,one_mul,mul_one]

private theorem pair_inv (i : Fin 4) (a : CoefficientField m) : (L i a)⁻¹ = L i a := by
  apply inv_eq_of_mul_eq_one_right
  rw [synchronizedPositivePoint_pair_mul]
  simp only [CharTwo.add_self_eq_zero,synchronizedPositivePoint_pair_zero]

private theorem linear_braid :
    W false * L 0 1 * W false = L 0 1 * W false * L 0 1 := by
  have hw : W false * W false = 1 := linearReflection_sq Q split c
  have hwi : (W false)⁻¹ = W false := inv_eq_of_mul_eq_one_right hw
  have hx : L 0 1 * L 0 1 = 1 := by
    rw [synchronizedPositivePoint_pair_mul]
    simp only [CharTwo.add_self_eq_zero,synchronizedPositivePoint_pair_zero]
  have h := synchronizedLinear_gauss Q split c (1 : (CoefficientField m)ˣ)
  simp only [Units.val_one,inv_one,map_one,mul_one] at h
  rw [←point_simple_linear Q split c] at h
  change W false * (W false * L 0 1 * (W false)⁻¹) =
    (W false * L 0 1 * (W false)⁻¹) * L 0 1 at h
  rw [hwi] at h
  have hh : L 0 1 * W false = W false * L 0 1 * W false * L 0 1 := by
    simpa only [←mul_assoc,hw,one_mul] using h
  calc
    _ = (W false * L 0 1 * W false * L 0 1) * L 0 1 := by
      rw [mul_assoc (W false * L 0 1 * W false),hx,mul_one]
    _ = _ := by rw [←hh]

private theorem fixed_of_braid {G : Type*} [Group G] {w x y z : G}
    (hb : w*x*w = x*w*x) (hy : w*z*w⁻¹ = y) (hxz : x*z*x⁻¹ = z) :
    w*(x*y*x⁻¹)*w⁻¹ = x*y*x⁻¹ := by
  calc
    _ = (w*x*w)*z*(w*x*w)⁻¹ := by rw [←hy]; group
    _ = (x*w*x)*z*(x*w*x)⁻¹ := by rw [hb]
    _ = x*(w*(x*z*x⁻¹)*w⁻¹)*x⁻¹ := by group
    _ = _ := by rw [hxz,hy]

private theorem field_support (a b : CoefficientField m) :
    ∃ p q r s t : CoefficientField m,
      S 3 0 p * L 3 q * S 1 0 r * L 2 s * S 2 0 t =
        (L 1 b)⁻¹ * (L 0 a)⁻¹ * L 1 b * L 0 a := by
  obtain ⟨p,q,r,s,t,h⟩ := synchronized_mixedPhi_decomposition Q split c a b
  obtain ⟨p,rfl⟩ := (omegaChartHom_bijective Q split c 3).surjective p
  obtain ⟨q,rfl⟩ := (synchronizedPositiveChart Q split c (.inl 3)).surjective q
  obtain ⟨r,rfl⟩ := (omegaChartHom_bijective Q split c 1).surjective r
  obtain ⟨s,rfl⟩ := (synchronizedPositiveChart Q split c (.inl 2)).surjective s
  obtain ⟨t,rfl⟩ := (omegaChartHom_bijective Q split c 2).surjective t
  exact ⟨p.toAdd,q,r.toAdd,s,t.toAdd,h⟩

private theorem omega_inv (i : Fin 4) (a : CoefficientField m) : (S i 0 a)⁻¹ = S i 0 a := by
  apply inv_eq_of_mul_eq_one_right
  rw [synchronizedPositivePoint_quartet_mul]
  simp only [CharTwo.add_self_eq_zero,map_zero,zero_mul,synchronizedPositivePoint_quartet_zero]

private theorem carter_unique
    (a b d e f g h a' b' d' e' f' g' h' : CoefficientField m)
    (he : S 2 0 a * L 2 b * S 1 0 d * L 3 e * S 3 0 f * L 1 g * S 0 0 h =
      S 2 0 a' * L 2 b' * S 1 0 d' * L 3 e' * S 3 0 f' * L 1 g' * S 0 0 h') :
    a = a' ∧ b = b' ∧ d = d' ∧ e = e' ∧ f = f' ∧ g = g' ∧ h = h' := by
  have hh := linearProduct_injective Q split c
    (a₁ := (synchronizedPositiveChart Q split c (.inr 2) (0,a),
      synchronizedPositiveChart Q split c (.inl 2) b,
      synchronizedPositiveChart Q split c (.inr 1) (0,d),
      synchronizedPositiveChart Q split c (.inl 3) e,
      synchronizedPositiveChart Q split c (.inr 3) (0,f),
      synchronizedPositiveChart Q split c (.inl 1) g,
      synchronizedPositiveChart Q split c (.inr 0) (0,h),PUnit.unit))
    (a₂ := (synchronizedPositiveChart Q split c (.inr 2) (0,a'),
      synchronizedPositiveChart Q split c (.inl 2) b',
      synchronizedPositiveChart Q split c (.inr 1) (0,d'),
      synchronizedPositiveChart Q split c (.inl 3) e',
      synchronizedPositiveChart Q split c (.inr 3) (0,f'),
      synchronizedPositiveChart Q split c (.inl 1) g',
      synchronizedPositiveChart Q split c (.inr 0) (0,h'),PUnit.unit)) (by
        simpa only [linearFactors,rootProduct,synchronizedPositivePoint,mul_one,mul_assoc] using he)
  exact ⟨congrArg Prod.snd ((synchronizedPositiveChart Q split c (.inr 2)).injective
      (congrArg (fun z => z.1) hh)),
    (synchronizedPositiveChart Q split c (.inl 2)).injective (congrArg (fun z => z.2.1) hh),
    congrArg Prod.snd ((synchronizedPositiveChart Q split c (.inr 1)).injective
      (congrArg (fun z => z.2.2.1) hh)),
    (synchronizedPositiveChart Q split c (.inl 3)).injective (congrArg (fun z => z.2.2.2.1) hh),
    congrArg Prod.snd ((synchronizedPositiveChart Q split c (.inr 3)).injective
      (congrArg (fun z => z.2.2.2.2.1) hh)),
    (synchronizedPositiveChart Q split c (.inl 1)).injective (congrArg (fun z => z.2.2.2.2.2.1) hh),
    congrArg Prod.snd ((synchronizedPositiveChart Q split c (.inr 0)).injective
      (congrArg (fun z => z.2.2.2.2.2.2.1) hh))⟩

private theorem phi_word_inv (p q r s t : CoefficientField m) :
    (S 3 0 p * L 3 q * S 1 0 r * L 2 s * S 2 0 t)⁻¹ =
      S 3 0 p * L 3 q * S 1 0 r * L 2 s * S 2 0 t := by
  let : IsElementaryAbelian 2 (phi (simpleRemainder Q split 1)) :=
    phiRemainder_elementary Q split (pinnedInput Q split c)
  apply inv_eq_of_mul_eq_one_right
  have hm : S 3 0 p * L 3 q * S 1 0 r * L 2 s * S 2 0 t ∈
      phi (simpleRemainder Q split 1) := by
    rw [←SetLike.mem_coe, ←phiProduct_range Q split c]
    refine ⟨(omegaChartHom Q split c 3 (.ofAdd p),
      synchronizedPositiveChart Q split c (.inl 3) q,
      omegaChartHom Q split c 1 (.ofAdd r),
      synchronizedPositiveChart Q split c (.inl 2) s,
      omegaChartHom Q split c 2 (.ofAdd t),PUnit.unit),?_⟩
    simp only [phiFactors,rootProduct,mul_one,mul_assoc]
    rfl
  simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hm

private theorem commute_of_conj {G : Type*} [Group G] {a b : G}
    (h : a*b*a⁻¹ = b) : Commute a b := by
  have hh := congrArg (fun z => z*a) h
  simpa only [Commute,SemiconjBy,mul_assoc,inv_mul_cancel,mul_one] using hh

private theorem omega_linear_commute (a b : CoefficientField m) :
    Commute (S 3 0 a) (L 2 b) ∧ Commute (L 1 b) (S 1 0 a) := by
  constructor
  · apply commute_of_conj
    simpa only [zero_mul,synchronizedPositivePoint_quartet_zero,one_mul] using
      synchronized_short_shifted_conjugate Q split c 0 a b
  · apply commute_of_conj
    simpa only [zero_mul,synchronizedPositivePoint_quartet_zero,one_mul] using
      synchronized_short_perpendicular_conjugate Q split c 0 a b

private theorem omega_next_reorder (t b : CoefficientField m) :
    S 0 0 t * L 2 b = L 2 b * S 3 0 (t*b) * S 0 0 t := by
  have h := synchronized_next_conjugate Q split c 0 t b
  simp only [map_zero,zero_mul,add_zero,synchronizedPositivePoint_pair_zero,
    synchronizedPositivePoint_quartet_zero,mul_one] at h
  have hh := congrArg (fun z => z * S 0 0 t) h
  simpa only [mul_assoc,inv_mul_cancel,mul_one,
    (omega_linear_commute Q split c (t*b) b).1.eq] using hh

private theorem seed_support (b : CoefficientField m) :
    ∃ p q : CoefficientField m,
      L 0 1 * L 1 b * (L 0 1)⁻¹ =
        S 3 0 p * L 3 q * S 1 0 p * L 2 b * L 1 b := by
  obtain ⟨p,q,r,s,t,hk⟩ := field_support Q split c 1 b
  have hki := phi_word_inv Q split c p q r s t
  have hreverse : S 3 0 p * L 3 q * S 1 0 r * L 2 s * S 2 0 t =
      S 2 0 t * L 2 s * S 1 0 r * L 3 q * S 3 0 p := by
    simpa only [mul_inv_rev,omega_inv,pair_inv,mul_assoc] using hki.symm
  have hxy : L 0 1 * L 1 b * (L 0 1)⁻¹ =
      (S 3 0 p * L 3 q * S 1 0 r * L 2 s * S 2 0 t) * L 1 b := by
    rw [←hki,hk]
    simp only [mul_inv_rev,pair_inv]
    have hy : L 1 b * L 1 b = 1 := by
      rw [synchronizedPositivePoint_pair_mul,CharTwo.add_self_eq_zero,
        synchronizedPositivePoint_pair_zero]
    simp only [mul_assoc,hy,mul_one]
  have hwz : W false * L 2 b * (W false)⁻¹ = L 1 b := by
    simpa only [next,Matrix.cons_val,Fin.isValue,Matrix.head_cons,MulAut.conj_apply] using
      batch_pair_reflection Q split c false 2 (by decide) b
  have hxz : L 0 1 * L 2 b * (L 0 1)⁻¹ = L 2 b := by
    rw [((synchronized_linear_commute_family Q split c b 1).2.2.2.2.symm).eq,
      mul_inv_cancel_right]
  have hf := fixed_of_braid (linear_braid Q split c) hwz hxz
  rw [hxy] at hf
  change MulAut.conj (W false) _ = _ at hf
  simp only [map_mul,batch_quartet_reflection Q split c false 3 (by decide),
    batch_quartet_reflection Q split c false 1 (by decide),
    batch_quartet_reflection Q split c false 2 (by decide),
    batch_pair_reflection Q split c false 3 (by decide),
    batch_pair_reflection Q split c false 2 (by decide),
    batch_pair_reflection Q split c false 1 (by decide),
    next,Matrix.cons_val,Fin.isValue] at hf
  have hc : Commute (S 1 0 p * L 3 q * S 3 0 r * L 1 s) (L 2 b) :=
    (((synchronized_adjacent_commute_family Q split c b 0 p).2.2.2.2.1.symm.mul_left
      (synchronized_linear_commute_family Q split c q b).2.2.1).mul_left
      (omega_linear_commute Q split c r b).1).mul_left
      (synchronized_linear_commute_family Q split c s b).2.1
  have hcollect :
      S 1 0 p * L 3 q * S 3 0 r * L 1 s * S 0 0 t * L 2 b =
        L 2 b * S 1 0 p * L 3 q * S 3 0 (r+t*b) * L 1 s * S 0 0 t := by
    calc
      _ = (S 1 0 p * L 3 q * S 3 0 r * L 1 s) * (S 0 0 t * L 2 b) := by group
      _ = (S 1 0 p * L 3 q * S 3 0 r * L 1 s) *
          (L 2 b * S 3 0 (t*b) * S 0 0 t) := by rw [omega_next_reorder]
      _ = L 2 b * (S 1 0 p * L 3 q * S 3 0 r * L 1 s) *
          S 3 0 (t*b) * S 0 0 t := by rw [←mul_assoc,←mul_assoc,hc.eq]
      _ = L 2 b * S 1 0 p * L 3 q * S 3 0 r * S 3 0 (t*b) *
          L 1 s * S 0 0 t := by
        simp only [mul_assoc,(synchronized_adjacent_commute_family Q split c s 0 (t*b)).2.1.left_comm]
      _ = _ := by
        have ho : S 3 0 r * S 3 0 (t*b) = S 3 0 (r+t*b) := by
          simp only [synchronizedPositivePoint_quartet_mul,
            map_zero,zero_mul,add_zero]
        simpa only [mul_assoc] using congrArg
          (fun z => L 2 b * S 1 0 p * L 3 q * z * L 1 s * S 0 0 t) ho
  rw [hcollect,hreverse] at hf
  have hcoords := carter_unique Q split c 0 b p q (r+t*b) s t t s r q p b 0 (by
    simpa only [synchronizedPositivePoint_quartet_zero,one_mul,mul_one] using hf)
  have ht : t = 0 := hcoords.2.2.2.2.2.2
  have hs : s = b := hcoords.2.1.symm
  have hr : r = p := hcoords.2.2.1.symm
  subst t; subst s; subst r
  refine ⟨p,q,?_⟩
  simpa only [synchronizedPositivePoint_quartet_zero,mul_one] using hxy

private theorem reverse_conjugate {G : Type*} [Group G] {a b z : G}
    (h : a*b*a⁻¹ = z*b) : b*a*b⁻¹ = z⁻¹*a := by
  calc
    _ = z⁻¹ * (z*b) * a * b⁻¹ := by group
    _ = z⁻¹ * (a*b*a⁻¹) * a * b⁻¹ := by rw [h]
    _ = _ := by group

private theorem correction_inv {G : Type*} [Group G] {x y k : G}
    (hx : x⁻¹ = x) (h : x*y*x⁻¹ = k*y) : x*k*x⁻¹ = k⁻¹ := by
  have hk : k = x*y*x⁻¹*y⁻¹ := by rw [h]; group
  rw [hk]
  simp only [mul_inv_rev,inv_inv,hx]
  have hx2 : x*x = 1 := by simpa only [hx] using inv_mul_cancel x
  simp only [←mul_assoc,hx2,one_mul]

private theorem seed_linear (b : CoefficientField m) :
    ∃ q : CoefficientField m,
      L 0 1 * L 1 b * (L 0 1)⁻¹ = L 3 q * L 2 b * L 1 b := by
  obtain ⟨p,q,h⟩ := seed_support Q split c b
  have hki : (S 3 0 p * L 3 q * S 1 0 p * L 2 b)⁻¹ =
      S 3 0 p * L 3 q * S 1 0 p * L 2 b := by
    simpa only [synchronizedPositivePoint_quartet_zero,mul_one] using
      phi_word_inv Q split c p q p b 0
  have hf := correction_inv (pair_inv Q split c 0 1) h
  rw [hki] at hf
  have ho3 : MulAut.conj (L 0 1) (S 3 0 p) = S 1 0 p * S 3 0 p := by
    have hh := synchronized_next_shifted_conjugate Q split c 0 p 1
    simp only [map_zero,zero_mul,add_zero,mul_one,synchronizedPositivePoint_pair_zero,
      synchronizedPositivePoint_quartet_zero] at hh
    simpa only [omega_inv,MulAut.conj_apply] using reverse_conjugate hh
  have ho1 : Commute (L 0 1) (S 1 0 p) := by
    apply Commute.symm
    apply commute_of_conj
    simpa only [zero_mul,synchronizedPositivePoint_quartet_zero,one_mul] using
      synchronized_short_terminal_conjugate Q split c 0 p 1
  have hl3 := (synchronized_linear_commute_family Q split c q 1).2.2.2.1.symm
  have hl2 := (synchronized_linear_commute_family Q split c b 1).2.2.2.2.symm
  change MulAut.conj (L 0 1) _ = _ at hf
  simp only [map_mul,ho3,MulAut.conj_apply,hl3.eq,ho1.eq,hl2.eq,mul_inv_cancel_right] at hf
  have hz : S 1 0 p = 1 := mul_right_cancel (show
      S 1 0 p * (S 3 0 p * L 3 q * S 1 0 p * L 2 b) =
      1 * (S 3 0 p * L 3 q * S 1 0 p * L 2 b) by
        simpa only [mul_assoc,one_mul] using hf)
  have hp : p = 0 := congrArg Prod.snd
    ((synchronizedPositiveChart Q split c (.inr 1)).injective (Subtype.ext
      (hz.trans (synchronizedPositivePoint_quartet_zero Q split c 1).symm)))
  refine ⟨q,?_⟩
  simpa only [hp,synchronizedPositivePoint_quartet_zero,one_mul,mul_one] using h

private theorem linear_support (a b : CoefficientField m) :
    ∃ q : CoefficientField m,
      L 0 a * L 1 b * (L 0 a)⁻¹ = L 3 q * L 2 (b*titsEnd m a) * L 1 b := by
  by_cases ha : a = 0
  · subst a
    refine ⟨0,?_⟩
    simp only [map_zero,mul_zero,synchronizedPositivePoint_pair_zero,one_mul,inv_one,mul_one]
  obtain ⟨r,hr⟩ := ((titsAutomorphism m).surjective.comp (titsAutomorphism m).surjective) a
  have hr2 : r^2 = a := (titsAutomorphism_twice m r).symm.trans hr
  have hr0 : r ≠ 0 := by intro h; apply ha; simpa only [h,zero_pow (by decide : (2 : ℕ) ≠ 0)] using hr2.symm
  let v : (CoefficientField m)ˣ := (Units.mk0 r hr0)⁻¹
  have hv : (v : CoefficientField m)⁻¹^2 = a := by
    simpa only [v,Units.val_inv_eq_inv_val,Units.val_mk0,inv_inv] using hr2
  let u : CoefficientField m := (titsEnd m v)⁻¹*b
  have ht0 : titsEnd m v ≠ 0 := (map_ne_zero (titsEnd m)).mpr (Units.ne_zero v)
  have hu : titsEnd m v*u = b := by
    dsimp only [u]
    rw [←mul_assoc,mul_inv_cancel₀ ht0,one_mul]
  have hu2 : (titsEnd m v)⁻¹*u = b*titsEnd m a := by
    rw [←hv,map_pow,map_inv₀]
    dsimp only [u]
    ring
  obtain ⟨q,hq⟩ := seed_linear Q split c u
  have hs0 : MulAut.conj ((synchronizedLinearTorus Q split c v)⁻¹) (L 0 1) = L 0 a := by
    simp only [MulAut.conj_apply,inv_inv,point_simple_linear]
    rw [synchronizedLinearTorus_simple,mul_one,hv]
  have hs1 : MulAut.conj ((synchronizedLinearTorus Q split c v)⁻¹) (L 1 u) = L 1 b := by
    simpa only [MulAut.conj_apply,inv_inv,hu] using
      synchronizedLinearTorus_reflectedLinear Q split c v u
  have hs2 : MulAut.conj ((synchronizedLinearTorus Q split c v)⁻¹) (L 2 u) =
      L 2 (b*titsEnd m a) := by
    simpa only [MulAut.conj_apply,inv_inv,hu2] using
      synchronizedLinearTorus_nextLinear Q split c v u
  have hs3 : MulAut.conj ((synchronizedLinearTorus Q split c v)⁻¹) (L 3 q) = L 3 q := by
    simpa only [MulAut.conj_apply,inv_inv] using
      synchronizedLinearTorus_perpendicularLinear Q split c v q
  simp only [map_inv] at hs0 hs1 hs2 hs3
  refine ⟨q,?_⟩
  have hh := congrArg (MulAut.conj ((synchronizedLinearTorus Q split c v)⁻¹)) hq
  simpa only [map_mul,map_inv,hs0,hs1,hs2,hs3] using hh

private theorem two_linear_unique (p q p' q' : CoefficientField m)
    (h : L 3 p * L 2 q = L 3 p' * L 2 q') : p = p' ∧ q = q' := by
  rw [(synchronized_linear_commute_family Q split c p q).2.2.1.eq,
    (synchronized_linear_commute_family Q split c p' q').2.2.1.eq] at h
  have hh := carter_unique Q split c 0 q 0 p 0 0 0 0 q' 0 p' 0 0 0 (by
    simpa only [synchronizedPositivePoint_quartet_zero,synchronizedPositivePoint_pair_zero,
      one_mul,mul_one] using h)
  exact ⟨hh.2.2.2.1,hh.2.1⟩

/-- The last linear pair has exactly the two native linear coefficients. -/
theorem synchronized_last_linear_conjugate (b a : CoefficientField m) :
    L 1 b * L 0 a * (L 1 b)⁻¹ =
      L 3 (titsEnd m b*a) * L 2 (b*titsEnd m a) * L 0 a := by
  obtain ⟨q,hq⟩ := linear_support Q split c a b
  obtain ⟨r,hr⟩ := linear_support Q split c b a
  have he := congrArg (MulAut.conj (W true)) hr
  have he' : L 1 b * L 0 a * (L 1 b)⁻¹ =
      L 2 r * L 3 (a*titsEnd m b) * L 0 a := by
    simpa only [map_mul,map_inv,batch_pair_reflection Q split c true 0 (by decide),
      batch_pair_reflection Q split c true 1 (by decide),
      batch_pair_reflection Q split c true 2 (by decide),
      batch_pair_reflection Q split c true 3 (by decide),next,Matrix.cons_val,Fin.isValue] using he
  have hrev : L 1 b * L 0 a * (L 1 b)⁻¹ =
      L 3 q * L 2 (b*titsEnd m a) * L 0 a := by
    have hh := reverse_conjugate hq
    simpa only [mul_inv_rev,pair_inv,
      ←(synchronized_linear_commute_family Q split c q (b*titsEnd m a)).2.2.1.eq] using hh
  have hp : q = titsEnd m b*a := by
    have hh := mul_right_cancel (hrev.symm.trans he')
    rw [←(synchronized_linear_commute_family Q split c (a*titsEnd m b) r).2.2.1.eq] at hh
    exact (two_linear_unique Q split c _ _ _ _ hh).1.trans (mul_comm _ _)
  simpa only [hp] using hrev

open Theory.GroupTheory.OrderedRootPresentation
open ReeF4.CentralCovers.TwoPrimary

/-- Discharge the remaining linear pair in the exact native angular table. -/
theorem synchronized_lastLinearAngular_equation
    (hj : (.inl 0 : PositiveTables.Root) ∈ tail sourceOrder (.inl 1))
    (u : AngularPresentation.Parameter m (.inl 1))
    (v : AngularPresentation.Parameter m (.inl 0)) :
    synchronizedSourceRoot Q split c (.inl 1) u * synchronizedSourceRoot Q split c (.inl 0) v *
      (synchronizedSourceRoot Q split c (.inl 1) u)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder (.inl 1))
        ((AngularPresentation.table m).conjugate (.inl 1) (.inl 0) hj u v) := by
  obtain ⟨b,rfl⟩ := (PositiveTables.rootChartEquiv m (.inl 1)).surjective u
  obtain ⟨a,rfl⟩ := (PositiveTables.rootChartEquiv m (.inl 0)).surjective v
  rw [AngularNextTransforms.table17,AngularNextTransforms.tail17_word]
  rw [synchronizedSourceRoot_field Q split c (.inl 1) b,
    synchronizedSourceRoot_field Q split c (.inl 0) a,
    synchronizedSourceRoot_field Q split c (.inl 3) (titsEnd m b*a),
    synchronizedSourceRoot_field Q split c (.inl 2) (b*titsEnd m a)]
  exact synchronized_last_linear_conjugate Q split c b a

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
