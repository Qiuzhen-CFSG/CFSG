module
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.Complete
public import Theory.SpecificGroups.Triality.NormalizedRootCentralizers
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.UnitRepresentatives
import all Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.UnitRepresentatives
import all Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.ArmsReduction
import all Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.ShortLeading

/-!
# Triality involution fusion through compatible parabolic maps

The genuine root-coordinate reduction is performed with its local conjugators
retained. Each step lies in an original root parabolic and has both endpoints
in the positive Sylow subgroup. The two-reflection rotation is factored through
the arms radical; the central short-leading reduction retains its rank-one and
radical conjugators. These paths therefore transport through any two parabolic
maps agreeing on the whole Borel, without a map from the entire triality group.

The highest-root torus and the actual cubic-field SL₂ normalize the two root
parameters to one. The resulting representatives are the highest long root and
the same short root used in the source nonfusion argument. The companion applies
this to the literal original factor join and then uses cyclic quotient transfer
to obtain the ambient two-class catalogue at every original degree n>1.

The internal imports reuse checked coordinate identities while strengthening
their conjugacy conclusions to local paths; no model recognition is assumed.
Source: Aschbacher–Smith F.4.30, F.4.35, F.4.43, printed pp.290,292,296,
and 5.3.3–4, p.659 (refs/quasithin.pdf). The triality root coordinates and
cubic-field conventions follow GLS3 §§2.4–2.6 through the imported modules.
-/

public noncomputable section
open Subgroup
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
open Triality.Standard.RadicalCoordinates Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.RadicalCoordinates.LeviCommutators
open Triality.Standard.Parabolics.CentralRootSquare
open Triality.Standard.EvenInvolutionGeometry
open Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityCompletionFusion

private theorem radical_le_U (P : Parameters) (hp : P.prime=2) (a : Node) :
    radical P a ≤ unipotent P := by
  rw [radical_eq_descendedRootSubgroup P hp a]
  exact descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P hp a)
private theorem short_U (P : Parameters) (hp : P.prime=2) (i : Fin 3) (t : ExtensionField P) :
    short P hp i t ∈ unipotent P :=
  radical_le_U P hp .central (descendedRootSubgroup_le_radical P hp .central
    (short_mem P hp .central i trivial t))
private theorem long_U (P : Parameters) (hp : P.prime=2) (i : Fin 3) (t : fixedField P) :
    long P hp i t ∈ unipotent P :=
  radical_le_U P hp .arms (descendedRootSubgroup_le_radical P hp .arms
    (long_mem P hp .arms i trivial t))
private theorem U_parabolic (P : Parameters) (a : Node) : unipotent P ≤ parabolic P a :=
  (unipotent_le_borel P).trans (borel_le_parabolic P a)
private theorem weyl_mem (P : Parameters) (hp : P.prime=2) (a : Node) :
    weylRepresentative P hp (relativeReflection a) ∈ parabolic P a := by
  rw [weylRepresentative_simple]
  exact simpleRepresentative_mem_parabolic P hp a

private inductive Fusion (P : Parameters) : Carrier P → Carrier P → Prop
  | refl (x) : Fusion P x x
  | step (a : Node) (g x y : Carrier P) (hg : g∈parabolic P a)
      (hx : x∈unipotent P) (hy : y∈unipotent P) (he : g*x*g⁻¹=y) : Fusion P x y
  | trans {x y z} : Fusion P x y → Fusion P y z → Fusion P x z
  | symm {x y} : Fusion P x y → Fusion P y x

private theorem Fusion.order_eq {P : Parameters} {x y : Carrier P} (h : Fusion P x y) :
    orderOf x=orderOf y := by
  induction h with
  | refl => rfl
  | step a g x y hg hx hy he => exact ((MulAut.conj g).orderOf_eq x).symm.trans (congrArg orderOf he)
  | trans h k ih ik => exact ih.trans ik
  | symm h ih => exact ih.symm

private theorem rotate (P : Parameters) (hp : P.prime=2) (x y : Carrier P)
    (hx : x∈radical P .arms) (hy : y∈unipotent P)
    (he : weylRepresentative P hp (.r 5)*x*(weylRepresentative P hp (.r 5))⁻¹=y) :
    Fusion P x y := by
  let a := weylRepresentative P hp (.sr 0)
  let b := weylRepresentative P hp (.sr 1)
  have ha : a∈parabolic P .arms := weyl_mem P hp .arms
  have hb : b∈parabolic P .central := weyl_mem P hp .central
  have hx' : a*x*a⁻¹∈radical P .arms :=
    (normal_subgroupOf_iff (radical_le_parabolic P .arms)).mp (radical_normal P .arms) x a hx ha
  have hw : weylRepresentative P hp (.r 5)=b*a := by
    rw [show (DihedralGroup.r 5 : DihedralGroup 6)=.sr 1*.sr 0 by decide,weylRepresentative_mul]
  apply (Fusion.step .arms a x _ ha (radical_le_U P hp .arms hx)
    (radical_le_U P hp .arms hx') rfl).trans
  apply Fusion.step .central b _ y hb (radical_le_U P hp .arms hx') hy
  rw [hw] at he
  simpa only [mul_inv_rev,mul_assoc] using he

private theorem short_arms (P : Parameters) (hp : P.prime=2) (t : ExtensionField P) :
    short P hp 2 t∈radical P .arms :=
  descendedRootSubgroup_le_radical P hp .arms (short_mem P hp .arms 2 (by change (2 : Fin 3)≠0; decide) t)
private theorem long_arms (P : Parameters) (hp : P.prime=2) (i : Fin 3) (t : fixedField P) :
    long P hp i t∈radical P .arms :=
  descendedRootSubgroup_le_radical P hp .arms (long_mem P hp .arms i trivial t)

private theorem long_pair_zero (P : Parameters) (hp : P.prime=2)
    (b f : fixedField P) (hb : b≠0) :
    Fusion P (long P hp 0 b * long P hp 2 f) (long P hp 0 b) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  let t := f / b
  have ht : b*t=f := mul_div_cancel₀ f hb
  have hex : long P hp 1 t * long P hp 0 b =
      long P hp 0 b * long P hp 1 t * long P hp 2 (b*t) := by
    have h := congrArg (fun x => x * (long P hp 2 (b*t))⁻¹)
      (long_zero_one_exchange P hp b t).symm
    simp only [mul_inv_cancel_right] at h
    rw [long_inv P hp 2 (b*t)] at h
    exact h
  apply Fusion.step .arms (long P hp 1 t) _ _
    (U_parabolic P .arms (long_U P hp 1 t))
    ((unipotent P).mul_mem (long_U P hp 0 b) (long_U P hp 2 f)) (long_U P hp 0 b)
  rw [conjugate_mul,conjugate_of_exchange _ _ _ hex (highest_commute_long P hp (b*t) 1 t)]
  rw [← (highest_commute_long P hp f 1 t).eq]
  simp only [mul_inv_cancel_right]
  rw [mul_assoc,← long_add,ht,CharTwo.add_self_eq_zero,long_zero,mul_one]

private theorem long_pair_one (P : Parameters) (hp : P.prime=2)
    (e f : fixedField P) (he : e≠0) :
    Fusion P (long P hp 1 e * long P hp 2 f) (long P hp 1 e) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  let t := f / e
  have ht : t*e=f := div_mul_cancel₀ f he
  apply Fusion.step .arms (long P hp 0 t) _ _
    (U_parabolic P .arms (long_U P hp 0 t))
    ((unipotent P).mul_mem (long_U P hp 1 e) (long_U P hp 2 f)) (long_U P hp 1 e)
  rw [conjugate_mul,conjugate_of_exchange _ _ _ (long_zero_one_exchange P hp t e)
    (highest_commute_long P hp (t*e) 0 t)]
  rw [← (highest_commute_long P hp f 0 t).eq]
  simp only [mul_inv_cancel_right]
  rw [mul_assoc,← long_add,ht,CharTwo.add_self_eq_zero,long_zero,mul_one]

private def LocalReduced (P : Parameters) (hp : P.prime=2) (x : Carrier P) : Prop :=
  (∃ z : highestRoot P, Fusion P x z.val) ∨
  (∃ v : radical P .central, (firstLayer P hp v).1 ≠ 0 ∧ Fusion P x v.val)

private theorem LocalReduced.of_fusion {P : Parameters} {hp : P.prime=2}
    {x y : Carrier P} (hy : LocalReduced P hp y) (h : Fusion P x y) : LocalReduced P hp x := by
  rcases hy with ⟨z,hz⟩ | ⟨v,hv,hc⟩
  · exact Or.inl ⟨z,h.trans hz⟩
  · exact Or.inr ⟨v,hv,h.trans hc⟩

private theorem reduced_long_zero (P : Parameters) (hp : P.prime=2) (b f : fixedField P) :
    LocalReduced P hp (long P hp 0 b * long P hp 2 f) := by
  by_cases hb : b=0
  · exact Or.inl ⟨⟨long P hp 2 f,long_mem_highest P hp f⟩,by simpa only [hb,long_zero,one_mul] using (Fusion.refl (long P hp 2 f))⟩
  · exact Or.inl ⟨⟨long P hp 2 b,long_mem_highest P hp b⟩,
      (long_pair_zero P hp b f hb).trans
        (rotate P hp _ _ (long_arms P hp 0 b) (long_U P hp 2 b) (rotation_long_zero P hp b))⟩

private theorem reduced_long_one (P : Parameters) (hp : P.prime=2) (e f : fixedField P) :
    LocalReduced P hp (long P hp 1 e * long P hp 2 f) := by
  by_cases he : e=0
  · exact Or.inl ⟨⟨long P hp 2 f,long_mem_highest P hp f⟩,by simpa only [he,long_zero,one_mul] using (Fusion.refl (long P hp 2 f))⟩
  · exact Or.inl ⟨⟨long P hp 2 e,long_mem_highest P hp e⟩,
      (long_pair_one P hp e f he).trans
        (Fusion.step .central _ _ _ (weyl_mem P hp .central)
          (long_U P hp 1 e) (long_U P hp 2 e) (central_long_one P hp e))⟩

private theorem reduced_of_short_one (P : Parameters) (hp : P.prime=2)
    (c d : ExtensionField P) (e f : fixedField P) (hc : c≠0) :
    LocalReduced P hp (armsCoordinates P hp (![c,d],![0,e,f])).val := by
  refine Or.inr ⟨coordinates P hp (![c,0,d],![f,e]),?_,?_⟩
  · rw [firstLayer_coordinates P hp]
    exact hc
  · exact Fusion.step .central _ _ _ (weyl_mem P hp .central)
      (radical_le_U P hp .arms (armsCoordinates P hp _).property)
      (radical_le_U P hp .central (coordinates P hp _).property) (central_image P hp c d e f)

private theorem reduced_of_short_two (P : Parameters) (hp : P.prime=2)
    (d : ExtensionField P) (b f : fixedField P) :
    LocalReduced P hp (armsCoordinates P hp (![0,d],![b,0,f])).val := by
  by_cases hd : d=0
  · have hv : (armsCoordinates P hp (![0,d],![b,0,f])).val =
        long P hp 0 b * long P hp 2 f := by
      rw [armsCoordinates_factorization]
      simp [hd]
    rw [hv]
    exact reduced_long_zero P hp b f
  · refine Or.inr ⟨coordinates P hp (![fieldFrobenius P d,0,0],![f,b]),?_,?_⟩
    · rw [firstLayer_coordinates P hp]
      exact (map_ne_zero (fieldFrobenius P)).mpr hd
    · exact rotate P hp _ _ (armsCoordinates P hp _).property
        (radical_le_U P hp .central (coordinates P hp _).property) (rotation_image P hp d b f)

private theorem shear_preserves_square (P : Parameters) (hp : P.prime=2)
    (a : ExtensionField P) (v : ArmsParameters P)
    (hs : (armsCoordinates P hp v)^2=1) :
    (armsCoordinates P hp (shearParameters P a v))^2=1 := by
  apply Subtype.ext
  change (armsCoordinates P hp (shearParameters P a v)).val ^ 2 = 1
  rw [← short_shear,conj_pow]
  have h := congrArg (fun x : radical P .arms => x.val) hs
  change (armsCoordinates P hp v).val ^2=1 at h
  rw [h,mul_one,mul_inv_cancel]

private theorem reduced_of_long_zero (P : Parameters) (hp : P.prime=2)
    (v : ArmsParameters P) (hb : v.2 0 ≠ 0) (hs : (armsCoordinates P hp v)^2=1) :
    LocalReduced P hp (armsCoordinates P hp v).val := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  let a := v.1 0 / (v.2 0).val
  let w := shearParameters P a v
  have hbval : (v.2 0).val ≠ 0 := by exact_mod_cast hb
  have hwa : w.1 0=0 := by
    change v.1 0 + (v.2 0).val * (v.1 0 / (v.2 0).val)=0
    rw [mul_div_cancel₀ _ hbval,CharTwo.add_self_eq_zero]
  have hwb : w.2 0 = v.2 0 := rfl
  have hwe : w.2 1=0 := by
    have hz := arms_square_condition P hp w (shear_preserves_square P hp a v hs)
    rw [hwa,armsPairing_zero_left,add_zero,hwb] at hz
    exact (mul_eq_zero.mp hz).resolve_right hb
  have hw : w=(![0,w.1 1],![w.2 0,0,w.2 2]) := by
    apply Prod.ext
    · funext i; fin_cases i <;> simp [hwa]
    · funext i; fin_cases i <;> simp [hwe]
  have hr : LocalReduced P hp (armsCoordinates P hp w).val := by
    rw [hw]
    exact reduced_of_short_two P hp _ _ _
  exact hr.of_fusion (Fusion.step .arms _ _ _ (U_parabolic P .arms (short_U P hp 0 a))
    (radical_le_U P hp .arms (armsCoordinates P hp v).property)
    (radical_le_U P hp .arms (armsCoordinates P hp w).property) (short_shear P hp a v))

private theorem reduced_of_long_zero_eq_zero (P : Parameters) (hp : P.prime=2)
    (v : ArmsParameters P) (hb : v.2 0=0) :
    LocalReduced P hp (armsCoordinates P hp v).val := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  by_cases hc : v.1 0=0
  · by_cases hd : v.1 1=0
    · have hv : (armsCoordinates P hp v).val = long P hp 1 (v.2 1) * long P hp 2 (v.2 2) := by
        rw [armsCoordinates_factorization]
        simp [hb,hc,hd]
      rw [hv]
      exact reduced_long_one P hp _ _
    · obtain ⟨a,ha⟩ := armsPairing_surjective_left P hp (v.1 1) hd (v.2 1)
      have hw : shearParameters P a v = (![0,v.1 1],![0,0,v.2 2]) := by
        apply Prod.ext
        · funext i; fin_cases i <;> simp [shearParameters,hb,hc,higherCoefficient,-fieldFrobenius_apply]
        · funext i; fin_cases i <;>
            simp [shearParameters,hb,hc,ha,CharTwo.add_self_eq_zero,-fieldFrobenius_apply]
      apply (reduced_of_short_two P hp (v.1 1) 0 (v.2 2)).of_fusion
      exact Fusion.step .arms _ _ _ (U_parabolic P .arms (short_U P hp 0 a))
        (radical_le_U P hp .arms (armsCoordinates P hp v).property)
        (radical_le_U P hp .arms (armsCoordinates P hp _).property)
        (by rw [←hw]; exact short_shear P hp a v)
  · have hv : v=(![v.1 0,v.1 1],![0,v.2 1,v.2 2]) := by
      apply Prod.ext
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> simp [hb]
    rw [hv]
    exact reduced_of_short_one P hp _ _ _ _ hc

/-- Every arms-radical involution reduces to a highest-root element or a central
radical element with nonzero first short coordinate, on the literal carrier. -/
private theorem arms_local_reduction (P : Parameters) (hp : P.prime=2)
    (u : radical P .arms) (hu : orderOf u.val=2) :
    (∃ z : highestRoot P, Fusion P u.val z.val) ∨
    (∃ v : radical P .central, (firstLayer P hp v).1≠0 ∧ Fusion P u.val v.val) := by
  obtain ⟨v,rfl⟩ := (armsCoordinates P hp).surjective u
  change LocalReduced P hp (armsCoordinates P hp v).val
  by_cases hb : v.2 0=0
  · exact reduced_of_long_zero_eq_zero P hp v hb
  · apply reduced_of_long_zero P hp v hb
    apply Subtype.ext
    change (armsCoordinates P hp v).val ^2=1
    rw [← hu]
    exact pow_orderOf_eq_one _
open Triality.Standard.EvenInvolutionGeometry.ShortNormalization
open Triality.Standard.Parabolics.CentralRootSquare.ElementaryImage
private theorem reduced_short_fusion (P : Parameters) (hp : P.prime=2) (v : RootOrbitParameters P .central)
    (ha : v.1 0 ≠ 0) (hv : v.1 1 = 0) (hs : (coordinates P hp v)^2 = 1) :
    Fusion P (short P hp 0 (v.1 0)) (coordinates P hp v).val := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  obtain ⟨c,hc,hq⟩ := exists_higher_quadratic_preimage P hp ha
    (pairing_of_square P hp v hv hs) (v.2 1)
  obtain ⟨k,hk⟩ := armsPairing_surjective_right P hp (v.1 0) ha
    (v.2 0 + cubicTrace P (c * fieldFrobenius P (v.1 0) *
      fieldFrobenius P (fieldFrobenius P (v.1 0))))
  let w : RootOrbitParameters P .central := (![0,c,k],0)
  let r : RootOrbitParameters P .central := (![v.1 0,0,0],0)
  have hcd : armsPairing P c (v.1 2) = 0 := hc ▸ pairing_higher P hp (v.1 0) c
  have hmul : multiply P w r = multiply P v w := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [multiply,w,r,hv,higherCoefficient, -fieldFrobenius_apply,add_comm]
      exact hc
    · funext i
      fin_cases i
      · simp [multiply,w,r,hv,hc,hk,CharTwo.add_self_eq_zero,
          -fieldFrobenius_apply,add_assoc]
      · simp [multiply,w,r,hv,hq,hcd,higherCoefficient,-fieldFrobenius_apply]
  have he : (coordinates P hp w).val * (coordinates P hp r).val =
      (coordinates P hp v).val * (coordinates P hp w).val := by
    exact congrArg Subtype.val ((coordinates_multiply P hp w r).symm.trans
      ((congrArg (coordinates P hp) hmul).trans (coordinates_multiply P hp v w)))
  have hr : (coordinates P hp r).val = short P hp 0 (v.1 0) := by
    rw [coordinates_val,rootElement_factorization]
    simp [r,extendOrbit]
  rw [hr] at he
  exact Fusion.step .central _ _ _ (radical_le_parabolic P .central (coordinates P hp w).property)
    (short_U P hp 0 _) (radical_le_U P hp .central (coordinates P hp v).property)
    ((mul_inv_eq_iff_eq_mul).mpr he)
private theorem central_short_fusion (P : Parameters) (hp : P.prime=2)
    (u : radical P .central) (ha : (firstLayer P hp u).1≠0) (hu : orderOf u.val=2) :
    ∃ a : ExtensionField P, a≠0 ∧ Fusion P (short P hp 0 a) u.val := by
  have hs : u^2=1 := Subtype.ext (hu ▸ pow_orderOf_eq_one u.val)
  obtain ⟨g,hg⟩ := exists_firstLayer_normalization P hp u ha hs
  let v := (coordinates P hp).symm (conjugation P g u)
  have hv : coordinates P hp v=conjugation P g u := (coordinates P hp).apply_symm_apply _
  have hl : (v.1 0,v.1 1)=((firstLayer P hp u).1,0) :=
    (firstLayer_coordinates P hp v).symm.trans ((congrArg (firstLayer P hp) hv).trans hg)
  have ha' : v.1 0≠0 := by
    have he : v.1 0=(firstLayer P hp u).1 := congrArg Prod.fst hl
    rwa [he]
  have hs' : (coordinates P hp v)^2=1 := by rw [hv,←map_pow,hs,map_one]
  have hc := reduced_short_fusion P hp v ha' (congrArg Prod.snd hl) hs'
  rw [hv] at hc
  refine ⟨v.1 0,ha',hc.trans ?_⟩
  exact (Fusion.step .central _ _ _ g.property (radical_le_U P hp .central u.property)
    (radical_le_U P hp .central (conjugation P g u).property) (conjugation_val P g u).symm).symm

private theorem unipotent_fusion (n : ℕ) (hn : 0<n)
    (u : unipotent (binaryParameters n hn)) (hu : orderOf u.val=2) :
    (∃ z : highestRoot (binaryParameters n hn), z.val≠1 ∧ Fusion (binaryParameters n hn) z.val u.val) ∨
    (∃ a : ExtensionField (binaryParameters n hn), a≠0 ∧
      Fusion (binaryParameters n hn) (short (binaryParameters n hn) rfl 0 a) u.val) := by
  let P := binaryParameters n hn
  have hs : u^2=1 := Subtype.ext (hu ▸ pow_orderOf_eq_one u.val)
  have harms (ha : u.val∈radical P .arms) : _ := arms_local_reduction P rfl ⟨u.val,ha⟩ hu
  rcases TwoRank.unipotent_mem_radical_or_radical_of_square_eq_one n hn u hs with ha | hc
  · rcases harms ha with ⟨z,hz⟩ | ⟨v,hv,hc⟩
    · exact Or.inl ⟨z,fun he => by have hh := hz.order_eq; rw [hu,he,orderOf_one] at hh; contradiction,hz.symm⟩
    · obtain ⟨a,ha,hav⟩ := central_short_fusion P rfl v hv (hc.order_eq.symm.trans hu)
      exact Or.inr ⟨a,ha,hav.trans hc.symm⟩
  · let v : radical P .central := ⟨u.val,hc⟩
    by_cases hv : (firstLayer P rfl v).1=0
    · rcases harms (mem_armsRadical_of_firstShort_eq_zero P rfl v hv) with ⟨z,hz⟩ | ⟨v,hv,hc⟩
      · exact Or.inl ⟨z,fun he => by have hh := hz.order_eq; rw [hu,he,orderOf_one] at hh; contradiction,hz.symm⟩
      · obtain ⟨a,ha,hav⟩ := central_short_fusion P rfl v hv (hc.order_eq.symm.trans hu)
        exact Or.inr ⟨a,ha,hav.trans hc.symm⟩
    · exact Or.inr (central_short_fusion P rfl v hv hu)

variable {E : Type*} [Group E]
private theorem Fusion.mem_U_iff {P : Parameters} {x y : Carrier P} (h : Fusion P x y) :
    x∈unipotent P ↔ y∈unipotent P := by
  induction h with
  | refl => rfl
  | step a g x y hg hx hy he => exact iff_of_true hx hy
  | trans h k ih ik => exact ih.trans ik
  | symm h ih => exact ih.symm

private theorem Fusion.map_conj {P : Parameters}
    (f : parabolic P .arms →* E) (l : parabolic P .central →* E)
    (ha : ∀ x∈borel P, ∀ hx hy, f ⟨x,hx⟩=l ⟨x,hy⟩)
    {x y : Carrier P} (h : Fusion P x y)
    (hx : x∈unipotent P) (hy : y∈unipotent P) :
    IsConj (f ⟨x,U_parabolic P .arms hx⟩) (f ⟨y,U_parabolic P .arms hy⟩) := by
  induction h with
  | refl => exact IsConj.refl _
  | step a g x y hg hx' hy' he =>
    cases a with
    | arms =>
      apply isConj_iff.mpr
      refine ⟨f ⟨g,hg⟩,?_⟩
      rw [←map_inv,←map_mul,←map_mul]
      exact congrArg f (Subtype.ext he)
    | central =>
      rw [ha x (unipotent_le_borel P hx) _ (U_parabolic P .central hx),
        ha y (unipotent_le_borel P hy) _ (U_parabolic P .central hy)]
      apply isConj_iff.mpr
      refine ⟨l ⟨g,hg⟩,?_⟩
      rw [←map_inv,←map_mul,←map_mul]
      exact congrArg l (Subtype.ext he)
  | @trans x y z h k ih ik =>
    have hy' := h.mem_U_iff.mp hx
    exact (ih hx hy').trans (ik hy' hy)
  | symm h ih => exact (ih hy hx).symm

private theorem highest_U (P : Parameters) (hp : P.prime=2) : highestRoot P ≤ unipotent P :=
  (highestRoot_le_center_unipotent P hp).trans (map_subtype_le _)

/-- The highest long root in the original arms parabolic. -/
@[expose] def longElement (P : Parameters) (hp : P.prime=2) : parabolic P .arms :=
  ⟨highestHom P hp (Multiplicative.ofAdd 1), (borel_le_parabolic P .arms)
    ((unipotent_le_borel P) ((map_subtype_le (center (unipotent P)))
      (highestRoot_le_center_unipotent P hp (by
        rw [←highestHom_range P hp]; exact ⟨_,rfl⟩))))⟩

/-- The exact short root used by the original nonfusion argument. -/
@[expose] def shortElement (P : Parameters) (hp : P.prime=2) : parabolic P .arms :=
  ⟨short P hp 2 1, radical_le_parabolic P .arms (descendedRootSubgroup_le_radical P hp .arms
    (short_mem P hp .arms 2 (by change (2:Fin 3)≠0; decide) 1))⟩

private theorem highest_one_fusion (P : Parameters) (hp : P.prime=2)
    (z : highestRoot P) (hz : z.val≠1) : Fusion P (longElement P hp).val z.val := by
  have hz' : z.val∈(highestHom P hp).range := (highestHom_range P hp).ge z.property
  obtain ⟨a,ha⟩ := hz'
  have ha0 : a.toAdd≠0 := by
    intro he
    apply hz
    rw [←ha,show a=1 from congrArg Multiplicative.ofAdd he,map_one]
  let g := TorusCoordinates.torusMulEquiv P hp (1,Units.mk0 a.toAdd ha0)
  apply Fusion.step .arms g.val _ _
    (borel_le_parabolic P .arms (torus_le_borel P g.property))
    (highest_U P hp (by rw [←highestHom_range P hp]; exact ⟨_,rfl⟩)) (highest_U P hp z.property)
  have hh := NormalizedRootCentralizers.torus_conjugate_highestHom P hp
    (1,Units.mk0 a.toAdd ha0) 1
  change g.val * (longElement P hp).val * g.val⁻¹ = _ at hh
  have hh' : g.val * (longElement P hp).val * g.val⁻¹ = highestHom P hp a := by
    simpa only [Units.val_mk0,mul_one,ofAdd_toAdd] using hh
  exact hh'.trans ha

private def shortSL (n : ℕ) (hn : 0<n) :
    Matrix.SpecialLinearGroup (Fin 2) (ExtensionField (binaryParameters n hn)) →*
      parabolic (binaryParameters n hn) .arms :=
  let P := binaryParameters n hn
  ((toCarrier P).comp (sl2ElementaryLift P rfl (shortRankOneFixed n hn))).codRestrict _ (by
    intro g
    apply levi_le_parabolic P .arms
    refine ⟨sl2ElementaryLift P rfl (shortRankOneFixed n hn) g,?_,rfl⟩
    exact ((pinnedRankOneMaps P rfl).range_armsFixedEmbedding (armRootCommutation P rfl)).le
      ⟨g,rfl⟩ |>.1)

private theorem short_zero_one_fusion (n : ℕ) (hn : 0<n)
    (t : ExtensionField (binaryParameters n hn)) (ht : t≠0) :
    Fusion (binaryParameters n hn) (short (binaryParameters n hn) rfl 0 1)
      (short (binaryParameters n hn) rfl 0 t) := by
  let P := binaryParameters n hn
  obtain ⟨g,hg⟩ := isConj_iff.mp (upper_conjugate_one t ht)
  let f := shortSL n hn
  apply Fusion.step .arms (f g).val _ _ (f g).property (short_U P rfl 0 1) (short_U P rfl 0 t)
  rw [foldedShort_zero_eq_shortRoot,foldedShort_zero_eq_shortRoot]
  exact congrArg (fun x : parabolic P .arms => x.val)
    (by simpa only [map_mul,map_inv] using congrArg f hg)

private theorem short_one_fusion (n : ℕ) (hn : 0<n)
    (t : ExtensionField (binaryParameters n hn)) (ht : t≠0) :
    Fusion (binaryParameters n hn) (shortElement (binaryParameters n hn) rfl).val
      (short (binaryParameters n hn) rfl 0 t) := by
  let P := binaryParameters n hn
  have hr : Fusion P (short P rfl 2 1) (short P rfl 0 1) :=
    rotate P rfl _ _ (short_arms P rfl 1) (short_U P rfl 0 1)
      (by simpa only [map_one] using rotation_short_two P rfl 1)
  exact hr.trans (short_zero_one_fusion n hn t ht)

/-- Both compatible local maps carry all common-Sylow involutions into the
same two pinned root classes. No map from the entire triality group is assumed. -/
theorem compatible_involution_classes (n : ℕ) (hn : 0<n)
    (f : parabolic (binaryParameters n hn) .arms →* E)
    (l : parabolic (binaryParameters n hn) .central →* E)
    (ha : ∀ x∈borel (binaryParameters n hn), ∀ hx hy, f ⟨x,hx⟩=l ⟨x,hy⟩)
    (x : parabolic (binaryParameters n hn) .arms)
    (hx : x.val∈unipotent (binaryParameters n hn)) (hx2 : orderOf x=2) :
    IsConj (f (longElement (binaryParameters n hn) rfl)) (f x) ∨
      IsConj (f (shortElement (binaryParameters n hn) rfl)) (f x) := by
  let P := binaryParameters n hn
  have hx2' : orderOf x.val=2 := (Subgroup.orderOf_coe x).trans hx2
  rcases unipotent_fusion n hn ⟨x.val,hx⟩ hx2' with ⟨z,hz,hc⟩ | ⟨t,ht,hc⟩
  · exact Or.inl (((highest_one_fusion P rfl z hz).trans hc).map_conj f l ha
      (highest_U P rfl (by rw [←highestHom_range P rfl]; exact ⟨_,rfl⟩)) hx)
  · exact Or.inr (((short_one_fusion n hn t ht).trans hc).map_conj f l ha (short_U P rfl 2 1) hx)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityCompletionFusion
