module
public import Theory.SpecificGroups.Triality.BinaryTorusEndpoints
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.PositiveWeylModel

/-!
# Excluding the highest-root twist in binary triality

Write s for the arms reflection multiplied by the highest long-root
involution z, and t for the central reflection. If (st)^6=1, its half-turn
q=(st)^3 commutes with s. The short-root permutation rules give q(a)=s(a)
for the simple short-root involution a. The rank-one equation (as)^3=z
therefore forces q(z)=s(z)=z. Applying the long-root permutation rules to
this same equality forces t to fix its simple long-root involution, contrary
to the native rank-one negative-root separation.

All root identities are proved in the actual graph-field carrier and then
transported through two homomorphisms agreeing on the entire Borel. Only the
central endpoint needs injectivity. This excludes the remaining orbit in the
binary reflection-pair reduction, even for an arbitrary marked completion.
The generic transport lemma keeps concrete subgroup instances out of the
conjugation calculation.

Source: GLS3 §§2.4,2.6 for the root identities; this supplies the small-field
comparison needed for Aschbacher--Smith F.4.17,24, pp.282--283,287
(`refs/quasithin.pdf`).
-/

public noncomputable section
namespace Triality.Standard.BinaryTwistRelations
variable {G : Type*} [Group G]

private theorem obstruction (s t a b d x y z : G)
    (hs : s^2=1) (ht : t^2=1)
    (hsb : MulAut.conj s b=d) (hsd : MulAut.conj s d=b)
    (hta : MulAut.conj t a=b) (htb : MulAut.conj t b=a)
    (htd : MulAut.conj t d=d)
    (hsy : MulAut.conj s y=x) (hsz : MulAut.conj s z=z)
    (htz : MulAut.conj t z=y)
    (has : (a*s)^3=z) (hbraid : (s*t)^6=1) : MulAut.conj t x=x := by
  let S := MulAut.conj s
  let T := MulAut.conj t
  let q := (s*t)^3
  let Q := MulAut.conj q
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht)
  have hqi : q⁻¹=q := inv_eq_of_mul_eq_one_left (by
    change (s*t)^3*(s*t)^3=1
    rw [←pow_add]
    exact hbraid)
  have hsr : s*(s*t)*s⁻¹=(s*t)⁻¹ := by
    rw [mul_inv_rev,hti]
    calc
      _ = (s*s)*t*s⁻¹ := by group
      _ = _ := by rw [←pow_two,hs,one_mul]
  have hsq : S q=q := by
    change s*(s*t)^3*s⁻¹=q
    rw [←conj_pow,hsr,inv_pow]
    exact hqi
  have hqs : Q s=s := by
    have hh := mul_inv_eq_iff_eq_mul.mp hsq
    change q*s*q⁻¹=s
    rw [←hh,mul_inv_cancel_right]
  have hQ (v : G) : Q v=S (T (S (T (S (T v))))) := by
    dsimp [Q,q,S,T,MulAut.conj_apply]
    simp only [pow_succ,pow_zero]
    group
  have hqa : Q a=S a := by rw [hQ,hta,hsb,htd,hsd,htb]
  have hqz : Q z=z := by
    rw [←has,map_pow,map_mul,hqa,hqs]
    have he : S a*s=S (a*s) := by rw [map_mul]; simp [S]
    rw [he,←map_pow,has]
    exact hsz
  have hstep : S (T (S (T x)))=z := by
    rw [hQ,htz,hsy] at hqz
    exact hqz
  have hstep' : T (S (T x))=z := S.injective (hstep.trans hsz.symm)
  have hstep'' : S (T x)=y := by
    have he := congrArg T hstep'
    have hTT (v : G) : T (T v)=v := by
      dsimp [T,MulAut.conj_apply]
      calc
        _ = (t*t)*v*(t*t)⁻¹ := by group
        _ = v := by rw [←pow_two,ht]; simp
    rw [hTT,htz] at he
    exact he
  have hSS (v : G) : S (S v)=v := by
    change s*(s*v*s⁻¹)*s⁻¹=v
    calc
      _ = (s*s)*v*(s*s)⁻¹ := by group
      _ = v := by rw [←pow_two,hs]; simp
  have he := congrArg S hstep''
  rw [hSS,hsy] at he
  exact he

private theorem obstruction_maps {L R B : Type*} [Group L] [Group R] [Group B]
    (i : B →* L) (j : B →* R) (l : L →* G) (r : R →* G)
    (hc : l.comp i = r.comp j) (hr : Function.Injective r)
    (s : L) (t : R) (a b d x y z : B)
    (hs : s^2=1) (ht : t^2=1)
    (hsb : s*i b*s⁻¹=i d) (hsd : s*i d*s⁻¹=i b)
    (hta : t*j a*t⁻¹=j b) (htb : t*j b*t⁻¹=j a) (htd : t*j d*t⁻¹=j d)
    (hsy : s*i y*s⁻¹=i x) (hsz : s*i z*s⁻¹=i z) (htz : t*j z*t⁻¹=j y)
    (has : (i a*s)^3=i z) (hfix : t*j x*t⁻¹≠j x) : (l s*r t)^6≠1 := by
  intro hpow
  let m := l.comp i
  have hl (u : B) : l (i u)=m u := rfl
  have hh (u : B) : r (j u)=m u := (DFunLike.congr_fun hc u).symm
  have left_conj (u v : B) (h : s*i u*s⁻¹=i v) :
      MulAut.conj (l s) (m u)=m v := by
    have he := congrArg l h
    rw [map_mul,map_mul,map_inv,hl u,hl v] at he
    exact he
  have right_conj (u v : B) (h : t*j u*t⁻¹=j v) :
      MulAut.conj (r t) (m u)=m v := by
    have he := congrArg r h
    rw [map_mul,map_mul,map_inv,hh u,hh v] at he
    exact he
  have hs' : (l s)^2=1 := by rw [←map_pow,hs,map_one]
  have ht' : (r t)^2=1 := by rw [←map_pow,ht,map_one]
  have has' : (m a*l s)^3=m z := by
    have he := congrArg l has
    rw [map_pow,map_mul,hl a,hl z] at he
    exact he
  have he := obstruction (l s) (r t) (m a) (m b) (m d) (m x) (m y) (m z)
    hs' ht' (left_conj b d hsb) (left_conj d b hsd)
    (right_conj a b hta) (right_conj b a htb) (right_conj d d htd)
    (left_conj y x hsy) (left_conj z z hsz) (right_conj z y htz) has' hpow
  apply hfix
  apply hr
  rw [map_mul,map_mul,map_inv,hh x]
  exact he

open Subgroup Parabolics ConcreteBruhat RadicalCoordinates.LeviCommutators
open BinaryTorusEndpoints RootPresentationRecognition
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "C" => Carrier P

private def sb (i : Fin 3) : borel P :=
  ⟨short P (Eq.refl 2) i 1, unipotent_le_borel P
    (descendSubgroup_mono P (RadicalCoordinates.rootSubgroup_le_positiveSubgroup P (Eq.refl 2) .central)
      (short_mem P (Eq.refl 2) .central i trivial 1))⟩

private def lb (i : Fin 3) : borel P :=
  ⟨long P (Eq.refl 2) i 1, unipotent_le_borel P
    (descendSubgroup_mono P (RadicalCoordinates.rootSubgroup_le_positiveSubgroup P (Eq.refl 2) .arms)
      (long_mem P (Eq.refl 2) .arms i trivial 1))⟩

private abbrev twist := endpointWord .arms ![0,0,1] 0 1

private theorem twist_val : (twist:C)=(lb 2:C)*simpleRepresentative P (Eq.refl 2) .arms := by
  change (fixedBorel ![0,0,1]:C)*simpleRepresentative P (Eq.refl 2) .arms*
    (fixedBorel 0:C)*1=(lb 2:C)*simpleRepresentative P (Eq.refl 2) .arms
  simp only [fixedBorel,CentralCovers.TwoPrimary.baseProduct,Pi.zero_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,short_zero P (Eq.refl 2),long_zero P (Eq.refl 2),
    one_mul,mul_one]
  rfl

private theorem lb_sq (i : Fin 3) : (lb i:C)^2=1 := by
  change (long P (Eq.refl 2) i 1)^2=1
  calc
    (long P (Eq.refl 2) i 1)^2 = long P (Eq.refl 2) i 1*long P (Eq.refl 2) i 1 := pow_two _
    _ = long P (Eq.refl 2) i (1+1) := (long_add P (Eq.refl 2) i 1 1).symm
    _ = long P (Eq.refl 2) i 0 := congrArg (long P (Eq.refl 2) i)
      (CharTwo.add_self_eq_zero (1 : fixedField P))
    _ = 1 := long_zero P (Eq.refl 2) i

private theorem twist_conjugate (u v : C)
    (h : simpleRepresentative P (Eq.refl 2) .arms*u*(simpleRepresentative P (Eq.refl 2) .arms)⁻¹=v)
    (hz : Commute (lb 2:C) v) : MulAut.conj (twist:C) u=v := by
  change (twist:C)*u*(twist:C)⁻¹=v
  rw [twist_val]
  calc
    _ = (lb 2:C)*(simpleRepresentative P (Eq.refl 2) .arms*u*(simpleRepresentative P (Eq.refl 2) .arms)⁻¹)*(lb 2:C)⁻¹ := by group
    _ = v := by rw [h,hz.eq,mul_inv_cancel_right]

private theorem twist_short_one : MulAut.conj (twist:C) (sb 1:C)=(sb 2:C) := by
  apply twist_conjugate
  · simpa only [sb,map_one] using PositiveWeylModel.arms_short_one P (Eq.refl 2) 1
  · exact EvenInvolutionGeometry.ArmsNormalization.highest_commute_short P (Eq.refl 2) 1 2 1

private theorem twist_short_two : MulAut.conj (twist:C) (sb 2:C)=(sb 1:C) := by
  apply twist_conjugate
  · simpa only [sb,map_one] using PositiveWeylModel.arms_short_two P (Eq.refl 2) 1
  · exact EvenInvolutionGeometry.ArmsNormalization.highest_commute_short P (Eq.refl 2) 1 1 1

private theorem twist_long (i : Fin 3) :
    MulAut.conj (twist:C) (lb i:C)=(lb (![1,0,2] i):C) := by
  apply twist_conjugate
  · exact PositiveWeylModel.arms_long P (Eq.refl 2) i 1
  · exact EvenInvolutionGeometry.ArmsNormalization.highest_commute_long P (Eq.refl 2) 1 _ 1

private theorem central_short (i : Fin 3) :
    MulAut.conj (simpleEndpoint .central:C) (sb i:C)=(sb (![1,0,2] i):C) :=
  PositiveWeylModel.central_short P (Eq.refl 2) i 1

private theorem central_long :
    MulAut.conj (simpleEndpoint .central:C) (lb 2:C)=(lb 1:C) :=
  PositiveWeylModel.central_long P (Eq.refl 2) 2 (by decide) 1

private theorem twist_sq : twist^2=1 := by
  apply Subtype.ext
  change (twist:C)^2=1
  rw [twist_val]
  have hc : Commute (simpleRepresentative P (Eq.refl 2) .arms) (lb 2:C) :=
    mul_inv_eq_iff_eq_mul.mp (PositiveWeylModel.arms_long P (Eq.refl 2) 2 1)
  rw [hc.symm.mul_pow,lb_sq,simpleRepresentative_sq P (Eq.refl 2) .arms,one_mul]

private theorem twist_short_cube : ((sb 0:C)*(twist:C))^3=(lb 2:C) := by
  let a := (sb 0:C)
  let w := simpleRepresentative P (Eq.refl 2) .arms
  let z := (lb 2:C)
  have hw : w=a*(w*a*w)*a := by
    dsimp [a,w,sb]
    rw [PositiveWeylModel.short_zero P (Eq.refl 2) 1,simpleRepresentative_positive P (Eq.refl 2) .arms 1]
    exact simpleRepresentative_eq_root_word P (Eq.refl 2) .arms
  have haw : (a*w)^3=1 := by
    calc
      _ = (a*(w*a*w)*a)*w := by simp only [pow_succ,pow_zero]; group
      _ = w*w := by rw [←hw]
      _ = 1 := by simpa only [pow_two] using simpleRepresentative_sq P (Eq.refl 2) .arms
  have hza : Commute z a :=
    EvenInvolutionGeometry.ArmsNormalization.highest_commute_short P (Eq.refl 2) 1 0 1
  have hzw : Commute z w :=
    (mul_inv_eq_iff_eq_mul.mp (PositiveWeylModel.arms_long P (Eq.refl 2) 2 1)).symm
  have hz3 : z^3=z := by
    calc
      z^3=z^2*z := by group
      _=z := by rw [show z^2=1 from lb_sq 2,one_mul]
  rw [twist_val]
  change (a*(z*w))^3=z
  rw [←mul_assoc,←hza.eq,mul_assoc,(hza.mul_right hzw).mul_pow,hz3,haw,mul_one]

private theorem central_not_fixed :
    MulAut.conj (simpleEndpoint .central:C) (lb 0:C)≠(lb 0:C) := by
  intro he
  apply FoldedCellGeometry.positive_conjugate_not_borel 1 Nat.zero_lt_one .central
  have hi : (simpleRepresentative P (Eq.refl 2) .central)⁻¹=simpleRepresentative P (Eq.refl 2) .central :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using simpleRepresentative_sq P (Eq.refl 2) .central)
  change simpleRepresentative P (Eq.refl 2) .central*(long P (Eq.refl 2) 0 1)*
    (simpleRepresentative P (Eq.refl 2) .central)⁻¹=long P (Eq.refl 2) 0 1 at he
  rw [PositiveWeylModel.long_zero P (Eq.refl 2) 1,hi] at he
  rw [he]
  exact unipotent_le_borel P (positive_mem_unipotent P (Eq.refl 2) .central 1)

/-- The highest-root twist cannot obey the hexagon relation in compatible
endpoint images that are faithful on the central parabolic. -/
theorem twisted_product_six_ne_one
    (l : parabolic P .arms →* G) (r : parabolic P .central →* G)
    (hr : Function.Injective r)
    (hc : l.comp (inclusion (borel_le_parabolic P .arms)) =
      r.comp (inclusion (borel_le_parabolic P .central))) :
    (l (endpointWord .arms ![0,0,1] 0 1)*r (simpleEndpoint .central))^6≠1 := by
  apply obstruction_maps
    (inclusion (borel_le_parabolic P .arms))
    (inclusion (borel_le_parabolic P .central)) l r hc hr twist (simpleEndpoint .central)
    (sb 0) (sb 1) (sb 2) (lb 0) (lb 1) (lb 2) twist_sq
    (Subtype.ext (simpleRepresentative_sq P (Eq.refl 2) .central))
    (Subtype.ext twist_short_one) (Subtype.ext twist_short_two)
    (Subtype.ext (central_short 0)) (Subtype.ext (central_short 1))
    (Subtype.ext (central_short 2))
    (Subtype.ext (twist_long 1)) (Subtype.ext (twist_long 2))
    (Subtype.ext central_long) (Subtype.ext twist_short_cube)
  intro h
  exact central_not_fixed (congrArg Subtype.val h)

end Triality.Standard.BinaryTwistRelations
