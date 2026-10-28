module
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.Orbits
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.J4Fusion.InvolutionCosets

/-!
# Involutions in the original Todd point group and its ambient join

The native fixed-coset calculations lift to conjugation in the actual Todd
semidirect product. Together with the existing M24 involution coverage, they
give four explicit representatives outside the radical, retaining their
orders and literal quotient images. The original Todd equivalence transports
these representatives and their conjugators to M. Adding the two radical
orbits gives six representatives for all point-group involutions.

The original ambient Sylow subgroup is still Sylow in C_G(z) joined with M.
Sylow conjugacy therefore gives the same six representatives there, with
conjugators inside that join and without assuming its simplicity. The descendant
CoreLifts and CoreFusion modules fuse these four lifts into the original plane
core and complete the two-class reduction.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), proof of (6.4) and
its use in (6.5)(2), p.602.
-/

public section
open Subgroup Sporadic.Mathieu MathieuCode
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open SourceIncidence LocalGeometry.LocalSubgroups
open MathieuCode.J4Fusion.InvolutionCosets
noncomputable section

private def toddElement (s : M24) (v : Cocode) : ToddGroup :=
  ⟨Multiplicative.ofAdd v,s⟩

private lemma toddElement_fixed {s : M24} {v : Cocode}
    (hsq : toddElement s v ^ 2 = 1) : cocodeRepresentation s v = v := by
  rw [pow_two] at hsq
  have he := congrArg (fun x : ToddGroup => x.left.toAdd) hsq
  change v + cocodeRepresentation s v = 0 at he
  have hn : -v = v := by
    rw [←neg_one_smul (ZMod 2),show (-1 : ZMod 2) = 1 by decide,one_smul]
  exact (eq_neg_of_add_eq_zero_right he).trans hn

private lemma toddElement_conjugate (s g : M24) (u w : Cocode)
    (hg : Commute g s) :
    IsConj (toddElement s u)
      (toddElement s (cocodeRepresentation s w - w + cocodeRepresentation g u)) := by
  apply isConj_iff.mpr
  refine ⟨toddElement g (-w),mul_inv_eq_iff_eq_mul.mpr ?_⟩
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    change -w + cocodeRepresentation g u =
      (cocodeRepresentation s w - w + cocodeRepresentation g u) + cocodeRepresentation s (-w)
    rw [map_neg]
    abel
  · exact hg.eq

/-- The four explicit Todd lifts used in the first paragraph of AS91 (6.4). -/
def toddLift (b e : Bool) : ToddGroup :=
  toddElement (if b then M24InvolutionCentralizers.involution2A else M24InvolutionCentralizers.involution2B)
    (if e then (if b then zVector else tVector) else 0)

private lemma toddElement_order (s : M24) (v : Cocode) (hs : orderOf s = 2)
    (hv : cocodeRepresentation s v = v) : orderOf (toddElement s v) = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two]
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change v + cocodeRepresentation s v = 0
      rw [hv,←two_smul (ZMod 2) v,show (2 : ZMod 2) = 0 by decide,zero_smul]
    · exact (pow_two s).symm.trans (orderOf_eq_prime_iff.mp hs).1
  · intro he
    exact (orderOf_eq_prime_iff.mp hs).2 (congrArg SemidirectProduct.right he)

/-- All four candidates are actual involutions, in the literal Todd product. -/
theorem toddLift_order (b e : Bool) : orderOf (toddLift b e) = 2 := by
  cases b <;> cases e
  · exact toddElement_order _ _ M24InvolutionCentralizers.involution2B_order (map_zero _)
  · exact toddElement_order _ _ M24InvolutionCentralizers.involution2B_order tVector_fixed
  · exact toddElement_order _ _ M24InvolutionCentralizers.involution2A_order (map_zero _)
  · exact toddElement_order _ _ M24InvolutionCentralizers.involution2A_order zVector_fixed

/-- Their images use precisely the original two native quotient involutions. -/
theorem toddLift_projection (b e : Bool) : (toddLift b e).right =
    if b then M24InvolutionCentralizers.involution2A else M24InvolutionCentralizers.involution2B := by
  cases b <;> cases e <;> rfl

private lemma toddElement_z_cover (v : Cocode)
    (hv : cocodeRepresentation CocodeOctad.Involutions.z v = v) :
    ∃ e : Bool, IsConj (toddLift true e) (toddElement CocodeOctad.Involutions.z v) := by
  rcases fixed_coset_z v hv with ⟨w,rfl⟩ | ⟨k,w,rfl⟩
  · refine ⟨false,?_⟩
    simpa only [toddLift,Bool.false_eq_true,↓reduceIte,map_zero,add_zero] using
      toddElement_conjugate CocodeOctad.Involutions.z 1 0 w (Commute.one_left _)
  · refine ⟨true,?_⟩
    exact toddElement_conjugate _ (actor^k.val) zVector w (actor_commutes.pow_left k.val)

private lemma toddElement_t_cover (v : Cocode)
    (hv : cocodeRepresentation CocodeOctad.Involutions.t v = v) :
    ∃ e : Bool, IsConj (toddLift false e) (toddElement CocodeOctad.Involutions.t v) := by
  rcases fixed_coset_t v hv with ⟨w,rfl⟩ | ⟨w,rfl⟩
  · refine ⟨false,?_⟩
    simpa only [toddLift,Bool.false_eq_true,↓reduceIte,map_zero,add_zero] using
      toddElement_conjugate CocodeOctad.Involutions.t 1 0 w (Commute.one_left _)
  · refine ⟨true,?_⟩
    simpa only [toddLift,Bool.false_eq_true,↓reduceIte,map_one,Module.End.one_apply] using
      toddElement_conjugate CocodeOctad.Involutions.t 1 tVector w (Commute.one_left _)

/-- The zero-vector lifts use the original splitting, not a new section. -/
theorem toddLift_false (b : Bool) : toddLift b false =
    SemidirectProduct.inr (if b then M24InvolutionCentralizers.involution2A
      else M24InvolutionCentralizers.involution2B) := by
  cases b <;> rfl

/-- A fixed vector outside the displacement image represents the second
involution orbit over the same quotient representative. -/
theorem toddLift_nonzero_coset (b : Bool) (v : Cocode)
    (hv : cocodeRepresentation (if b then M24InvolutionCentralizers.involution2A
      else M24InvolutionCentralizers.involution2B) v = v)
    (hn : ¬ ∃ w : Cocode, v = cocodeRepresentation
      (if b then M24InvolutionCentralizers.involution2A
        else M24InvolutionCentralizers.involution2B) w - w) :
    IsConj (toddLift b true) (⟨Multiplicative.ofAdd v,
      if b then M24InvolutionCentralizers.involution2A
        else M24InvolutionCentralizers.involution2B⟩ : ToddGroup) := by
  cases b
  · rcases fixed_coset_t v hv with hz | ⟨w,rfl⟩
    · exact (hn hz).elim
    · change IsConj (toddElement CocodeOctad.Involutions.t tVector)
        (toddElement CocodeOctad.Involutions.t
          (cocodeRepresentation CocodeOctad.Involutions.t w - w + tVector))
      simpa only [map_one,Module.End.one_apply] using
        toddElement_conjugate CocodeOctad.Involutions.t 1 tVector w (Commute.one_left _)
  · rcases fixed_coset_z v hv with hz | ⟨k,w,rfl⟩
    · exact (hn hz).elim
    · exact toddElement_conjugate _ (actor^k.val) zVector w (actor_commutes.pow_left k.val)

/-- Every involution outside the Todd radical is conjugate in the actual
semidirect product to one of the four explicit lifts. -/
theorem todd_involution_cover (x : ToddGroup) (hx : orderOf x = 2) (hne : x.right ≠ 1) :
    ∃ b e : Bool, IsConj (toddLift b e) x := by
  have hxr : orderOf x.right = 2 := by
    apply orderOf_eq_prime
    · have he := congrArg SemidirectProduct.right ((orderOf_eq_prime_iff.mp hx).1)
      simpa only [pow_two,SemidirectProduct.mul_right,SemidirectProduct.one_right] using he
    · exact hne
  have lift (s : M24) (hs : IsConj s x.right)
      (hc : ∀ v, cocodeRepresentation s v = v →
        ∃ b e : Bool, IsConj (toddLift b e) (toddElement s v)) :
      ∃ b e : Bool, IsConj (toddLift b e) x := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hs
    let n : ToddGroup := SemidirectProduct.inr g⁻¹
    let y := MulAut.conj n x
    have hy : y.right = s := by
      change (n*x*n⁻¹).right = s
      simp only [SemidirectProduct.mul_right,SemidirectProduct.inv_right,n,
        SemidirectProduct.right_inr,inv_inv]
      rw [←hg]
      group
    have he : y = toddElement s y.left.toAdd := by
      apply SemidirectProduct.ext
      · rfl
      · exact hy
    have hy2 : toddElement s y.left.toAdd ^ 2 = 1 := by
      rw [←he]
      change (MulAut.conj n x)^2 = 1
      rw [←map_pow,(orderOf_eq_prime_iff.mp hx).1,map_one]
    obtain ⟨b,e,hc⟩ := hc _ (toddElement_fixed hy2)
    refine ⟨b,e,hc.trans ?_⟩
    rw [←he]
    exact (isConj_iff.mpr ⟨n,rfl⟩).symm
  rcases M24InvolutionCentralizers.involution_classes x.right hxr with hA | hB
  · apply lift _ hA
    intro v hv
    obtain ⟨e,he⟩ := toddElement_z_cover v hv
    exact ⟨true,e,he⟩
  · apply lift _ hB
    intro v hv
    obtain ⟨e,he⟩ := toddElement_t_cover v hv
    exact ⟨false,e,he⟩

variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

/-- The lifts retain the original Todd embedding into the ambient group. -/
def pointLift (a : LocalData h) (b e : Bool) : G := a.P.toddEquiv (toddLift b e)

theorem pointLift_coe (a : LocalData h) (b e : Bool) :
    pointLift a b e = (a.P.toddEquiv (toddLift b e) : G) := by
  unfold pointLift
  rfl

theorem pointLift_mem (a : LocalData h) (b e : Bool) : pointLift a b e ∈ a.P.M :=
  (a.P.toddEquiv (toddLift b e)).property

theorem pointLift_order (a : LocalData h) (b e : Bool) : orderOf (pointLift a b e) = 2 :=
  (Subgroup.orderOf_coe (a.P.toddEquiv (toddLift b e))).trans
    ((a.P.toddEquiv.orderOf_eq _).trans (toddLift_order b e))

theorem pointLift_projection (a : LocalData h) (b e : Bool) :
    a.P.projection ⟨pointLift a b e,pointLift_mem a b e⟩ =
      if b then M24InvolutionCentralizers.involution2A else M24InvolutionCentralizers.involution2B := by
  change (a.P.toddEquiv.symm (a.P.toddEquiv (toddLift b e))).right = _
  rw [MulEquiv.symm_apply_apply,toddLift_projection]

theorem pointLift_not_mem_radical (a : LocalData h) (b e : Bool) : pointLift a b e ∉ a.P.E := by
  intro hm
  have hk : (⟨pointLift a b e,pointLift_mem a b e⟩ : a.P.M) ∈ a.P.projection.ker := by
    rw [a.P.projection_ker]
    exact hm
  have he := MonoidHom.mem_ker.mp hk
  rw [pointLift_projection] at he
  cases b
  · exact (orderOf_eq_prime_iff.mp M24InvolutionCentralizers.involution2B_order).2 he
  · exact (orderOf_eq_prime_iff.mp M24InvolutionCentralizers.involution2A_order).2 he

/-- The source (6.4) point-group reduction, with an actual M-conjugator. -/
theorem point_involution_outside_radical (a : LocalData h) (u : G)
    (huM : u ∈ a.P.M) (hu : orderOf u = 2) (huE : u ∉ a.P.E) :
    ∃ b e : Bool, ∃ m ∈ a.P.M, MulAut.conj m (pointLift a b e) = u := by
  let uM : a.P.M := ⟨u,huM⟩
  let x := a.P.toddEquiv.symm uM
  have hx : orderOf x = 2 := (a.P.toddEquiv.symm.orderOf_eq uM).trans
    ((Subgroup.orderOf_coe uM).symm.trans hu)
  have hne : x.right ≠ 1 := by
    intro he
    have hm : uM ∈ a.P.projection.ker := he
    rw [a.P.projection_ker] at hm
    exact huE hm
  obtain ⟨b,e,hc⟩ := todd_involution_cover x hx hne
  obtain ⟨m,hm⟩ := isConj_iff.mp (a.P.toddEquiv.toMonoidHom.map_isConj hc)
  refine ⟨b,e,m,m.property,?_⟩
  have he := congrArg Subtype.val hm
  simpa only [pointLift,x,uM,MulAut.conj_apply,Subgroup.coe_mul,Subgroup.coe_inv,
    MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply] using he

/-- Six point-group representatives suffice, and every conjugator remains in M. -/
theorem point_involution_representatives (a : LocalData h) (u : G)
    (huM : u ∈ a.P.M) (hu : orderOf u = 2) :
    (∃ m ∈ a.P.M, MulAut.conj m z = u) ∨
    (∃ m ∈ a.P.M, MulAut.conj m (second a) = u) ∨
    ∃ b e : Bool, ∃ m ∈ a.P.M, MulAut.conj m (pointLift a b e) = u := by
  by_cases huE : u ∈ a.P.E
  · have hu1 : u ≠ 1 := (orderOf_eq_prime_iff.mp hu).2
    exact (E_orbits a u huE hu1).elim Or.inl (fun he => Or.inr (Or.inl he))
  · exact Or.inr (Or.inr (point_involution_outside_radical a u huM hu huE))

/-- The original Sylow subgroup remains Sylow in C_G(z) joined with M.
Thus every involution in that join is conjugate into M by an element of
the join; no simplicity hypothesis on the join is used. -/
theorem join_involution_into_point (a : LocalData h) (u : G)
    (huK : u ∈ centralizer z ⊔ a.P.M) (hu : orderOf u = 2) :
    ∃ k ∈ centralizer z ⊔ a.P.M, MulAut.conj k u ∈ a.P.M := by
  let K := centralizer z ⊔ a.P.M
  have hTM : (a.T : Subgroup G) ≤ a.P.M := fun x hx => (a.sylow_le hx).1.2
  have hTK : (a.T : Subgroup G) ≤ K := hTM.trans le_sup_right
  let S := a.T.subtype hTK
  let uK : K := ⟨u,huK⟩
  have ho : orderOf uK = 2^1 := ((Subgroup.orderOf_coe uK).symm.trans hu).trans (pow_one 2).symm
  obtain ⟨v,hv⟩ := S.exists_isConj_of_orderOf_eq_prime_pow ho
  obtain ⟨k,hk⟩ := isConj_iff.mp hv
  refine ⟨k,k.property,?_⟩
  have he := congrArg Subtype.val hk
  change MulAut.conj k.val u = v.val.val at he
  rw [he]
  exact hTM v.property

/-- Every involution of the original join has one of the six source
representatives, with its conjugator still in that join. This is the
Sylow transport needed by (6.5)(2), before the remaining four lifts are
fused into the original plane core. -/
theorem join_involution_representatives (a : LocalData h) (u : G)
    (huK : u ∈ centralizer z ⊔ a.P.M) (hu : orderOf u = 2) :
    (∃ k ∈ centralizer z ⊔ a.P.M, MulAut.conj k z = u) ∨
    (∃ k ∈ centralizer z ⊔ a.P.M, MulAut.conj k (second a) = u) ∨
    ∃ b e : Bool, ∃ k ∈ centralizer z ⊔ a.P.M, MulAut.conj k (pointLift a b e) = u := by
  obtain ⟨k,hk,hku⟩ := join_involution_into_point a u huK hu
  have ho : orderOf (MulAut.conj k u) = 2 := ((MulAut.conj k).orderOf_eq u).trans hu
  have transport (r : G) (hr : ∃ m ∈ a.P.M, MulAut.conj m r = MulAut.conj k u) :
      ∃ n ∈ centralizer z ⊔ a.P.M, MulAut.conj n r = u := by
    obtain ⟨m,hm,he⟩ := hr
    refine ⟨k⁻¹*m,(centralizer z ⊔ a.P.M).mul_mem
      ((centralizer z ⊔ a.P.M).inv_mem hk) ((le_sup_right : a.P.M ≤ centralizer z ⊔ a.P.M) hm),?_⟩
    apply (MulAut.conj k).injective
    calc
      MulAut.conj k (MulAut.conj (k⁻¹*m) r) = MulAut.conj m r := by
        simp [MulAut.conj_apply,mul_assoc]
      _ = MulAut.conj k u := he
  rcases point_involution_representatives a (MulAut.conj k u) hku ho with hz | ht | ⟨b,e,he⟩
  · exact Or.inl (transport z hz)
  · exact Or.inr (Or.inl (transport (second a) ht))
  · exact Or.inr (Or.inr ⟨b,e,transport (pointLift a b e) he⟩)

end
end Theory.GroupTheory.Recognition.JankoFour.SourceFusion
