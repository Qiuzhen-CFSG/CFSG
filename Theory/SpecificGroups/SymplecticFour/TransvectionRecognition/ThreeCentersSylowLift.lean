module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ThreeCentersDihedralLift
public import Theory.SpecificGroups.SL2.ResidualSylowGeneration
public import Theory.SpecificGroups.SL2.TwoSubgroupExponent
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import Theory.SpecificGroups.PSL2.AutomorphismModel


/-!
# The SL₂ Sylow lift in the three-center argument

Commuting point-quotient images of transvections have commuting lifts: their
product has order dividing four, whereas a noncommuting transvection product
has odd order. If all commuting conjugates have the same center, each quotient
Sylow group lifts into the stabilizer of the plane of the first two centers.
Those two Sylows generate SL₂. Uniqueness of transvection lifts through the
central radical then puts the third center in that plane, a contradiction.

The exact original three-center configuration converts the resulting pair
back into its normalizing coset. Together with the completed odd-dihedral
case, this constructs the c₂ element of the original irreducible subgroup.
No splitting, Sylow-lifting or coset-witness premise remains.

Source: Aschbacher--Smith G.4.9, printed p.341, preliminary claim. The original
E.2.7 simple-socle application is in SourceC2Witness.
-/

public noncomputable section

open Subgroup Module
open scoped MatrixGroups
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open InvolutionTypes InvolutionCentralizers
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Commutation of transvection images in the point quotient lifts to the
actual transvections. -/
theorem pointQuotient_commute_lift (a b : pointLocal (F:=F))
    (ha : IsB1 a.val) (hb : IsB1 b.val)
    (hq : Commute (pointQuotient a) (pointQuotient b)) : Commute a b := by
  have hs (t : pointLocal (F:=F)) (ht : IsB1 t.val) : t^2=1 :=
    Subtype.ext (by simpa only [Subgroup.coe_pow,Subgroup.coe_one,ht.1] using pow_orderOf_eq_one t.val)
  have hrad : (a*b)^2∈pointRadical := by
    change pointQuotient ((a*b)^2)=1
    rw [map_pow,map_mul,hq.mul_pow,←map_pow,←map_pow,hs a ha,hs b hb,map_one,mul_one]
  have hfour : (a.val*b.val)^4=1 := by
    have he := congrArg (fun t : pointRadical (F:=F) => t.val.val)
      (pointRadical_pow_two ⟨(a*b)^2,hrad⟩)
    simpa only [Subgroup.coe_pow,Subgroup.coe_mul,Subgroup.coe_one,←pow_mul] using he
  by_contra hn
  have hnc : ¬Commute a.val b.val := fun hh => hn (Subtype.ext hh.eq)
  have ho := odd_order_product_of_isB1 a.val b.val ha hb hnc
  have hd := orderOf_dvd_of_pow_eq_one hfour
  have hcop : Nat.Coprime (orderOf (a.val*b.val)) 4 := ho.coprime_two_right.pow_right 2
  have hone : orderOf (a.val*b.val)=1 := by
    exact Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hd
  have he := orderOf_eq_one_iff.mp hone
  have hba : b.val=a.val⁻¹ := eq_inv_of_mul_eq_one_right he
  exact hnc (by rw [hba]; exact (Commute.refl _).inv_right)

private theorem sl2_involutions_conjugate {K : Type*} [Field K] [Finite K] [CharP K 2]
    (a b : SL(2,K)) (ha : orderOf a=2) (hb : orderOf b=2) : IsConj a b := by
  let e := Theory.PSL2.sl2QuotientEquiv K
  have h := Theory.PSL2.involutions_isConj (e a) (e b)
    ((e.orderOf_eq a).trans ha) ((e.orderOf_eq b).trans hb)
  simpa only [MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply]
    using e.symm.toMonoidHom.map_isConj h

private theorem sl2_sylow_commute {K : Type*} [Field K] [Finite K] [CharP K 2]
    (P : Sylow 2 SL(2,K)) (u v : SL(2,K)) (hu : u∈P) (hv : v∈P) : Commute u v := by
  let e := Matrix.SpecialLinearGroup.sylowEquivAdditive K 2 P
  have h : (⟨u,hu⟩:P)*(⟨v,hv⟩:P)=(⟨v,hv⟩:P)*(⟨u,hu⟩:P) := by
    apply e.symm.injective
    simp only [map_mul]
    exact mul_comm _ _
  exact congrArg Subtype.val h

private theorem sl2_sylow_sup {K : Type*} [Field K] [Finite K] [CharP K 2]
    (P Q : Sylow 2 SL(2,K)) (a b : SL(2,K))
    (ha : a∈P) (hb : b∈Q) (hn : ¬Commute a b) :
    (P:Subgroup SL(2,K))⊔Q=⊤ := by
  by_contra hne
  have hle := Matrix.SpecialLinearGroup.overgroup_le_sylowNormalizer P le_sup_left hne
  have hQN : (Q:Subgroup SL(2,K))≤normalizer (P:Set SL(2,K)) := le_sup_right.trans hle
  have hQP : (Q:Subgroup SL(2,K))≤P := by
    have h := Q.isPGroup'.inf_normalizer_sylow P
    rw [inf_eq_left.mpr hQN] at h
    exact inf_eq_left.mp h.symm
  exact hn (sl2_sylow_commute P a b ha (hQP hb))

/-- A three-center subgroup with central point radical and an SL₂ image
has commuting conjugate transvections with different center lines. -/
theorem commuting_conjugates_distinct_centers_of_sl2_image
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (L : Subgroup (pointLocal (F:=F)))
    (f : L →* SL(2,K)) (hf : Function.Surjective f)
    (hfq : ∀ u v:L, f u=f v ↔ pointQuotient u.val=pointQuotient v.val)
    (hcentral : L⊓pointRadical≤center (pointLocal (F:=F)))
    (a b c : L) (ha : IsB1 a.val.val) (hb : IsB1 b.val.val) (hc : IsB1 c.val.val)
    (haq : f a≠1) (hbq : f b≠1) (hcq : f c≠1)
    (hab : ¬Commute (f a) (f b))
    (hout : ¬ movedSpace c.val.val≤movedSpace a.val.val⊔movedSpace b.val.val) :
    ∃ u v:L, IsConj a u ∧ IsConj a v ∧ Commute u.val.val v.val.val ∧
      movedSpace u.val.val≠movedSpace v.val.val := by
  classical
  let j : L →* Sp F := pointLocal.subtype.comp L.subtype
  have horder (u:L) (hu:IsB1 (j u)) (huq:f u≠1) : orderOf (f u)=2 := by
    apply orderOf_eq_prime _ huq
    rw [←map_pow]
    have hus : u^2=1 := by
      apply Subtype.ext
      apply Subtype.ext
      change (j u)^2=1
      simpa only [hu.1] using pow_orderOf_eq_one (j u)
    rw [hus,map_one]
  have huniq (u v:L) (hu:IsB1 (j u)) (hv:IsB1 (j v))
      (huq:f u≠1) (he:f u=f v) : u=v := by
    apply Subtype.ext
    apply eq_of_isB1_same_pointQuotient u.val v.val hu hv
    · intro hh
      apply huq
      simpa only [map_one] using (hfq u 1).mpr (by simpa only [Subgroup.coe_one,map_one] using hh)
    · exact (hfq u v).mp he
    · apply hcentral
      refine ⟨L.mul_mem (L.inv_mem u.property) v.property,?_⟩
      change pointQuotient (u.val⁻¹*v.val)=1
      rw [map_mul,map_inv,(hfq u v).mp he,inv_mul_cancel]
  have hconj (u v:L) (hu:IsB1 (j u)) (hv:IsB1 (j v))
      (huq:f u≠1) (hvq:f v≠1) : IsConj u v := by
    obtain ⟨q,hq⟩ := isConj_iff.mp (sl2_involutions_conjugate (f u) (f v)
      (horder u hu huq) (horder v hv hvq))
    obtain ⟨g,rfl⟩ := hf q
    refine isConj_iff.mpr ⟨g,huniq (g*u*g⁻¹) v ?_ hv ?_ ?_⟩
    · simpa only [map_mul,map_inv] using (isB1_conj_iff (j g) (j u)).mpr hu
    · rw [map_mul,map_mul,map_inv,hq]
      exact hvq
    · simpa only [map_mul,map_inv] using hq
  by_contra hno
  push Not at hno
  have hline (u v:L) (hu:IsConj a u) (hv:IsConj a v)
      (huv:Commute (j u) (j v)) : movedSpace (j u)=movedSpace (j v) := hno u v hu hv huv
  let W := movedSpace (j a)⊔movedSpace (j b)
  let R : Subgroup L := (stabilizer W).comap j
  have hstable (u:L) (hu:movedSpace (j u)≤W) : u∈R := by
    apply (mem_stabilizer_iff W (j u)).mpr
    intro x hx
    have hm : (j u) • x-x∈W := hu ⟨x,rfl⟩
    have he : (j u) • x=((j u) • x-x)+x := by abel
    rw [he]
    exact W.add_mem hm hx
  have hSylow (u:L) (hu:IsB1 (j u)) (huq:f u≠1) : ∃ P:Sylow 2 SL(2,K), f u∈P := by
    have hp:IsPGroup 2 (zpowers (f u)) := IsPGroup.of_card (n:=1) (by
      rw [Nat.card_zpowers,horder u hu huq,pow_one])
    obtain ⟨P,hP⟩ := hp.exists_le_sylow
    exact ⟨P,hP (mem_zpowers (f u))⟩
  obtain ⟨P,haP⟩ := hSylow a ha haq
  obtain ⟨Q,hbQ⟩ := hSylow b hb hbq
  have hcover (u:L) (hu:IsB1 (j u)) (huq:f u≠1) (huconj:IsConj a u)
      (huW:movedSpace (j u)≤W) (S:Sylow 2 SL(2,K)) (huS:f u∈S) :
      (S:Subgroup SL(2,K))≤R.map f := by
    intro t ht
    by_cases ht1:t=1
    · rw [ht1]
      exact (R.map f).one_mem
    have ht2:t^2=1 := congrArg Subtype.val
      (Matrix.SpecialLinearGroup.twoSubgroup_pow_two (S:Subgroup SL(2,K)) S.isPGroup' ⟨t,ht⟩)
    obtain ⟨q,hq⟩ := isConj_iff.mp (sl2_involutions_conjugate (f u) t
      (horder u hu huq) (orderOf_eq_prime ht2 ht1))
    obtain ⟨g,rfl⟩ := hf q
    let v:L := g*u*g⁻¹
    have hvf:f v=t := by simpa only [v,map_mul,map_inv] using hq
    have hv:IsB1 (j v) := by
      simpa only [v,map_mul,map_inv] using (isB1_conj_iff (j g) (j u)).mpr hu
    have hcomm : Commute (j u) (j v) := by
      apply Commute.map _ pointLocal.subtype
      apply pointQuotient_commute_lift u.val v.val hu hv
      have hscomm : f (u*v)=f (v*u) := by
        simpa only [map_mul] using (sl2_sylow_commute S (f u) (f v) huS (hvf.symm ▸ ht)).eq
      change pointQuotient u.val*pointQuotient v.val=pointQuotient v.val*pointQuotient u.val
      simpa only [Subgroup.coe_mul,map_mul] using (hfq (u*v) (v*u)).mp hscomm
    have hvconj:IsConj a v := huconj.trans (isConj_iff.mpr ⟨g,rfl⟩)
    have hvR:v∈R := hstable v ((hline u v huconj hvconj hcomm).symm.le.trans huW)
    exact ⟨v,hvR,hvf⟩
  have hmap:R.map f=⊤ := top_unique (by
    rw [←sl2_sylow_sup P Q (f a) (f b) haP hbQ hab]
    exact sup_le (hcover a ha haq (IsConj.refl _) le_sup_left P haP)
      (hcover b hb hbq (hconj a b ha hb haq hbq) le_sup_right Q hbQ))
  obtain ⟨k,hk⟩ := isConj_iff.mp (hconj a c ha hc haq hcq)
  obtain ⟨g,hg,hgf⟩ := (show f k∈R.map f by rw [hmap]; exact mem_top _)
  have hfc : f (g*a*g⁻¹)=f c := by
    simp only [map_mul,map_inv,hgf]
    simpa only [map_mul,map_inv] using congrArg f hk
  have hgc:g*a*g⁻¹=c := huniq _ c (by
      simpa only [map_mul,map_inv] using (isB1_conj_iff (j g) (j a)).mpr ha) hc
    (hfc ▸ hcq) hfc
  have hW : W.map (toLinear (j g)).toLinearMap=W := hg
  apply hout
  change movedSpace (j c)≤W
  rw [←hgc,map_mul,map_mul,map_inv,movedSpace_conj,←hW]
  exact Submodule.map_mono (show movedSpace (j a)≤W from le_sup_left)

namespace ThreeCenterConfiguration
variable {X : Subgroup (Sp F)} {a : Sp F}

omit [Finite F] [CharP F 2] in
private theorem third_center_outside_pair (D : ThreeCenterConfiguration X a) :
    ¬ movedSpace D.thirdLocal.val≤movedSpace D.firstLocal.val⊔movedSpace D.secondLocal.val := by
  have hma := movedSpace_eq_span_center a D.center D.parameter D.center_ne_zero
    D.parameter_ne_zero D.formula
  let U := Submodule.span F (Set.range ![D.center,(D.x:Sp F) • D.center])
  have haU : movedSpace a≤U := by
    rw [hma]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (Submodule.subset_span ⟨0,rfl⟩))
  have hbU : movedSpace ((D.x:Sp F)*a*(D.x:Sp F)⁻¹)≤U := by
    rw [movedSpace_conj,hma,Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro z ⟨u,hu,rfl⟩
    have hu:u=D.center := Set.mem_singleton_iff.mp hu
    rw [hu]
    exact Submodule.subset_span ⟨1,rfl⟩
  intro hle
  change movedSpace (D.frame*((D.y:Sp F)*a*(D.y:Sp F)⁻¹)*D.frame⁻¹)≤
    movedSpace (D.frame*a*D.frame⁻¹)⊔
      movedSpace (D.frame*((D.x:Sp F)*a*(D.x:Sp F)⁻¹)*D.frame⁻¹) at hle
  rw [movedSpace_conj D.frame,movedSpace_conj D.frame,movedSpace_conj D.frame,←Submodule.map_sup] at hle
  have hraw := (Submodule.map_le_map_iff_of_injective (toLinear D.frame).injective _ _).mp hle
  apply D.third_outside
  apply (hraw.trans (sup_le haU hbU))
  rw [movedSpace_conj]
  exact ⟨D.center,by rw [hma]; exact Submodule.subset_span rfl,rfl⟩

/-- The original three-center configuration supplies the same-coset
commuting transvection whose product is c₂. The quotient alternatives and
both lifting steps are fully discharged. -/
theorem exists_commuting_coset_witness {n:ℕ} (hF:Nat.card F=2^n)
    (D : ThreeCenterConfiguration X a) (ha:IsB1 a)
    (han:a∈normalizer (X:Set (Sp F))) :
    ∃ b:Sp F, IsB1 b ∧ a⁻¹*b∈X ∧ Commute a b ∧ a*b∈X ∧ IsC2 (a*b) := by
  classical
  by_contra hno
  obtain ⟨k,hk,_,⟨e⟩⟩ := D.quotientImage_sl2_of_no_coset_witness hF ha han hno
  let f : D.localGenerated →* SL(2,GaloisField 2 k) :=
    e.toMonoidHom.comp D.generatedQuotient
  have hf : Function.Surjective f := e.surjective.comp D.generatedQuotient_surjective
  have hfq (u v:D.localGenerated) : f u=f v ↔ pointQuotient u.val=pointQuotient v.val := by
    constructor
    · intro h
      exact congrArg Subtype.val (e.injective h)
    · intro h
      exact congrArg e (Subtype.ext h)
  let aL:D.localGenerated := ⟨D.firstLocal,subset_closure (by simp)⟩
  let bL:D.localGenerated := ⟨D.secondLocal,subset_closure (by simp)⟩
  let cL:D.localGenerated := ⟨D.thirdLocal,subset_closure (by simp)⟩
  have hneq (u:D.localGenerated) (hu:pointQuotient u.val≠1) : f u≠1 := by
    intro h
    apply hu
    have h1:f u=f 1 := by simpa only [map_one] using h
    simpa only [Subgroup.coe_one,map_one] using (hfq u 1).mp h1
  obtain ⟨u,v,hu,hv,hcomm,hdiff⟩ := commuting_conjugates_distinct_centers_of_sl2_image
    D.localGenerated f hf hfq (D.radicalIntersection_central_of_no_coset_witness ha han hno)
    aL bL cL (D.firstLocal_isB1 ha) (D.secondLocal_isB1 ha) (D.thirdLocal_isB1 ha)
    (hneq aL (D.first_second_quotient_ne_one ha).1)
    (hneq bL (D.first_second_quotient_ne_one ha).2)
    (hneq cL (D.third_quotient_ne_one_of_no_coset_witness ha han hno))
    (by
      intro hh
      apply D.first_second_quotient_noncommute ha
      change pointQuotient D.firstLocal*pointQuotient D.secondLocal=
        pointQuotient D.secondLocal*pointQuotient D.firstLocal
      have he:f (aL*bL)=f (bL*aL) := by simpa only [map_mul] using hh.eq
      simpa only [Subgroup.coe_mul,map_mul] using (hfq (aL*bL) (bL*aL)).mp he)
    D.third_center_outside_pair
  obtain ⟨r,hr⟩ := isConj_iff.mp hu
  obtain ⟨s,hs⟩ := isConj_iff.mp hv
  let w:D.localGenerated := r⁻¹*s
  let q:Sp F := D.frame⁻¹*w.val.val*D.frame
  let z:Sp F := D.frame⁻¹*r.val.val⁻¹
  let b:Sp F := z*v.val.val*z⁻¹
  have hru:r.val.val*D.firstLocal.val*r.val.val⁻¹=u.val.val :=
    congrArg (fun t:D.localGenerated => t.val.val) hr
  have hsv:s.val.val*D.firstLocal.val*s.val.val⁻¹=v.val.val :=
    congrArg (fun t:D.localGenerated => t.val.val) hs
  have hza:z*u.val.val*z⁻¹=a := by
    rw [←hru]
    change (D.frame⁻¹*r.val.val⁻¹)*(r.val.val*(D.frame*a*D.frame⁻¹)*r.val.val⁻¹)*
      (D.frame⁻¹*r.val.val⁻¹)⁻¹=a
    group
  have hqb:q*a*q⁻¹=b := by
    dsimp only [b]
    rw [←hsv]
    change (D.frame⁻¹*(r.val.val⁻¹*s.val.val)*D.frame)*a*
      (D.frame⁻¹*(r.val.val⁻¹*s.val.val)*D.frame)⁻¹=
      (D.frame⁻¹*r.val.val⁻¹)*(s.val.val*(D.frame*a*D.frame⁻¹)*s.val.val⁻¹)*
      (D.frame⁻¹*r.val.val⁻¹)⁻¹
    group
  have hqmem:q∈closure {a,(D.x:Sp F)*a*(D.x:Sp F)⁻¹,
      (D.y:Sp F)*a*(D.y:Sp F)⁻¹} := by
    obtain ⟨t,ht,he⟩ := D.localGenerated_map_le ⟨w.val,w.property,rfl⟩
    have hqt:q=t := by
      change D.frame⁻¹*w.val.val*D.frame=t
      change D.frame*t*D.frame⁻¹=w.val.val at he
      rw [←he]
      group
    exact hqt ▸ ht
  have hcos:a⁻¹*b∈X := by
    rw [←hqb]
    apply conjugate_in_coset_of_mem_closure X a han _ _ q hqmem
    intro t ht
    rcases ht with rfl|rfl|rfl
    · simp
    · exact D.conjugate_in_coset han D.x
    · exact D.conjugate_in_coset han D.y
  have hb:IsB1 b := hqb ▸ (isB1_conj_iff q a).mpr ha
  have hab:Commute a b := by
    have he := hcomm.map (MulAut.conj z).toMonoidHom
    change Commute (z*u.val.val*z⁻¹) b at he
    rwa [hza] at he
  have hmd:movedSpace a≠movedSpace b := by
    intro he
    apply hdiff
    apply Submodule.map_injective_of_injective (toLinear z).injective
    rw [←movedSpace_conj,←movedSpace_conj,hza]
    exact he
  exact hno ⟨b,hb,hcos,hab,isC2_mem_of_commuting_coset X a b ha hb hab hmd hcos⟩

end ThreeCenterConfiguration

/-- Every irreducible subgroup normalized by a transvection contains a
c₂ product of commuting transvections in that original normalizing coset. -/
theorem irreducible_normalized_exists_isC2 {n:ℕ} (hF:Nat.card F=2^n)
    (X:Subgroup (Sp F))
    (hi:Representation.IsIrreducible ((Representation.symplecticNatural 2).comp X.subtype))
    (a:Sp F) (ha:IsB1 a) (han:a∈normalizer (X:Set (Sp F))) :
    ∃ b:Sp F, IsB1 b ∧ a⁻¹*b∈X ∧ Commute a b ∧ a*b∈X ∧ IsC2 (a*b) := by
  obtain ⟨D⟩ := exists_threeCenterConfiguration X hi a ha
  exact D.exists_commuting_coset_witness hF ha han

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
