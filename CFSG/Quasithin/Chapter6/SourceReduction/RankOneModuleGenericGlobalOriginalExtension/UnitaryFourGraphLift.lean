module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourQuadraticQuotient

/-!
# Lifting the original U₄ graph quotient involution

The marked plane residual has an actual Levi section and Hermitian two-core.
Vanishing Hermitian H¹ conjugates any two sections by a core element. Applied
to an automorphism whose square is inner in the core, this corrects the
Levi action; the remaining square is central in the residual and hence trivial.

Transport to the original LS corrects each quotient involution by an element
of the same O₂(L). Its square lies in C_S(L), already proved trivial. Thus
every involution of LS/O₂(LS) lifts with its quotient class unchanged. In the
degree-two branch the canonical graph quotient actor has an actual involutory
representative, and LS splits over L. Conjugating into the genuine relative
Sylow gives an outer involution in the original S and a complement to T∩L.
The exact conjugation of its quotient marking is retained.

All statements preserve the arbitrary selected perfect R, broad original
marking, either input orientation and q=4. No equality S=T or R=O²(H) is used.
The companion Chapter 12 module includes reduced DGS restoration and the
literal prepared application. Identifying the full residual graph action and
both full-endpoint/Borel squares, DGS exhaustion, uniqueness and unconditional
GlobalExit remain necessary.
Source: Aschbacher--Smith F.1.12, pp.263--264; I.1.6(3), p.408 (Hermitian H¹);
5.2.6--7, pp.650--651 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.OriginalUnitaryFour.GraphLift

private theorem sections_conjugate
    {k E A V : Type*} [Field k] [Group E] [Group A] [AddCommGroup V] [Module k V]
    (f : E →* A) (ρ : Representation k A V) (e : f.ker ≃* Multiplicative V)
    (s t : A →* E) (hs : ∀ a, f (s a)=a) (ht : ∀ a, f (t a)=a)
    (he : ∀ a v, (e.symm (Multiplicative.ofAdd (ρ a v)) : E) =
      s a * (e.symm (Multiplicative.ofAdd v) : E) * (s a)⁻¹)
    [Subsingleton (Representation.OneCohomology.H1 ρ)] :
    ∃ v : f.ker, ∀ a, (v : E) * t a * (v : E)⁻¹ = s a := by
  let d (a : A) : f.ker := ⟨t a * (s a)⁻¹,by
    rw [MonoidHom.mem_ker,map_mul,map_inv,ht,hs,mul_inv_cancel]⟩
  let c (a : A) : V := (e (d a)).toAdd
  have hc (a : A) : (e.symm (Multiplicative.ofAdd (c a)) : E) = t a * (s a)⁻¹ :=
    congrArg Subtype.val (e.symm_apply_apply (d a))
  have hmul (a b : A) : c (a*b)=ρ a (c b)+c a := by
    apply Multiplicative.ofAdd.injective
    apply e.symm.injective
    apply Subtype.ext
    rw [hc,add_comm]
    change _ = (e.symm (Multiplicative.ofAdd (c a) * Multiplicative.ofAdd (ρ a (c b))) : E)
    rw [e.symm.map_mul]
    change _ = (e.symm (Multiplicative.ofAdd (c a)) : E) * (e.symm (Multiplicative.ofAdd (ρ a (c b))) : E)
    rw [hc,he,hc,map_mul,map_mul]
    group
  let z : Representation.OneCohomology.cocycles ρ := ⟨c,hmul⟩
  obtain ⟨w,hw⟩ := (Representation.OneCohomology.classMap_eq_zero_iff ρ z).mp (Subsingleton.elim _ _)
  let v : f.ker := e.symm (Multiplicative.ofAdd w)
  have hc' (a : A) : c a = ρ a w-w :=
    (congrArg (fun z : Representation.OneCohomology.cocycles ρ => z.val a) hw).symm
  refine ⟨v,fun a => ?_⟩
  have hh := hc a
  rw [hc',sub_eq_add_neg] at hh
  change (e.symm (Multiplicative.ofAdd (ρ a w) * (Multiplicative.ofAdd w)⁻¹) : E) = _ at hh
  rw [map_mul,map_inv] at hh
  change (e.symm (Multiplicative.ofAdd (ρ a w)) : E) * (v : E)⁻¹ = t a * (s a)⁻¹ at hh
  rw [he] at hh
  change s a * (v : E) * (s a)⁻¹ * (v : E)⁻¹ = t a * (s a)⁻¹ at hh
  have hcomm : Commute (s a * (v : E) * (s a)⁻¹) (v : E)⁻¹ := by
    have hh' := congrArg (fun x : f.ker => (x : E))
      (e.injective (show e (e.symm (Multiplicative.ofAdd (ρ a w)) * v⁻¹) =
        e (v⁻¹ * e.symm (Multiplicative.ofAdd (ρ a w))) by
          simp only [map_mul]; exact mul_comm _ _))
    change _ * _ = _ * _
    simpa only [coe_mul,coe_inv,he] using hh'
  rw [hcomm.eq] at hh
  calc
    (v : E) * t a * (v : E)⁻¹ = (v : E) * (t a * (s a)⁻¹) * s a * (v : E)⁻¹ := by group
    _ = (v : E) * ((v : E)⁻¹ * (s a * (v : E) * (s a)⁻¹)) * s a * (v : E)⁻¹ := by rw [hh]
    _ = s a := by group

private theorem involution_correction
    {k E A V : Type*} [Field k] [Group E] [Group A] [AddCommGroup V] [Module k V]
    (f : E →* A) (ρ : Representation k A V) (e : f.ker ≃* Multiplicative V)
    (s : A →* E) (hs : ∀ a, f (s a)=a)
    (he : ∀ a v, (e.symm (Multiplicative.ofAdd (ρ a v)) : E) =
      s a * (e.symm (Multiplicative.ofAdd v) : E) * (s a)⁻¹)
    [Subsingleton (Representation.OneCohomology.H1 ρ)]
    (hcenter : f.ker ⊓ center E = ⊥)
    (α : MulAut E) (β : MulAut A) (hα : ∀ x, f (α x)=β (f x))
    (z : f.ker) (hsq : α^2=MulAut.conj (z : E)) :
    ∃ v : f.ker, (MulAut.conj (v : E) * α)^2=1 := by
  let t := α.toMonoidHom.comp (s.comp β.symm.toMonoidHom)
  have ht (a : A) : f (t a)=a := by
    change f (α (s (β.symm a)))=a
    rw [hα,hs,β.apply_symm_apply]
  obtain ⟨v,hv⟩ := sections_conjugate f ρ e s t hs ht he
  let δ := MulAut.conj (v : E) * α
  have hδ (a : A) : δ (s a)=s (β a) := by
    have hh := hv (β a)
    change (v : E) * α (s (β.symm (β a))) * (v : E)⁻¹ = _ at hh
    rwa [β.symm_apply_apply] at hh
  have hβ (a : A) : β (β a)=a := by
    have hh := congrArg f (DFunLike.congr_fun hsq (s a))
    change f (α (α (s a)))=f ((z : E)*s a*(z : E)⁻¹) at hh
    simpa only [hα,hs,map_mul,map_inv,MonoidHom.mem_ker.mp z.property,
      one_mul,mul_one,inv_one] using hh
  let u : f.ker := ⟨(v : E)*α (v : E)*z,by
    rw [MonoidHom.mem_ker,map_mul,map_mul,hα,MonoidHom.mem_ker.mp v.property,
      MonoidHom.mem_ker.mp z.property,map_one,mul_one,one_mul]⟩
  have hδsq : δ^2=MulAut.conj (u : E) := by
    apply MulEquiv.ext
    intro x
    have hh := DFunLike.congr_fun hsq x
    change α (α x)=(z : E)*x*(z : E)⁻¹ at hh
    change (v : E)*α ((v : E)*α x*(v : E)⁻¹)*(v : E)⁻¹ =
      ((v : E)*α (v : E)*z)*x*((v : E)*α (v : E)*z)⁻¹
    rw [map_mul,map_mul,map_inv,hh]
    group
  have huS (a : A) : (u : E)*s a*(u : E)⁻¹=s a := by
    have hh := DFunLike.congr_fun hδsq (s a)
    change δ (δ (s a))=(u : E)*s a*(u : E)⁻¹ at hh
    rw [hδ,hδ,hβ] at hh
    exact hh.symm
  have hcomm (x y : f.ker) : (x : E)*(y : E)=(y : E)*(x : E) := by
    have hh : x*y=y*x := e.injective (by simp only [map_mul]; exact mul_comm _ _)
    exact congrArg Subtype.val hh
  have huz : (u : E) ∈ center E := by
    apply mem_center_iff.mpr
    intro x
    let y : f.ker := ⟨x*(s (f x))⁻¹,by rw [MonoidHom.mem_ker,map_mul,map_inv,hs,mul_inv_cancel]⟩
    have hx : x=(y : E)*s (f x) := by dsimp [y]; group
    have hh := mul_inv_eq_iff_eq_mul.mp (huS (f x))
    rw [hx]
    calc
      (y : E)*s (f x)*(u : E) = (y : E)*((u : E)*s (f x)) := by rw [mul_assoc,hh]
      _ = (u : E)*((y : E)*s (f x)) := by rw [←mul_assoc,hcomm,mul_assoc]
  have hu1 : (u : E)=1 := mem_bot.mp (hcenter.le ⟨u.property,huz⟩)
  exact ⟨v,by rw [hδsq,hu1,map_one]⟩


open ChapterF.GreenBook.LieModels.UnitaryFour
open Representation.OrthogonalFourMinus.FiniteModel

/-- Hermitian H¹ corrects an automorphism whose square is inner in the
plane core to an actual involution, by an element of that same core. -/
theorem plane_involution_correction (m : ℕ) (hm : 1 ≤ m)
    (α : MulAut (L2 m hm)) (z : pCore 2 (L2 m hm))
    (hsq : α^2=MulAut.conj (z : L2 m hm)) :
    ∃ v : pCore 2 (L2 m hm), (MulAut.conj (v : L2 m hm)*α)^2=1 := by
  let : NeZero m := ⟨by omega⟩
  let Q := pCore 2 (L2 m hm)
  let q := L2QuotientEquivSL2 m hm
  let f := q.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hk : f.ker=Q := by
    rw [MonoidHom.ker_comp_of_injective _ _ q.injective,QuotientGroup.ker_mk']
  let e := (MulEquiv.subgroupCongr hk).trans (L2TwoCoreEquiv m hm).symm
  let s := (L2Levi m hm).comp (planeSL2Equiv m).symm.toMonoidHom
  have hs (a : Matrix.SpecialLinearGroup (Fin 2) (Field m)) : f (s a)=a := by
    change L2QuotientEquivSL2 m hm (QuotientGroup.mk (L2Levi m hm ((planeSL2Equiv m).symm a)))=a
    rw [L2QuotientEquivSL2_mk,L2Restriction_levi,MulEquiv.apply_symm_apply]
  have he (a : Matrix.SpecialLinearGroup (Fin 2) (Field m)) (v : Space m) :
      (e.symm (Multiplicative.ofAdd (action m a v)) : L2 m hm) =
        s a * (e.symm (Multiplicative.ofAdd v) : L2 m hm) * (s a)⁻¹ := by
    have hh := congrArg Subtype.val (L2TwoCoreEquiv_conj m hm (s a) (Multiplicative.ofAdd v))
    change s a * (L2TwoCoreEquiv m hm (Multiplicative.ofAdd v)).val * (s a)⁻¹ =
      (L2TwoCoreEquiv m hm (Multiplicative.ofAdd (action m (f (s a)) v))).val at hh
    rw [hs] at hh
    exact hh.symm
  let β := MulAut.congr q (quotientAut Q α)
  have hα (x : L2 m hm) : f (α x)=β (f x) := by
    change q (QuotientGroup.mk' Q (α x)) = q ((quotientAut Q α) (q.symm (q (QuotientGroup.mk' Q x))))
    rw [q.symm_apply_apply,quotientAut_apply_mk]
  let : Subsingleton (Representation.OneCohomology.H1 (action m)) := action_H1_subsingleton m
  obtain ⟨v,hv⟩ := involution_correction f (action m) e s hs he
    (by rw [hk]; exact L2TwoCore_inf_center m hm) α β hα ⟨z.val,hk.ge z.property⟩ hsq
  exact ⟨⟨v.val,hk.le v.property⟩,hv⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.OriginalUnitaryFour.GraphLift

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (mark : OriginalUnitaryFour.Marking m hm point L R (sourceS L H))
include d h hTH hp mark

/-- Every original left quotient involution lifts after correction by the
same O₂(L). No complement or involution in the ambient group is assumed. -/
theorem original_unitaryFour_involution_correction
    (g : (L ⊔ sourceS L H : Subgroup G)) (hg : g.val^2 ∈ L.pCoreIn 2) :
    ∃ v ∈ L.pCoreIn 2, (v*g.val)^2=1 := by
  obtain ⟨_,⟨a⟩,_,_⟩ := d.original_unitaryFour_factors h hTH hp m hm point mark
  have hn : L ⊔ sourceS L H ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer ((sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes)
  let c := L.normalizerMonoidHom ⟨g.val,hn g.property⟩
  have hcval (x : L) : (c x).val=g.val*x.val*g.val⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
  let z : L := ⟨g.val^2,pCoreIn_le 2 L hg⟩
  have hz : z ∈ pCore 2 L := (mem_map_iff_mem L.subtype_injective).mp hg
  have hcsq : c^2=MulAut.conj z := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (c (c x)).val=(z*x*z⁻¹).val
    simp only [hcval,coe_mul,coe_inv]
    change g.val*(g.val*x.val*g.val⁻¹)*g.val⁻¹ = g.val^2*x.val*(g.val^2)⁻¹
    simp only [pow_two]
    group
  let α := MulAut.congr a c
  let za : pCore 2 (L2 m hm) := ⟨a z,by
    rw [←pCore_map_iso 2 a]
    exact mem_map_of_mem a.toMonoidHom hz⟩
  have hα : α^2=MulAut.conj za.val := by
    rw [←map_pow,hcsq,MulAut.congr_conj]
  obtain ⟨u,hu⟩ := OriginalUnitaryFour.GraphLift.plane_involution_correction m hm α za hα
  let v : L := a.symm u.val
  have hv : v ∈ pCore 2 L := by
    have he := mem_map_of_mem a.symm.toMonoidHom u.property
    rwa [pCore_map_iso] at he
  have hvc : (MulAut.conj v*c)^2=1 := by
    apply (MulAut.congr a).injective
    rw [map_pow,map_mul,MulAut.congr_conj,a.apply_symm_apply,map_one]
    exact hu
  let w := (v : G)*g.val
  have hwQ : w^2 ∈ L.pCoreIn 2 := by
    have hvG := mem_map_of_mem L.subtype hv
    have hgN := normalizer_le_normalizer_characteristic_image L (pCore 2 L) (hn g.property)
    have hconj := (mem_normalizer_iff.mp hgN v.val).mp hvG
    have hh := (L.pCoreIn 2).mul_mem ((L.pCoreIn 2).mul_mem hvG hconj) hg
    have he : w^2=(v : G)*(g.val*v.val*g.val⁻¹)*g.val^2 := by dsimp [w]; simp only [pow_two]; group
    rw [he]
    exact hh
  have hwC : w^2 ∈ centralizer (L : Set G) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    have he := congrArg Subtype.val (DFunLike.congr_fun hvc (⟨x,hx⟩ : L))
    change (v*(c (v*(c ⟨x,hx⟩)*v⁻¹))*v⁻¹).val=x at he
    simp only [coe_mul,coe_inv,hcval] at he
    have he' : w^2*x*(w^2)⁻¹=x := by
      calc
        w^2*x*(w^2)⁻¹ = (v : G)*(g.val*((v : G)*(g.val*x*g.val⁻¹)*(v : G)⁻¹)*g.val⁻¹)*(v : G)⁻¹ := by dsimp [w]; simp only [pow_two]; group
        _ = x := he
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  have hQS : L.pCoreIn 2 ≤ sourceS L H := by
    rw [←d.original_unitaryFour_left_core_eq h hTH hp m hm point mark]
    exact d.original_left_core_le_sourceS h hTH
  have hw1 : w^2=1 := mem_bot.mp
    ((d.original_unitaryFour_residual_centralizer_eq_bot h hTH hp m hm point mark).le ⟨hQS hwQ,hwC⟩)
  exact ⟨v.val,mem_map_of_mem L.subtype hv,hw1⟩


/-- The core correction preserves every original left quotient class. -/
theorem original_unitaryFour_same_coset_involution
    (g : (L ⊔ sourceS L H : Subgroup G)) (hg : g.val^2 ∈ L.pCoreIn 2) :
    ∃ t : (L ⊔ sourceS L H : Subgroup G), t.val^2=1 ∧
      QuotientGroup.mk' (pCore 2 (L ⊔ sourceS L H : Subgroup G)) t =
        QuotientGroup.mk' (pCore 2 (L ⊔ sourceS L H : Subgroup G)) g := by
  obtain ⟨v,hv,hvg⟩ := d.original_unitaryFour_involution_correction h hTH hp m hm point mark g hg
  let J := L ⊔ sourceS L H
  let u : J := ⟨v,(show L ≤ J from le_sup_left) (pCoreIn_le 2 L hv)⟩
  have hu : u ∈ pCore 2 J := by
    apply (mem_map_iff_mem J.subtype_injective).mp
    change v ∈ J.pCoreIn 2
    rw [d.original_unitaryFour_left_core_eq h hTH hp m hm point mark]
    exact hv
  refine ⟨u*g,hvg,?_⟩
  have he : QuotientGroup.mk' (pCore 2 J) u=1 := (QuotientGroup.eq_one_iff u).mpr hu
  rw [map_mul,he,one_mul]

/-- Every actual involution in LS/O₂(LS) lifts to an involution of the
same original LS, retaining its literal quotient representative. -/
theorem original_unitaryFour_quotient_involution_lifts
    (x : (L ⊔ sourceS L H : Subgroup G) ⧸ pCore 2 (L ⊔ sourceS L H : Subgroup G))
    (hx : orderOf x=2) :
    ∃ t : (L ⊔ sourceS L H : Subgroup G), orderOf t.val=2 ∧
      QuotientGroup.mk' (pCore 2 (L ⊔ sourceS L H : Subgroup G)) t=x := by
  let J := L ⊔ sourceS L H
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 J) x
  have hg : g.val^2 ∈ L.pCoreIn 2 := by
    have he : g^2 ∈ pCore 2 J := by
      apply (QuotientGroup.eq_one_iff (g^2)).mp
      change QuotientGroup.mk' (pCore 2 J) (g^2)=1
      rw [map_pow]
      have hh := pow_orderOf_eq_one (QuotientGroup.mk' (pCore 2 J) g)
      rwa [hx] at hh
    have he' := mem_map_of_mem J.subtype he
    change g.val^2 ∈ J.pCoreIn 2 at he'
    rwa [d.original_unitaryFour_left_core_eq h hTH hp m hm point mark] at he'
  obtain ⟨t,ht,he⟩ := d.original_unitaryFour_same_coset_involution h hTH hp m hm point mark g hg
  refine ⟨t,orderOf_eq_prime ht ?_,he⟩
  intro ht1
  have ht' : t=1 := Subtype.ext ht1
  rw [ht',map_one] at he
  rw [←he,orderOf_one] at hx
  omega

/-- The marked native graph quotient actor has an actual original
involutory representative outside L, with the same canonical action. -/
theorem original_unitaryFour_graph_involution
    (q : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group (MatrixField m))
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) :
    ∃ t : (L ⊔ sourceS L H : Subgroup G), t.val ∉ L ∧ orderOf t.val=2 ∧
      originalUnitaryFourJoinAction h hTH m q t =
        MulAut.congr (OriginalUnitaryFour.planeQuotient m hm) (Extension.L2QuotientAut m hm) := by
  obtain ⟨g,_,_,hact,horder⟩ := d.original_unitaryFour_graph_quotient_lift h hTH hp m hm point mark q hi
  obtain ⟨t,ht,he⟩ := d.original_unitaryFour_quotient_involution_lifts h hTH hp m hm point mark _ horder
  have ha : originalUnitaryFourJoinAction h hTH m q t=originalUnitaryFourJoinAction h hTH m q g := by
    have hh := congrArg (fun x => (d.originalUnitaryFourQuadraticQuotientEquiv h hTH hp m hm point mark q hi x).val) he
    simpa only [originalUnitaryFourQuadraticQuotientEquiv_mk] using hh
  refine ⟨t,?_,ht,ha.trans hact⟩
  intro htL
  have hl := originalUnitaryFourJoinAction_left h hTH m q (⟨t.val,htL⟩ : L)
  change originalUnitaryFourJoinAction h hTH m q t = _ at hl
  apply OriginalUnitaryFour.quadraticGraph_not_inner m hm
  refine ⟨q (QuotientGroup.mk' (pCore 2 L) ⟨t.val,htL⟩),?_⟩
  rw [←hl,ha,hact,OriginalUnitaryFour.planeQuotient_graph]
  rfl


omit d h hTH hp mark in
private theorem index_two_involution_complement
    {X : Type*} [Group X] [Finite X] (N : Subgroup X) (hi : N.index=2)
    (t : X) (ht : orderOf t=2) (hout : t ∉ N) :
    N.IsComplement' (zpowers t) := by
  classical
  apply isComplement'_of_card_mul_and_disjoint
  · rw [Nat.card_zpowers,ht,←hi,N.card_mul_index]
  · apply disjoint_iff_inf_le.mpr
    rintro x ⟨hx,hxt⟩
    change x ∈ N at hx
    change x ∈ zpowers t at hxt
    rw [mem_zpowers_iff_mem_range_orderOf,ht] at hxt
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hxt
    have hk2 := Finset.mem_range.mp hk
    interval_cases k
    · simp
    · exact (hout (by simpa only [pow_one] using hx)).elim

/-- The same original left join splits over L, with its graph-marked
involution as the actual complement generator. -/
theorem original_unitaryFour_left_split
    (q : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group (MatrixField m))
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) :
    ∃ t : (L ⊔ sourceS L H : Subgroup G), orderOf t.val=2 ∧
      (L.subgroupOf (L ⊔ sourceS L H)).IsComplement' (zpowers t) ∧
      originalUnitaryFourJoinAction h hTH m q t =
        MulAut.congr (OriginalUnitaryFour.planeQuotient m hm) (Extension.L2QuotientAut m hm) := by
  obtain ⟨t,hout,ht,ha⟩ := d.original_unitaryFour_graph_involution h hTH hp m hm point mark q hi
  have hidx : L.relIndex (L ⊔ sourceS L H)=2 := by
    let J := L ⊔ sourceS L H
    let : (L.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
      (sup_le L.le_normalizer ((sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes))
    have he := relIndex_sup_left ((sourceS L H).subgroupOf J) (L.subgroupOf J)
    rw [←subgroupOf_sup (show L ≤ J from le_sup_left)
      (show sourceS L H ≤ J from le_sup_right),relIndex_subgroupOf le_rfl,
      relIndex_subgroupOf (show sourceS L H ≤ J from le_sup_right)] at he
    rw [he,←inf_relIndex_right,inf_comm,d.left_intersection,hi]
  exact ⟨t,ht,index_two_involution_complement _ hidx t
    ((Subgroup.orderOf_coe t).symm.trans ht) hout,ha⟩

/-- The original S contains an outer involution. Its graph quotient
marking is retained up to the displayed conjugation in the same LS. -/
theorem original_unitaryFour_source_graph_involution
    (q : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group (MatrixField m))
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) :
    ∃ t : sourceS L H, t.val ∉ L ∧ orderOf t.val=2 ∧
      ∃ c : (L ⊔ sourceS L H : Subgroup G),
        originalUnitaryFourJoinAction h hTH m q (inclusion le_sup_right t) =
          originalUnitaryFourJoinAction h hTH m q c *
            (MulAut.congr (OriginalUnitaryFour.planeQuotient m hm) (Extension.L2QuotientAut m hm)) *
              (originalUnitaryFourJoinAction h hTH m q c)⁻¹ := by
  let J := L ⊔ sourceS L H
  obtain ⟨t,hout,ht,ha⟩ := d.original_unitaryFour_graph_involution h hTH hp m hm point mark q hi
  have htJ : orderOf t=2 := (Subgroup.orderOf_coe t).symm.trans ht
  have hcyc : IsPGroup 2 (zpowers t) := IsPGroup.iff_card.mpr
    ⟨1,by rw [Nat.card_zpowers,htJ,pow_one]⟩
  have hs : Chapter1.IsSylowIn 2 (sourceS L H)
      (ChapterF.Source.parabolic ![L,R] (sourceS L H) 0) :=
    (d.hypothesisF11 h hTH).sylow_parabolic 0
  obtain ⟨P,hP⟩ := hs.restrict (show sourceS L H ≤ J from le_sup_right)
    (show J ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 from le_sup_left)
  obtain ⟨Q,hQ⟩ := hcyc.exists_le_sylow
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq J Q P
  have hcP : c*t*c⁻¹ ∈ (P : Subgroup J) := by
    rw [←hc]
    exact ⟨t,hQ (mem_zpowers t),rfl⟩
  have hcS : (c : G)*t.val*(c : G)⁻¹ ∈ sourceS L H :=
    hP.le (mem_map_of_mem J.subtype hcP)
  let s : sourceS L H := ⟨(c : G)*t.val*(c : G)⁻¹,hcS⟩
  refine ⟨s,?_,?_,c,?_⟩
  · intro hL
    have hn : J ≤ normalizer (L : Set G) := sup_le L.le_normalizer
      ((sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes)
    exact hout ((mem_normalizer_iff.mp (hn c.property) t.val).mpr hL)
  · exact ((orderOf_injective (MulAut.conj c.val).toMonoidHom (MulAut.conj c.val).injective t.val)).trans ht
  · change originalUnitaryFourJoinAction h hTH m q (c*t*c⁻¹)=_
    rw [map_mul,map_mul,map_inv,ha]

/-- The actual original S is split over its inner Sylow T∩L. -/
theorem original_unitaryFour_source_split
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) :
    ∃ t : sourceS L H, orderOf t.val=2 ∧
      (((T : Subgroup G) ⊓ L).subgroupOf (sourceS L H)).IsComplement' (zpowers t) := by
  let q := d.originalUnitaryFourQuotientCoordinates h hTH hp m hm point mark
  obtain ⟨t,hout,ht,_⟩ := d.original_unitaryFour_source_graph_involution h hTH hp m hm point mark q hi
  exact ⟨t,ht,index_two_involution_complement _ hi t
    ((Subgroup.orderOf_coe t).symm.trans ht) (fun hx => hout hx.2)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
