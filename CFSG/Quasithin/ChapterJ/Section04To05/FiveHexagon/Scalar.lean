module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedTorus
public import Theory.GroupAction.SelfCentralizingOddInverter

/-!
# The scalar cyclic four in the original marked torus

The full action of the original I on the two order-five lines supplies an
actor which squares both coordinates. The prime-plane is self-centralizing,
and the marked involution zu inverts it. Hence its centralizing normalizer
acts faithfully. The scalar actor is central in that normalizer, has square
exactly zu, and has order four. In particular it centralizes the actual
opposite SL₂(5) already constructed from the two original five-subgroups.

Source: Aschbacher–Smith, discussion before J.4.8, printed p.443.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
open Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def squareFive {V:Type*} [Group V] [Finite V] (hV:Nat.card V=5) : MulAut V := by
  let : IsCyclic V := isCyclic_of_prime_card hV
  let hp : IsPGroup 5 V := IsPGroup.of_card (n:=1) hV
  exact { hp.powEquiv (n:=2) (by decide) with
    map_mul' := fun x y => by
      change (x*y)^2=x^2*y^2
      exact (show Commute x y from mul_comm' x y).mul_pow 2 }

private theorem squareFive_apply {V:Type*} [Group V] [Finite V] (hV:Nat.card V=5) (v:V) :
    squareFive hV v=v^2 := rfl

variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

/-- A scalar square map on the actual five-plane is realized inside the same I. -/
theorem exists_source_square_actor
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (hfusion : IsConj (sourceU e) c.z) :
    ∃ i:sourceI e, ∀ x∈edge B5 (sourceU e),(i:G)*x*(i:G)⁻¹=x^2 := by
  obtain ⟨hu,hi⟩ := source_inverter c B5 e hz hfive
  let hB := B5Image_card d.card_Z B5
  let hA := (source_three_fives c B5 (sourceU e) hu hfusion hi).1
  let a := sourceTorusEquiv c B5 e hz hfive hfusion
  let i := a.symm (squareFive hB,squareFive hA)
  have hpair : a i=(squareFive hB,squareFive hA) := a.apply_symm_apply _
  have hbase (b:G) (hb:b∈B5Image B5) : (i:G)*b*(i:G)⁻¹=b^2 := by
    have he := congrArg (fun f:MulAut (B5Image B5) × MulAut (fixedFive B5 (sourceU e)) =>
      ((f.1 ⟨b,hb⟩:B5Image B5):G)) hpair
    rw [sourceTorusEquiv_first] at he
    exact he
  have hfixed (b:G) (hb:b∈fixedFive B5 (sourceU e)) : (i:G)*b*(i:G)⁻¹=b^2 := by
    have he := congrArg (fun f:MulAut (B5Image B5) × MulAut (fixedFive B5 (sourceU e)) =>
      ((f.2 ⟨b,hb⟩:fixedFive B5 (sourceU e)):G)) hpair
    rw [sourceTorusEquiv_second] at he
    exact he
  refine ⟨i,?_⟩
  intro x hx
  have hnorm : fixedFive B5 (sourceU e)≤normalizer (B5Image B5 : Set G) :=
    (le_centralizer_iff.mp (central_edge B5 (sourceU e))).trans (Subgroup.centralizer_le_normalizer _)
  have hx' : x∈(B5Image B5 : Set G)*(fixedFive B5 (sourceU e) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hnorm]
    exact hx
  obtain ⟨b,hb,w,hw,rfl⟩ := hx'
  calc
    _ = ((i:G)*b*(i:G)⁻¹)*((i:G)*w*(i:G)⁻¹) := by group
    _ = b^2*w^2 := by rw [hbase b hb,hfixed w hw]
    _ = (b*w)^2 := (show Commute b w from (central_edge B5 (sourceU e) hb w hw).symm).mul_pow 2 |>.symm

omit [Finite G] in
private theorem commute_in_sourceI {x y:G} (hx:x∈sourceI e) (hy:y∈sourceI e) : Commute x y := by
  obtain ⟨a⟩ := sourceI_equiv e
  have he : (⟨x,hx⟩:sourceI e)*⟨y,hy⟩=⟨y,hy⟩*(⟨x,hx⟩:sourceI e) := by
    apply a.injective
    rw [map_mul,map_mul,mul_comm]
  exact congrArg Subtype.val he

/-- The actual diagonal scalar has order four, square zu, and centralizes
 the actual opposite SL₂(5), all in the same marked torus. -/
theorem exists_source_scalar_four
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (hfusion : IsConj (sourceU e) c.z) :
    ∃ i:G, i∈sourceI e ∧ orderOf i=4 ∧ i^2=c.z*sourceU e ∧
      i∈centralizer (oppositePair c B5 (sourceU e) : Set G) ∧
      ∀ x∈edge B5 (sourceU e),i*x*i⁻¹=x^2 := by
  obtain ⟨hu,hi⟩ := source_inverter c B5 e hz hfive
  obtain ⟨i,hisq⟩ := exists_source_square_actor c B5 e hz hfive hfusion
  let E := edge B5 (sourceU e)
  let t := c.z*sourceU e
  have hC : centralizer (E:Set G)=E := centralizer_base_fixed c B5 (sourceU e) hu hfusion hi
  have hodd : Odd (Nat.card E) := by
    rw [base_fixed_card c B5 (sourceU e) hu hfusion hi]
    decide
  have hinv : ∀x∈E,t*x*t⁻¹=x⁻¹ := product_inverts_edge c B5 (sourceU e) hu hfusion hi
  have htI : t∈sourceI e := (sourceI e).mul_mem (source_marks_mem c e hz).1
    (source_marks_mem c e hz).2
  have hIE : sourceI e≤centralizingNormalizer E t := by
    intro x hx
    exact ⟨(sourceI_normalizes_edge_and_opposite c B5 e hz hfive).1 hx,
      mem_centralizer_singleton_iff.mpr (commute_in_sourceI e hx htI).eq⟩
  let a : centralizingNormalizer E t := ⟨i,hIE i.property⟩
  let b : centralizingNormalizer E t := ⟨t,hIE htI⟩
  have ha : ∀x:E,centralizingNormalizerAction E t a x=x^2 := by
    intro x
    exact Subtype.ext (hisq x x.property)
  have hcentral := mem_center_of_power_action E t hC hodd hinv a 2 ha
  have hb : ∀x:E,centralizingNormalizerAction E t b x=x⁻¹ := by
    intro x
    exact Subtype.ext (hinv x x.property)
  have hab : a^2=b := by
    apply centralizingNormalizerAction_injective E t hC hodd hinv
    rw [map_pow]
    apply MulEquiv.ext
    intro x
    change centralizingNormalizerAction E t a (centralizingNormalizerAction E t a x)=
      centralizingNormalizerAction E t b x
    rw [ha,ha,hb,← pow_mul]
    apply eq_inv_iff_mul_eq_one.mpr
    change x^4*x=1
    rw [← pow_succ]
    let : IsElementaryAbelian 5 E := base_fixed_elementary c B5 (sourceU e) hu hfusion hi
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 5 E) x
  have hi2 : (i:G)^2=t := congrArg Subtype.val hab
  have htclass := (product_class c B5 (sourceU e) hu hfusion hi).2
  have ht2 : t^2=1 := by
    have hh := htclass.pow 2
    rw [(c.z_involution_of_card d.card_Z).2] at hh
    exact isConj_one_left.mp hh
  have htne : t≠1 := by
    intro hh
    have hz1 : c.z=1 := isConj_one_right.mp (hh ▸ htclass)
    exact (c.z_involution_of_card d.card_Z).1 hz1
  have hi4 : orderOf (i:G)=4 := by
    let : Fact (Nat.Prime 2) := ⟨by decide⟩
    apply orderOf_eq_prime_pow (p:=2) (n:=1)
    · simpa only [pow_one,hi2] using htne
    · change (i:G)^(2*2)=1
      rw [pow_mul,hi2,ht2]
  refine ⟨i,i.property,hi4,hi2,?_,hisq⟩
  intro x hx
  have hxC : x∈centralizingNormalizer E t :=
    ⟨opposite_pair_normalizes_edge c B5 (sourceU e) hu hfusion hi hx,
      (show oppositePair c B5 (sourceU e)≤centralizer ({t}:Set G) from
        sup_le inf_le_right inf_le_right) hx⟩
  exact congrArg Subtype.val (mem_center_iff.mp hcentral ⟨x,hxC⟩)

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
