module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.HexadOuterComplement
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The core complement step of the original Todd splitting

For an elementary subgroup P of the original extraspecial core Q which
contains the marker line and is preserved by the original cubic X, coprime
action splits P as the marker line times [P,X]. If P has order 128 and meets
the original intersection E1 only in that line, the commutator is an
order-64 complement to E1 in Q. Every subgroup preserving P and X preserves
this literal commutator.

The constructed order-1080 hexad subgroup has trivial two-core, by its
actual A6 quotient and cubic kernel. Its outer extension is disjoint from
any two-subgroup that it normalizes: an element of such an intersection
centralizes X, hence lies in the inner subgroup and its two-core.
Together these facts construct a complement in the point-plane overlap
once the invariant elementary preimage P has been constructed.

Source: Aschbacher--Segev, The uniqueness of groups of type J4, Invent.
Math. 105 (1991), (4.8), printed p.599, DOI 10.1007/BF01232280.
The existence of P is still a source-module obligation. The conditional
ToddSplitting consumer retains that premise and the original quotient maps.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open LocalGeometry Sporadic.Mathieu
noncomputable section
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z) (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
  (X : Sylow 3 (CubicLift.subgroup e))

omit [Finite G] in
private theorem normalized_commutator (A B J : Subgroup G)
    (ha : J ≤ normalizer (A : Set G)) (hb : J ≤ normalizer (B : Set G)) :
    J ≤ normalizer (⁅A,B⁆ : Subgroup G) := by
  intro j hj
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (ha hj),
    mem_normalizer_iff_map_conj_eq.mp (hb hj)]

include h in
/-- The cubic commutator removes exactly the marker line from any stable
 elementary subgroup of the original core containing that line. -/
theorem core_elementary_cubic_splitting
    (P : Subgroup (centralizer z)) [IsElementaryAbelian 2 P]
    (hPQ : P ≤ core z) (hZP : center (centralizer z) ≤ P)
    (hXP : cubicSylowImage e X ≤ normalizer (P : Set (centralizer z))) :
    ⁅P,cubicSylowImage e X⁆ ≤ P ∧
      Disjoint (center (centralizer z)) ⁅P,cubicSylowImage e X⁆ ∧
      center (centralizer z) ⊔ ⁅P,cubicSylowImage e X⁆ = P ∧
      2 * Nat.card (⁅P,cubicSylowImage e X⁆ : Subgroup (centralizer z)) = Nat.card P := by
  let A := cubicSylowImage e X
  let : Normalizes A P := ⟨hXP⟩
  have hfix : fixedPointSubgroup A P = (center (centralizer z)).subgroupOf P := by
    ext u
    constructor
    · intro hu
      have hc : (⟨u.val,hPQ u.property⟩ : core z) ∈
          (Subgroup.centralizer (A : Set (centralizer z))).subgroupOf (core z) := by
        intro a ha
        have hh := congrArg Subtype.val (hu ⟨a,ha⟩)
        change a*u.val*a⁻¹=u.val at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh)
      rw [core_cubic_centralizer h e X] at hc
      rw [←core_center_eq_centralizer_center h]
      exact mem_map_of_mem (core z).subtype hc
    · intro hu a
      apply Subtype.ext
      change a.val*u.val*a.val⁻¹=u.val
      have hc : a.val*u.val=u.val*a.val := mem_center_iff.mp hu a.val
      rw [hc,mul_inv_cancel_right]
  have hcop : Nat.Coprime (Nat.card A) (Nat.card P) := by
    rw [SourceComparison.cubicSylowImage_card h e X]
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup (p := 2) (G := P)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hc := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (A := A) (G := P) (Group.isSolvable_of_comm (fun x y : P => mul_comm x y))
    hcop inferInstance
  have hm := commutatorAction_subgroup_conj_map_eq_commutator P A hXP
  have hgen := congrArg (map P.subtype) hc.sup_eq_top
  rw [Subgroup.map_sup,hfix,map_subgroupOf_eq_of_le hZP,hm,←MonoidHom.range_eq_map,range_subtype] at hgen
  have hdis : Disjoint (center (centralizer z)) ⁅P,A⁆ := by
    apply disjoint_def.mpr
    intro x hxZ hxU
    obtain ⟨u,hu,rfl⟩ := hm.symm ▸ hxU
    have hh := disjoint_def.mp hc.disjoint (hfix.symm ▸ hxZ) hu
    exact congrArg Subtype.val hh
  have hZc : Nat.card (center (centralizer z))=2 := by
    rw [←core_center_eq_centralizer_center h,
      card_map_of_injective (core z).subtype_injective]
    let := h.extraspecial
    exact IsExtraspecial.center_order_p 2 (core z)
  refine ⟨le_normalizer_iff_commutator_le_left.mp hXP,hdis,hgen,?_⟩
  have he := card_sup_eq_mul_of_normalizes_of_disjoint
    (center (centralizer z)) ⁅P,A⁆ le_normalizer_of_normal hdis
  rw [hgen,hZc] at he
  exact he.symm

include h in
/-- A stable maximal singular preimage yields an invariant complement to
 the original maximal elementary intersection, by taking its cubic commutator. -/
theorem core_invariant_complement_of_elementary_preimage
    (E1 P J : Subgroup (centralizer z)) [IsElementaryAbelian 2 P]
    (hE1Q : E1 ≤ core z) (hE1c : Nat.card E1=128)
    (hPQ : P ≤ core z) (hPc : Nat.card P=128)
    (hEP : E1 ⊓ P = center (centralizer z))
    (hXJ : cubicSylowImage e X ≤ J)
    (hJN : J ≤ fullCubicNormalizer e X)
    (hJP : J ≤ normalizer (P : Set (centralizer z))) :
    let U := ⁅P,cubicSylowImage e X⁆
    U ≤ core z ∧ IsElementaryAbelian 2 U ∧ Nat.card U=64 ∧
      J ≤ normalizer (U : Set (centralizer z)) ∧
      Disjoint E1 U ∧ E1 ⊔ U = core z ∧
      (E1.subgroupOf (core z)).IsComplement' (U.subgroupOf (core z)) := by
  intro U
  have hZP : center (centralizer z) ≤ P := hEP ▸ inf_le_right
  obtain ⟨hUP,hZU,hgen,hUc⟩ := core_elementary_cubic_splitting h e X P hPQ hZP (hXJ.trans hJP)
  have hUQ : U ≤ core z := hUP.trans hPQ
  have hU64 : Nat.card U=64 := by change 2 * Nat.card U=Nat.card P at hUc; rw [hPc] at hUc; omega
  have hEU : Disjoint E1 U := by
    apply disjoint_def.mpr
    intro x hxE hxU
    exact disjoint_def.mp hZU (hEP ▸ ⟨hxE,hUP hxU⟩) hxU
  have hEn : (E1.subgroupOf (core z)).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hE1Q).mpr
    apply le_normalizer_iff_commutator_le_right.mpr
    have hcomm : ⁅core z,core z⁆ ≤ center (centralizer z) := by
      rw [←core_center_eq_centralizer_center h,←map_subtype_commutator]
      apply map_mono
      let := h.extraspecial
      exact (IsExtraspecial.quotient_elementary_abelian 2 (core z)).commutator_le_center_of_central_quotient
    exact (commutator_mono le_rfl hE1Q).trans (hcomm.trans (hEP ▸ inf_le_left))
  let := hEn
  have hcomp : (E1.subgroupOf (core z)).IsComplement' (U.subgroupOf (core z)) := by
    apply isComplement'_of_card_mul_and_disjoint
    · rw [Nat.card_congr (subgroupOfEquivOfLe hE1Q).toEquiv,
        Nat.card_congr (subgroupOfEquivOfLe hUQ).toEquiv,hE1c,hU64,h.core_card]
      norm_num
    · apply disjoint_def.mpr
      intro x hx hy
      exact Subtype.ext (disjoint_def.mp hEU hx hy)
  have he := congrArg (map (core z).subtype) hcomp.sup_eq_top
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hE1Q,map_subgroupOf_eq_of_le hUQ,
    ←MonoidHom.range_eq_map,range_subtype] at he
  exact ⟨hUQ,IsElementaryAbelian.of_injective (inclusion hUP) (inclusion_injective hUP),
    hU64,normalized_commutator P (cubicSylowImage e X) J hJP hJN,hEU,he,hcomp⟩

/-- The order-64 core complement and a subgroup avoiding the two-group E Q
 give the required complement in the point-plane overlap. -/
theorem overlap_complement_of_core_complement
    (E Q U J H : Subgroup G) (hEH : E ≤ H) (hQH : Q ≤ H) (hJH : J ≤ H)
    (hUQ : U ≤ Q) (hJU : J ≤ normalizer (U : Set G))
    (hE : Nat.card E=2048) (hU : Nat.card U=64) (hJ : Nat.card J=2160)
    (hH : Nat.card H=283115520)
    (hdis : Disjoint (E ⊔ Q) J) (hEU : Disjoint (E ⊓ Q) U) :
    (E.subgroupOf H).IsComplement' ((U ⊔ J).subgroupOf H) := by
  have hUJ : Disjoint U J := hdis.mono_left (hUQ.trans le_sup_right)
  have hUc : Nat.card (U ⊔ J : Subgroup G)=138240 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint U J hJU hUJ,hU,hJ]
  have hEUJ : Disjoint E (U ⊔ J) := by
    apply disjoint_def.mpr
    intro x hxE hxUJ
    have hx : x ∈ (U : Set G) * (J : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left U J hJU]
      exact hxUJ
    obtain ⟨u,hu,j,hj,rfl⟩ := hx
    have hjEQ : j ∈ E ⊔ Q := by
      have hh := (E ⊔ Q).mul_mem
        ((E ⊔ Q).inv_mem ((le_sup_right : Q ≤ E ⊔ Q) (hUQ hu)))
        ((le_sup_left : E ≤ E ⊔ Q) hxE)
      simpa only [inv_mul_cancel_left] using hh
    have hj1 : j=1 := disjoint_def.mp hdis hjEQ hj
    change u*j ∈ E at hxE
    change u*j=1
    rw [hj1,mul_one] at hxE ⊢
    exact disjoint_def.mp hEU ⟨hxE,hUQ hu⟩ hu
  apply isComplement'_of_card_mul_and_disjoint
  · rw [Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (sup_le (hUQ.trans hQH) hJH)).toEquiv,
      hE,hUc,hH]
  · apply disjoint_def.mpr
    intro x hx hy
    exact Subtype.ext (disjoint_def.mp hEUJ hx hy)

include h in
/-- The perfect hexad subgroup has no nontrivial normal two-subgroup. -/
theorem fullCubic_hexad_twoCore
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (A : Subgroup (fullCubicCentralizer e X))
    (hAc : Nat.card A=1080)
    (him : A.map (fullCubicSimpleProjection h e X)=hexadSectionImage hB) :
    pCore 2 A = ⊥ := by
  let j := (MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)
  have hj : Function.Injective j :=
    (MulAction.stabilizer M22 B).subtype_injective.comp (m22HexadSection_injective hB)
  let q : A →* j.range := ((fullCubicSimpleProjection h e X).comp A.subtype).codRestrict _
    (fun a => him.le (mem_map_of_mem _ a.property))
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨x,hx,he⟩ := him.ge a.property
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  have hjc : Nat.card j.range=360 := by
    have hc : Nat.card j.range=Nat.card (alternatingGroup (Fin 6)) :=
      (Nat.card_congr (Equiv.ofInjective j hj)).symm
    rw [hc,nat_card_alternatingGroup]
    norm_num
  have hkc : Nat.card q.ker=3 := by
    have hh := q.ker.card_mul_index
    rw [index_ker,MonoidHom.range_eq_top.mpr hq,card_top,hjc,hAc] at hh
    omega
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup j.range := (MonoidHom.ofInjective hj).symm.isSimpleGroup
  let P := pCore 2 A
  have hp : IsPGroup 2 P := pCore_isPGroup
  let : (P.map q).Normal := Subgroup.Normal.map inferInstance q hq
  have hm : P.map q = ⊥ := by
    rcases (inferInstance : (P.map q).Normal).eq_bot_or_eq_top with hb|ht
    · exact hb
    have h2 := (hp.map q).of_equiv ((MulEquiv.subgroupCongr ht).trans topEquiv)
    obtain ⟨n,hn⟩ := h2.exists_card_eq
    rw [hjc] at hn
    have hd : 5 ∣ 2^n := by rw [←hn]; norm_num
    have hh := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) hd
    norm_num at hh
  have hle : P ≤ q.ker := by
    simpa only [MonoidHom.comap_bot] using (map_le_iff_le_comap.mp hm.le)
  have h3 : IsPGroup 3 q.ker := IsPGroup.of_card (n := 1) (by rw [hkc]; norm_num)
  exact le_bot_iff.mp ((le_inf le_rfl hle).trans
    (hp.disjoint_of_coprime h3 (by decide)).eq_bot.le)

include h in
/-- The actual outer extension avoids every two-subgroup it normalizes. -/
theorem fullCubic_hexad_disjoint_normal_two
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (A : Subgroup (fullCubicCentralizer e X))
    (hAc : Nat.card A=1080)
    (him : A.map (fullCubicSimpleProjection h e X)=hexadSectionImage hB)
    (v : fullCubicNormalizer e X) (hv : orderOf v=2)
    (hvo : v.val ∉ fullCubicCentralizer e X)
    (hvA : v.val ∈ normalizer (A.map (fullCubicCentralizer e X).subtype : Set (centralizer z)))
    (N : Subgroup (centralizer z)) (hN : IsPGroup 2 N)
    (hXJ : cubicSylowImage e X ≤ A.map (fullCubicCentralizer e X).subtype ⊔ zpowers v.val)
    (hJN : A.map (fullCubicCentralizer e X).subtype ⊔ zpowers v.val ≤ normalizer (N : Set (centralizer z))) :
    Disjoint N (A.map (fullCubicCentralizer e X).subtype ⊔ zpowers v.val) := by
  classical
  let A0 := A.map (fullCubicCentralizer e X).subtype
  let J := A0 ⊔ zpowers v.val
  let Y := cubicSylowImage e X
  have hA0C : A0 ≤ fullCubicCentralizer e X := map_subtype_le A
  have hJY : J ≤ normalizer (Y : Set (centralizer z)) :=
    sup_le (hA0C.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr v.property)
  have hNY : Disjoint N Y := hN.disjoint_of_coprime
    (IsPGroup.of_card (p := 3) (n := 1) (by rw [SourceComparison.cubicSylowImage_card h e X]; norm_num))
    (by decide)
  have hNC : N ⊓ J ≤ fullCubicCentralizer e X := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    exact (le_inf
      ((commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hXJ.trans hJN)))
      (le_normalizer_iff_commutator_le_right.mp (inf_le_right.trans hJY))).trans hNY.eq_bot.le
  have hJC : J ⊓ fullCubicCentralizer e X = A0 := by
    apply le_antisymm
    · rintro x ⟨hxJ,hxC⟩
      have hx : x ∈ (A0 : Set (centralizer z)) * (zpowers v.val : Set (centralizer z)) := by
        rw [←coe_mul_of_right_le_normalizer_left A0 (zpowers v.val) (zpowers_le.mpr hvA)]
        exact hxJ
      obtain ⟨a,ha,b,hb,rfl⟩ := hx
      have hvo2 : orderOf v.val=2 := (orderOf_coe v).trans hv
      change b ∈ zpowers v.val at hb
      rw [mem_zpowers_iff_mem_range_orderOf,hvo2] at hb
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hb
      have hi2 := Finset.mem_range.mp hi
      have hi' : i=0 ∨ i=1 := by omega
      rcases hi' with rfl|rfl
      · simpa using ha
      · have hh := (fullCubicCentralizer e X).mul_mem
          ((fullCubicCentralizer e X).inv_mem (hA0C ha)) hxC
        exact (hvo (by simpa using hh)).elim
    · exact le_inf le_sup_left hA0C
  have hNA : N ⊓ J ≤ A0 := (le_inf inf_le_right hNC).trans hJC.le
  let N0 := N.comap ((fullCubicCentralizer e X).subtype.comp A.subtype)
  let : N0.Normal := by
    constructor
    intro x hx a
    exact (mem_normalizer_iff.mp (hJN ((le_sup_left : A0 ≤ J) (mem_map_of_mem _ a.property))) x.val.val).mp hx
  let k : N0 →* N := {
    toFun x := ⟨x.val.val.val,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hki : Function.Injective k := by
    intro x y he
    exact Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun n : N => n.val) he)))
  have hN0 : IsPGroup 2 N0 := hN.of_injective k hki
  have hN0bot : N0=⊥ := by
    apply le_bot_iff.mp
    rw [←fullCubic_hexad_twoCore h e X hB A hAc him]
    exact le_sSup ⟨inferInstance,hN0⟩
  apply disjoint_def.mpr
  intro x hxN hxJ
  obtain ⟨a,ha,rfl⟩ := hNA ⟨hxN,hxJ⟩
  have he : (⟨a,ha⟩ : A)=1 := mem_bot.mp (hN0bot ▸ hxN)
  exact congrArg (fun y : A => y.val.val) he

end
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
