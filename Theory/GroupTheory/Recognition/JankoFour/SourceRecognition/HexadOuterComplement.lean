module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.HexadComplement
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeHexadOuter
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.NormalizerInvolution
public import Theory.GroupTheory.NormalizingInvolutionCard
/-!
# Extending the marked hexad complement across its outer involution

The native involution preserves the exact A6 section. The original cubic
normalizer lifts it to an involution: the checked double-cover square
calculation puts a lift's square in the scalar cubic, and cubing that lift
removes this remaining odd part without changing its involutory image.
The canonical derived-subgroup description of HexadComplement then proves
that this lift normalizes the original perfect subgroup of order 1080.

Adjoining the involution gives an actual subgroup of order 2160 inside the
same point-plane overlap. It contains X and is disjoint from the marker
line, hence from the whole extraspecial core Q, since Q intersects the
cubic normalizer in that line. The original Aut(M22) projection has exactly
X as kernel on this subgroup and image of order 720. The involution and
native section markings are retained. MathieuJ4RecognitionApplication.
HexadOuterComplement discharges both perfectness and the original splitting
premise using the original marked Mathieu arguments.

This supplies the outer-extension step of Aschbacher--Segev (4.8), printed
p.599, Invent. Math. 105 (1991), DOI 10.1007/BF01232280. An invariant
complement to E1/Z in Q/Z and full Todd splitting are still required.
The double-cover square theorem is reused from the independent section 8
comparison family; it assumes no LocalData and uses only the stated split
involution in the original normalizer.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open LocalGeometry Sporadic.Mathieu LocalGeometry.LocalSubgroups
noncomputable section
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z) (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
  (X : Sylow 3 (CubicLift.subgroup e))

include h in
/-- A split outer fiber makes every design involution lift through the same full normalizer. -/
theorem fullCubic_design_involution_lift
    (s : fullCubicNormalizer e X) (hs : s^2=1) (hso : s.val ∉ fullCubicCentralizer e X)
    (t : m22DesignAut) (ht : orderOf t=2) :
    ∃ v : fullCubicNormalizer e X, orderOf v=2 ∧
      CubicLift.projection e v.val = m22DesignAutToAut t := by
  let s0 : SourceComparison.cubicNormalizerInH e X := s
  have hs0 : s0^2=1 := hs
  let q := QuotientGroup.mk' (SourceComparison.normalizerScalars e X)
  let f := SourceComparison.normalizerDoubleProjection h e X
  obtain ⟨n,hn⟩ := SourceComparison.cubicNormalizerProjection_surjective h e X
    (m22DesignAutToAut t)
  have hs' : (q s0)^2=1 := by rw [←map_pow,hs0,map_one]
  have hso' : f (q s0) ∉ MulAut.innerSubgroup M22 := by
    intro he
    exact hso ((SourceComparison.cubicNormalizer_inner_iff h e X s0).mp he)
  have ht2 : (m22DesignAutToAut t)^2=1 := by
    rw [←map_pow,show t^2=1 from ht ▸ pow_orderOf_eq_one t,map_one]
  have hn' : (f (q n))^2=1 := by
    change (SourceComparison.cubicNormalizerProjection e X n)^2=1
    rw [hn]
    exact ht2
  have hq := SourceComparison.OuterSquare.aut_square_one f
    (SourceComparison.normalizerDoubleProjection_surjective h e X)
    (SourceComparison.normalizerDoubleProjection_kernel_central h e X)
    (SourceComparison.normalizerDoubleProjection_kernel_card h e X)
    (q s0) hs' hso' (q n) hn'
  have hnA : n^2 ∈ SourceComparison.normalizerScalars e X :=
    (QuotientGroup.eq_one_iff _).mp (by change q (n^2)=1; rw [map_pow]; exact hq)
  have hc : Nat.card (SourceComparison.normalizerScalars e X)=3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (cubicSylowImage e X).le_normalizer).toEquiv,
      SourceComparison.cubicSylowImage_card h e X]
  have h6 : (n^2)^3=1 := by
    have hh := pow_card_eq_one' (x := (⟨n^2,hnA⟩ : SourceComparison.normalizerScalars e X))
    rw [hc] at hh
    exact congrArg Subtype.val hh
  have hv2 : (n^3)^2=1 := by simpa only [←pow_mul] using h6
  have hvimage : CubicLift.projection e (n^3).val=m22DesignAutToAut t := by
    change SourceComparison.cubicNormalizerProjection e X (n^3)=_
    rw [map_pow,hn,pow_succ,ht2,one_mul]
  have hvne : n^3 ≠ 1 := by
    intro he
    have hh : m22DesignAutToAut t=1 := by rw [←hvimage,he]; exact map_one _
    have hh' : t=1 := (map_eq_one_iff _ m22DesignAutToAut_injective).mp hh
    rw [hh',orderOf_one] at ht
    omega
  exact ⟨n^3,orderOf_eq_prime hv2 hvne,hvimage⟩

/-- Preservation of the same native A6 section preserves its canonical perfect lift. -/
theorem fullCubic_hexad_normalizes
    [Group.IsPerfect (fullCubicCentralizer e X)]
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (A : Subgroup (fullCubicCentralizer e X))
    (hAc : Nat.card A=1080) (hscalar : fullCubicScalar e X ≤ A)
    (him : A.map (fullCubicSimpleProjection h e X)=hexadSectionImage hB)
    (hgen : (fullCubicProjection h e X).ker ⊔ A=
      (hexadSectionImage hB).comap (fullCubicSimpleProjection h e X))
    (v : fullCubicNormalizer e X)
    (hinv : (hexadSectionImage hB).map (CubicLift.projection e v.val).toMonoidHom =
      hexadSectionImage hB) :
    v.val ∈ normalizer (A.map (fullCubicCentralizer e X).subtype : Set (centralizer z)) := by
  let u : MulAut (fullCubicCentralizer e X) :=
    (fullCubicCentralizer e X).normalizerMonoidHom
      ⟨v.val,normalizer_le_normalizer_centralizer (cubicSylowImage e X) v.property⟩
  let D := (hexadSectionImage hB).comap (fullCubicSimpleProjection h e X)
  have hu (c : fullCubicCentralizer e X) :
      fullCubicSimpleProjection h e X (u c) =
        CubicLift.projection e v.val (fullCubicSimpleProjection h e X c) := by
    exact SourceComparison.cubicNormalizerAction_projection h e X v c
  have hDle : D.map u.toMonoidHom ≤ D := by
    rintro c ⟨a,ha,rfl⟩
    change fullCubicSimpleProjection h e X (u a) ∈ hexadSectionImage hB
    rw [hu]
    exact hinv.le (mem_map_of_mem _ ha)
  have hD : D.map u.toMonoidHom=D := eq_of_le_of_card_ge hDle (by
    rw [card_map_of_injective (f := u.toMonoidHom) u.injective])
  have hder : ⁅D,D⁆=A := by
    rw [←map_subtype_commutator]
    exact fullCubic_hexad_subgroup_derived h e X hB A hAc hscalar him hgen
  have hAu : A.map u.toMonoidHom=A := by
    rw [←hder,map_commutator,hD]
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_map]
  have hm : (MulAut.conj v.val).toMonoidHom.comp (fullCubicCentralizer e X).subtype =
      (fullCubicCentralizer e X).subtype.comp u.toMonoidHom := by rfl
  change A.map ((MulAut.conj v.val).toMonoidHom.comp (fullCubicCentralizer e X).subtype) = _
  rw [hm,←map_map,hAu]

include h in
/-- Inside the original cubic normalizer, avoiding the marker also avoids the entire core. -/
theorem fullCubic_disjoint_core_of_marker (D : Subgroup (centralizer z))
    (hDN : D ≤ fullCubicNormalizer e X) (hDZ : Disjoint (center (centralizer z)) D) :
    Disjoint (core z) D := by
  apply disjoint_def.mpr
  intro x hxQ hxD
  exact disjoint_def.mp hDZ ((fullCubicNormalizer_core_intersection h e X).le ⟨hxQ,hDN hxD⟩) hxD

/-- Extend the original order-1080 subgroup across a compatible outer involution.
The resulting order-2160 subgroup still avoids the original marker line. -/
theorem fullCubic_hexad_outer_complement
    [Group.IsPerfect (fullCubicCentralizer e X)]
    (s : fullCubicNormalizer e X) (hs : s^2=1) (hso : s.val ∉ fullCubicCentralizer e X)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (M : Subgroup G)
    (hM : M.subgroupOf (centralizer z)=(designStabilizer B).comap (CubicLift.projection e)) :
    ∃ (A : Subgroup (fullCubicCentralizer e X)) (v : fullCubicNormalizer e X)
        (t : m22DesignAut),
      Nat.card A=1080 ∧ Group.IsPerfect A ∧ fullCubicScalar e X ≤ A ∧
      A.map (fullCubicSimpleProjection h e X)=hexadSectionImage hB ∧
      orderOf t=2 ∧ t.val ∉ M22 ∧ t • B=B ∧
      t • Classical.choose (exists_m22Hexad_complementary_point hB) =
        Classical.choose (exists_m22Hexad_complementary_point hB) ∧
      CubicLift.projection e v.val=m22DesignAutToAut t ∧
      orderOf v=2 ∧ v.val ∉ fullCubicCentralizer e X ∧
      v.val ∈ normalizer (A.map (fullCubicCentralizer e X).subtype : Set (centralizer z)) ∧
      let D := A.map (fullCubicCentralizer e X).subtype ⊔ zpowers v.val
      Nat.card D=2160 ∧ Disjoint (center (centralizer z)) D ∧
      Disjoint (core z) D ∧ D ≤ fullCubicNormalizer e X ∧
      cubicSylowImage e X ≤ D ∧ D ≤ M.subgroupOf (centralizer z) := by
  classical
  obtain ⟨A,hAc,hscalar,hdis,him,hgen,hAM⟩ := fullCubic_hexad_overlap_complement h e X hB M hM
  obtain ⟨t,ht,hto,htB,htp⟩ := exists_hexad_outer_involution hB
  obtain ⟨v,hv,hvt⟩ := fullCubic_design_involution_lift h e X s hs hso t ht
  have hvC : v.val ∉ fullCubicCentralizer e X := by
    intro he
    have hi := (SourceComparison.cubicNormalizer_inner_iff h e X v).mpr he
    change CubicLift.projection e v.val ∈ MulAut.innerSubgroup M22 at hi
    rw [hvt] at hi
    obtain ⟨a,ha⟩ := hi
    exact hto ((M22OuterCentralizers.induced_inner_iff t).mp ⟨a,ha.symm⟩)
  have hvA := fullCubic_hexad_normalizes h e X hB A hAc hscalar him hgen v (by
    rw [hvt]
    exact hexadSectionImage_stable hB t htB htp)
  let A0 := A.map (fullCubicCentralizer e X).subtype
  let D := A0 ⊔ zpowers v.val
  have hv2 : v.val^2=1 := congrArg Subtype.val (hv ▸ pow_orderOf_eq_one v)
  have hA0C : A0 ≤ fullCubicCentralizer e X := map_subtype_le A
  have hvout : v.val ∉ A0 := fun hvA => hvC (hA0C hvA)
  have hDc : Nat.card D=2160 := by
    rw [card_sup_zpowers_of_normalizing_involution A0 v.val hv2 hvout hvA,
      card_map_of_injective (fullCubicCentralizer e X).subtype_injective,hAc]
  have hA0dis : Disjoint (center (centralizer z)) A0 := by
    apply disjoint_def.mpr
    rintro x hx ⟨a,ha,rfl⟩
    have hz : a ∈ (fullCubicProjection h e X).ker := by
      rw [fullCubicProjection_ker]
      exact hx
    exact congrArg Subtype.val (disjoint_def.mp hdis hz ha)
  have hDdis : Disjoint (center (centralizer z)) D := by
    apply disjoint_def.mpr
    intro x hxZ hxD
    have hm : x ∈ (A0 : Set (centralizer z)) * (zpowers v.val : Set (centralizer z)) := by
      rw [←coe_mul_of_right_le_normalizer_left A0 (zpowers v.val) (zpowers_le.mpr hvA)]
      exact hxD
    obtain ⟨a,ha,b,hb,rfl⟩ := hm
    have hvo : orderOf v.val=2 := (Subgroup.orderOf_coe v).trans hv
    change b ∈ zpowers v.val at hb
    rw [mem_zpowers_iff_mem_range_orderOf,hvo] at hb
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hb
    have hi2 := Finset.mem_range.mp hi
    have hi' : i=0 ∨ i=1 := by omega
    rcases hi' with rfl|rfl
    · simpa using disjoint_def.mp hA0dis (by simpa using hxZ) ha
    · have hxC : a*v.val ∈ fullCubicCentralizer e X := center_le_centralizer _ (by simpa using hxZ)
      have hh := (fullCubicCentralizer e X).mul_mem
        ((fullCubicCentralizer e X).inv_mem (hA0C ha)) hxC
      exact (hvC (by simpa using hh)).elim
  have hXD : cubicSylowImage e X ≤ D := by
    intro x hx
    have hxC : x ∈ fullCubicCentralizer e X := SourceComparison.cubicSylowImage_le_centralizer h e X hx
    exact (le_sup_left : A0 ≤ D) ⟨⟨x,hxC⟩,hscalar hx,rfl⟩
  have hvM : v.val ∈ M.subgroupOf (centralizer z) := by
    rw [hM]
    change CubicLift.projection e v.val ∈ designStabilizer B
    rw [hvt]
    exact ⟨t,htB,rfl⟩
  have hDN : D ≤ fullCubicNormalizer e X :=
    sup_le (hA0C.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr v.property)
  have hDQ := fullCubic_disjoint_core_of_marker h e X D hDN hDdis
  exact ⟨A,v,t,hAc,fullCubic_hexad_subgroup_perfect h e X hB A hAc hscalar him,
    hscalar,him,ht,hto,htB,htp,hvt,hv,hvC,hvA,hDc,hDdis,hDQ,hDN,hXD,
    sup_le hAM (zpowers_le.mpr hvM)⟩
include h in
/-- The original automorphism quotient has exactly the retained cubic kernel
on the constructed subgroup; its image has order 720. -/
theorem fullCubic_marker_free_quotient (D : Subgroup (centralizer z))
    (hDc : Nat.card D=2160) (hDQ : Disjoint (core z) D)
    (hXD : cubicSylowImage e X ≤ D) :
    ((CubicLift.projection e).comp D.subtype).ker=(cubicSylowImage e X).subgroupOf D ∧
      Nat.card (D.map (CubicLift.projection e))=720 := by
  let f := (CubicLift.projection e).comp D.subtype
  let q := QuotientGroup.mk' (core z)
  have hk : f.ker=(cubicSylowImage e X).subgroupOf D := by
    ext a
    change CubicLift.projection e a.val=1 ↔ a.val ∈ cubicSylowImage e X
    constructor
    · intro ha
      have hi : q a.val ∈ e.projection.ker := ha
      obtain ⟨x,hx,hxa⟩ := (cubicSylow_map_coreQuotient h e X).ge hi
      have hQ : a.val*x⁻¹ ∈ core z := (QuotientGroup.eq_one_iff _).mp (by
        change q (a.val*x⁻¹)=1
        rw [map_mul,map_inv,hxa,mul_inv_cancel])
      have hD : a.val*x⁻¹ ∈ D := D.mul_mem a.property (D.inv_mem (hXD hx))
      have he : a.val=x := mul_inv_eq_one.mp (disjoint_def.mp hDQ hQ hD)
      exact he.symm ▸ hx
    · intro ha
      have hi := (cubicSylow_map_coreQuotient h e X).le (mem_map_of_mem q ha)
      exact hi
  refine ⟨hk,?_⟩
  have hkc : Nat.card f.ker=3 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe hXD).toEquiv,
      SourceComparison.cubicSylowImage_card h e X]
  have hc := f.ker.card_mul_index
  rw [hkc,hDc,index_ker] at hc
  have hr : f.range=D.map (CubicLift.projection e) := by
    rw [MonoidHom.range_comp,range_subtype]
  rw [hr] at hc
  omega

end
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
