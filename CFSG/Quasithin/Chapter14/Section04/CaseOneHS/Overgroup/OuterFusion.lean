module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.OuterGeometry
public import Theory.GroupTheory.InvolutionFusionCover

/-!
# The actual transfer conjugator in the HS outer branch

The centralizer C_L(r) has order divisible by seven, so no ambient
 conjugate of r lies in V, whose nonidentity elements have centralizers
 conjugate to H of order 15360. Ambient simplicity and Thompson transfer
 put a conjugate in T∩L−P. Conjugacy of involutions in the original L/P
 then supplies an actual L-conjugator placing it in PU−P.

All actors, quotient maps and conjugators remain in the original group.
 The later exclusion of placement in U and the extremal-centralizer
 contradiction remain to be proved; this is not the order-eight exclusion.
Source: Aschbacher--Smith, proof of 14.3.33(3), printed p.1005.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- The point centralizer in the outer branch has no factor seven in its order. -/
theorem point_card_of_core_card
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (hc : Nat.card (F.H.pCoreIn 2) = 128) : Nat.card F.H = 15360 := by
  have hcore : Nat.card (pCore 2 F.H) = 128 := by
    rw [←card_map_of_injective F.H.subtype_injective]
    exact hc
  obtain ⟨e⟩ := s.quotient F
  have hquot : Nat.card (F.H ⧸ pCore 2 F.H) = 120 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  have hh := (pCore 2 F.H).card_mul_index
  rw [hcore,index_eq_card,hquot] at hh
  omega

/-- No ambient conjugate of the constructed outer involution belongs to V.
Its actual L-centralizer has a seven-element, whereas C_G(v) does not. -/
theorem outer_involution_not_fused_into_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (hcard : Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 8)
    (r : G) (hr : r ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) (hrL : r ∉ L)
    (hr2 : orderOf r = 2) (hdis : ∀ l ∈ L, ⁅r,l⁆ ∈ V)
    (v : G) (hv : v ∈ V) : ¬ IsConj r v := by
  intro hfuse
  let := h.chosen.elementary
  obtain ⟨z,hz,hpoint,hH⟩ := source_point_centralizer F
  have hzV : z ∈ V := F.le_seed 1 (hpoint ▸ mem_zpowers z)
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz
  have hr1 : r ≠ 1 := by intro he; simp [he] at hr2
  have hv1 : v ≠ 1 := by
    intro he
    obtain ⟨g,hg⟩ := isConj_iff.mp hfuse
    exact hr1 ((MulAut.conj g).injective (hg.trans (he.trans (map_one _).symm)))
  obtain ⟨l,_,hl⟩ := h.vector_transitive hv hzV hv1 hz1
  have hrz : IsConj r z := hfuse.trans (isConj_iff.mpr ⟨l,hl⟩)
  obtain ⟨g,hg⟩ := isConj_iff.mp hrz
  let C := L ⊓ centralizer ({r} : Set G)
  let f := (MulAut.conj g).toMonoidHom
  have hCH : C.map f ≤ F.H := by
    rintro a ⟨c,hc,rfl⟩
    rw [hH]
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg f (mem_centralizer_singleton_iff.mp hc.2)
    simpa only [map_mul,show f r = z from hg] using he
  have hdvd := card_dvd_of_le hCH
  rw [card_map_of_injective (MulAut.conj g).injective] at hdvd
  have hcc : Nat.card C = 1344 := outer_involution_actor_centralizer_card h structural alternatives F s hne
    x hx hx3 r hr hrL hdis
  have hQ : Nat.card (F.H.pCoreIn 2) = 128 := by
    rw [point_core_card_eq_sixteen_mul_cubic_centralizer h structural alternatives F s hne x hx hx3,hcard]
  rw [hcc,point_card_of_core_card F s hQ] at hdvd
  norm_num at hdvd

/-- Ambient simplicity supplies the actual transfer conjugate in T∩L−P.
The remaining source argument must place it in PU and exclude extremality. -/
theorem exists_outer_involution_and_inner_conjugate
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (hcard : Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 8) :
    ∃ r y : G, r ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) ∧ r ∉ L ∧
      orderOf r = 2 ∧ (∀ l ∈ L, ⁅r,l⁆ ∈ V) ∧
      (∀ p ∈ L.pCoreIn 2, r*p*r⁻¹ = p⁻¹) ∧
      y ∈ (T : Subgroup G) ⊓ L ∧ y ∉ L.pCoreIn 2 ∧ IsConj r y := by
  let := h.chosen.elementary
  let := h.source.simpleQTKE.simple
  obtain ⟨r,hr,hrL,hr2,hd⟩ := exists_outer_involution h structural alternatives F s hne x hx hx3 hcard
  obtain ⟨y,hy,hry⟩ := T.exists_isConj_mem_of_index_two_ambient
    (index_ne_two_of_nonabelian_simple h.source.simpleQTKE.nonabelian)
    (L.subgroupOf (T : Subgroup G)) (inner_sylow_index_two h structural alternatives F s hne x hx hx3 hcard) r hr2
  have hyP : (y:G) ∉ L.pCoreIn 2 := by
    intro hyP
    have hy2 : (y:G)^2 = 1 := by
      obtain ⟨g,hg⟩ := isConj_iff.mp hry
      rw [←hg,conj_pow]
      have hh : r^2=1 := hr2 ▸ pow_orderOf_eq_one r
      rw [hh,mul_one,mul_inv_cancel]
    have hyV := (centerSpan_square_kernel_and_card h structural alternatives F s hne).1 y
      ((centerSpan_eq_core h structural alternatives F s hne).symm ▸ hyP) |>.mp hy2
    exact outer_involution_not_fused_into_seed h structural alternatives F s hne x hx hx3 hcard
      r hr hrL hr2 hd y hyV hry
  exact ⟨r,y,hr,hrL,hr2,hd,outer_cubic_inverts_core h structural alternatives F s hne x hx hx3 r hr hrL,
    ⟨y.property,hy⟩,hyP,hry⟩

/-- Conjugation in the original L places an involution outside P into PU.
Only the natural quotient conjugacy is used, and its conjugator is lifted
through the original quotient map. -/
theorem actor_involution_conjugate_into_core_closure
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (y : G) (hy : y ∈ L) (hy2 : orderOf y = 2) (hyP : y ∉ L.pCoreIn 2) :
    ∃ l : G, l ∈ L ∧ l*y*l⁻¹ ∈ L.pCoreIn 2 ⊔ F.U ∧ l*y*l⁻¹ ∉ L.pCoreIn 2 := by
  let := h.chosen.elementary
  let e := h.naturalMarking.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hmem (a : L) : f a = 1 ↔ (a:G) ∈ L.pCoreIn 2 := by
    change a ∈ f.ker ↔ _
    rw [hk]
    constructor
    · exact fun ha => mem_map_of_mem L.subtype ha
    · rintro ⟨b,hb,he⟩
      exact (Subtype.ext he : b = a) ▸ hb
  let yL : L := ⟨y,hy⟩
  have hy1 : f yL ≠ 1 := fun he => hyP ((hmem yL).mp he)
  have hyq : f yL * f yL = 1 := by
    rw [←map_mul]
    have he : yL*yL = 1 := Subtype.ext (by
      change y*y=1
      simpa only [pow_two,hy2] using pow_orderOf_eq_one y)
    rw [he,map_one]
  have hnot : ¬ F.U ≤ L.pCoreIn 2 := by
    intro hu
    have hh := centerSpan_inf_closure_card h structural alternatives F s hne
    rw [centerSpan_eq_core h structural alternatives F s hne,inf_eq_right.mpr hu,s.core_shape.card] at hh
    omega
  obtain ⟨a,ha,haP⟩ := SetLike.not_le_iff_exists.mp hnot
  let aL : L := ⟨a,closure_le_actor h structural alternatives F s hne ha⟩
  have ha1 : f aL ≠ 1 := fun he => haP ((hmem aL).mp he)
  have haq : f aL * f aL = 1 := by
    rw [←map_mul]
    apply (hmem _).mpr
    let : Fact (IsPGroup 2 F.U) := ⟨IsPGroup.of_card (n := 6) s.core_shape.card⟩
    have hh := mem_map_of_mem F.U.subtype (pth_power_mem_frattini_of_isPGroup (p:=2) (⟨a,ha⟩ : F.U))
    rw [closure_frattini h structural alternatives F hne] at hh
    have hp := ((seed_le_centerSpan h F).trans
      (centerSpan_eq_core h structural alternatives F s hne).le) (F.le_seed 1 hh)
    change a^2 ∈ L.pCoreIn 2 at hp
    change a*a ∈ L.pCoreIn 2
    simpa only [pow_two] using hp
  obtain ⟨b,hb⟩ := BinaryLinearThree.FourGroupGeometry.FixedSpaces.exists_involution_conjugator (f yL) hy1 hyq
  obtain ⟨c,hc⟩ := BinaryLinearThree.FourGroupGeometry.FixedSpaces.exists_involution_conjugator (f aL) ha1 haq
  have hconj : (c*b⁻¹)*f yL*(c*b⁻¹)⁻¹ = f aL := by
    have hb' : b⁻¹*f yL*b = BinaryLinearThree.FourGroupGeometry.FixedSpaces.involution := by
      calc
        b⁻¹*f yL*b = b⁻¹*(f yL*b) := by group
        _ = b⁻¹*(b*BinaryLinearThree.FourGroupGeometry.FixedSpaces.involution) := by rw [hb]
        _ = _ := by group
    calc
      (c*b⁻¹)*f yL*(c*b⁻¹)⁻¹ = c*(b⁻¹*f yL*b)*c⁻¹ := by group
      _ = c*BinaryLinearThree.FourGroupGeometry.FixedSpaces.involution*c⁻¹ := by rw [hb']
      _ = f aL := by rw [←hc,mul_inv_cancel_right]
  obtain ⟨l,hl⟩ := hf (c*b⁻¹)
  have hq : f (l*yL*l⁻¹) = f aL := by rw [map_mul,map_mul,map_inv,hl,hconj]
  have hP : ((l:G)*y*(l:G)⁻¹)*a⁻¹ ∈ L.pCoreIn 2 := by
    apply (hmem ((l*yL*l⁻¹)*aL⁻¹)).mp
    rw [map_mul,map_inv,hq,mul_inv_cancel]
  have hjoin : (l:G)*y*(l:G)⁻¹ ∈ L.pCoreIn 2 ⊔ F.U := by
    have hh := (L.pCoreIn 2 ⊔ F.U).mul_mem (mem_sup_left hP) (mem_sup_right ha)
    simpa only [inv_mul_cancel_right] using hh
  refine ⟨l,l.property,hjoin,?_⟩
  intro hh
  exact ha1 (hq.symm.trans ((hmem (l*yL*l⁻¹)).mpr hh))

/-- The actual outer involution and an actual ambient conjugator into PU−P,
with inversion, displacement and seed-fusion properties retained. -/
theorem exists_outer_involution_and_point_conjugate
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (hcard : Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 8) :
    ∃ r g : G, r ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) ∧ r ∉ L ∧
      orderOf r = 2 ∧ (∀ l ∈ L, ⁅r,l⁆ ∈ V) ∧
      (∀ p ∈ L.pCoreIn 2, r*p*r⁻¹ = p⁻¹) ∧
      g⁻¹*r*g ∈ L.pCoreIn 2 ⊔ F.U ∧ g⁻¹*r*g ∉ L.pCoreIn 2 ∧
      (∀ v ∈ V, ¬ IsConj r v) := by
  obtain ⟨r,y,hr,hrL,hr2,hd,hi,hy,hyP,hry⟩ :=
    exists_outer_involution_and_inner_conjugate h structural alternatives F s hne x hx hx3 hcard
  have hy2 : orderOf y = 2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hry
    exact (congrArg orderOf hg).symm.trans (((MulAut.conj g).orderOf_eq r).trans hr2)
  obtain ⟨l,_,hl,hlP⟩ := actor_involution_conjugate_into_core_closure h structural alternatives F s hne y hy.2 hy2 hyP
  obtain ⟨a,ha⟩ := isConj_iff.mp hry
  have he : ((l*a)⁻¹)⁻¹*r*(l*a)⁻¹ = l*y*l⁻¹ := by
    rw [←ha]
    group
  exact ⟨r,(l*a)⁻¹,hr,hrL,hr2,hd,hi,he.symm ▸ hl,he.symm ▸ hlP,
    fun v hv => outer_involution_not_fused_into_seed h structural alternatives F s hne x hx hx3 hcard r hr hrL hr2 hd v hv⟩


end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
