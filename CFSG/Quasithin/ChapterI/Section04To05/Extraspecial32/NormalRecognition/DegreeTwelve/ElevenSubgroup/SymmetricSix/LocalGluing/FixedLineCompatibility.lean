module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.LocalGluing.Transport
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.LocalGluing.FixedLineCompatibility.SquareRoots
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection.Cardinality

/-!
# Compatible fixed vectors in the conjugate fusion cores

The nonzero fixed vector b in [A(z),X] has a square root t*u, with t a
cubic conjugate of b. The earlier square-root theorem places every square
root of z in Q_z; conjugation and core reciprocity then exclude b from Q_u. The
order-six centralizer quotient then identifies the common fixed vector at
the two ends of the chain. This uses the literal canonical fusion cores.

For the marked source configuration we also recover b = (g*z*g⁻¹)*z and
membership of g*z*g⁻¹ in Q_z ∩ Q_u, including the choice u = a.u*z.
`selected_compatible_fixed_vector` discharges square-root containment using
relative quaternion normality and the selected inverter. Only the two
`CubicFourData` inputs remain explicit; their construction and the final
Lemma 4.6 assembly belong to the local-gluing consumer.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemma 4.6, pp.40–41, using Lemmas 2.3–2.4.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.LocalGluing
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {z r q b : G} {X : Subgroup G}

/-- The earlier-source square-root assertion for all conjugates of z. -/
@[expose] public def ConjugateSquareRootsInCore (z : G) : Prop :=
  ∀ r : G, IsConj z r → ∀ w : G, w ^ 2 = r → w ∈ coreInG r

omit [Finite G] in

/-- The earlier assertion at z automatically holds at every ambient
conjugate; the core is the canonical intrinsic core throughout. -/
public theorem conjugateSquareRootsInCore_of_base
    (roots : ∀ w : G, w^2=z → w ∈ coreInG z) : ConjugateSquareRootsInCore z := by
  intro r hr w hw
  obtain ⟨g,rfl⟩ := isConj_iff.mp hr
  let e : G ≃* G := MulAut.conj g
  have hw' : (e.symm w)^2=z := by
    apply e.injective
    rw [map_pow,MulEquiv.apply_symm_apply]
    simpa only [e, MulAut.conj_apply] using hw
  have hm := mem_map_of_mem e.toMonoidHom (roots (e.symm w) hw')
  simpa only [map_coreInG, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    e, MulAut.conj_apply] using hm

omit [Finite G] in
private theorem fusion_data (d : FusionEightData z) (hr : IsConj z r) :
    FusionEightData r := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hr
  exact fusionEightData_map (MulAut.conj g) d

private theorem core_reciprocity_base (h : Hypotheses z) (hr : IsConj z r)
    (hm : r ∈ coreInG z) : z ∈ coreInG r := by
  by_cases he : r = z
  · exact he ▸ h.involution_mem_coreInG
  obtain ⟨g, rfl⟩ := isConj_iff.mp hr
  have hi := (NonnormalRecognition.involution_mem_coreIntersection h g hm he).2
  rwa [map_coreInG] at hi

private theorem core_reciprocity (h : Hypotheses z) (hr : IsConj z r)
    (hq : IsConj z q) (hm : q ∈ coreInG r) : r ∈ coreInG q := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hr
  let e : G ≃* G := MulAut.conj g
  have hm' : e.symm q ∈ coreInG z := by
    have hm0 : q ∈ (coreInG z).map e.toMonoidHom := (map_coreInG e z).symm ▸ hm
    exact mem_map_equiv.mp hm0
  have hz' : IsConj z (e.symm z) := isConj_iff.mpr ⟨g⁻¹, by simp [e]⟩
  have hq' : IsConj z (e.symm q) := hz'.trans (e.symm.toMonoidHom.map_isConj hq)
  have hb := core_reciprocity_base h hq' hm'
  have hh := mem_map_of_mem e.toMonoidHom hb
  simpa only [map_coreInG, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, e, MulAut.conj_apply] using hh

private theorem commuting_square_one_eq_of_card_six {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 6) {v w : K} (hv : v*v=1) (hw : w*w=1)
    (hv1 : v ≠ 1) (hw1 : w ≠ 1) (hc : Commute v w) : v = w := by
  by_contra hne
  have hk := isKleinFour_closure_pair v w hv hw hv1 hw1 hne hc
  have hd := (closure ({v,w} : Set K)).card_subgroup_dvd_card
  rw [hk.card_four, hK] at hd
  norm_num at hd

private theorem product_mem_core_base (h : Hypotheses z) {v w : G}
    (hv : v ∈ Centralizer z) (hw : w ∈ Centralizer z)
    (hv2 : v*v=1) (hw2 : w*w=1) (hc : Commute v w)
    (hvQ : v ∉ coreInG z) (hwQ : w ∉ coreInG z) : v*w ∈ coreInG z := by
  let π : Centralizer z →* Centralizer z ⧸ Core z := QuotientGroup.mk' (Core z)
  let vH : Centralizer z := ⟨v,hv⟩
  let wH : Centralizer z := ⟨w,hw⟩
  have hn (x : Centralizer z) (hx : (x : G) ∉ coreInG z) : π x ≠ 1 := by
    intro he
    have hh : x ∈ Core z := (QuotientGroup.eq_one_iff x).mp he
    exact hx (mem_map_of_mem _ hh)
  have hs (x : Centralizer z) (hx : (x : G)*(x : G)=1) : π x * π x = 1 := by
    rw [← map_mul, show x*x=1 from Subtype.ext hx, map_one]
  have he := commuting_square_one_eq_of_card_six h.quotient_card
    (hs vH hv2) (hs wH hw2) (hn vH hvQ) (hn wH hwQ)
    (show Commute (π vH) (π wH) from by
      change π vH * π wH = π wH * π vH
      rw [← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext hc.eq))
  have hm : vH*wH ∈ Core z := (QuotientGroup.eq_one_iff _).mp (by
    change π (vH*wH)=1
    rw [map_mul, he, hs wH hw2])
  exact mem_map_of_mem _ hm

private theorem product_mem_core (h : Hypotheses z) (hr : IsConj z r) {v w : G}
    (hv : v ∈ Centralizer r) (hw : w ∈ Centralizer r)
    (hv2 : v*v=1) (hw2 : w*w=1) (hc : Commute v w)
    (hvQ : v ∉ coreInG r) (hwQ : w ∉ coreInG r) : v*w ∈ coreInG r := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hr
  let e : G ≃* G := MulAut.conj g
  have hc' (x : G) (hx : x ∈ Centralizer (e z)) : e.symm x ∈ Centralizer z := by
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using mem_centralizer_singleton_iff.mp hx
  have hs (x : G) (hx : x*x=1) : e.symm x * e.symm x = 1 := by
    rw [← map_mul, hx, map_one]
  have hn (x : G) (hx : x ∉ coreInG (e z)) : e.symm x ∉ coreInG z := by
    intro hm
    have hh := mem_map_of_mem e.toMonoidHom hm
    rw [map_coreInG, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hh
    exact hx hh
  have hh := product_mem_core_base h (hc' v hv) (hc' w hw) (hs v hv2) (hs w hw2)
    (show Commute (e.symm v) (e.symm w) from by
      change e.symm v * e.symm w = e.symm w * e.symm v
      rw [← map_mul, ← map_mul, hc.eq]) (hn v hvQ) (hn w hwQ)
  have hm := mem_map_of_mem e.toMonoidHom hh
  simpa only [map_coreInG, map_mul, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, e, MulAut.conj_apply] using hm

omit [Finite G] in
private theorem exists_cubic_generator (hc : Nat.card X = 3) :
    ∃ x : G, zpowers x = X ∧ x^3=1 := by
  let : IsCyclic X := isCyclic_of_prime_card hc
  obtain ⟨x,hx⟩ := IsCyclic.exists_generator (α := X)
  have hx3 : x^3=1 := hc ▸ pow_card_eq_one' (x := x)
  refine ⟨x, ?_, congrArg Subtype.val hx3⟩
  apply le_antisymm (zpowers_le.mpr x.property)
  intro t ht
  obtain ⟨n,hn⟩ := hx ⟨t,ht⟩
  exact ⟨n,congrArg Subtype.val hn⟩

omit [Finite G] in
/-- The square root used on p.40 is a cubic conjugate of b times q. -/
public theorem fixed_vector_square_root (k : CubicEightContext r q X)
    (p : CubicFourData r q X) (hb : b ∈ fixedLine r q X) :
    ∃ t : G, IsConj b t ∧ t ∈ movedFour r X ∧ (t*q)^2=b := by
  obtain ⟨x,hx,hx3⟩ := exists_cubic_generator k.cubic_card
  have hxX : x ∈ X := hx ▸ mem_zpowers x
  let t := x*b*x⁻¹
  have ht : t ∈ movedFour r X := (p.normalizes hxX b).mp hb.1
  have hq2 : q*q=1 := by simpa only [pow_two, k.involution_order] using pow_orderOf_eq_one q
  have hqx := k.inverts x hxX
  have hqb : q*b*q⁻¹=b := mul_inv_eq_iff_eq_mul.mpr
    (mem_centralizer_singleton_iff.mp hb.2).symm
  have hqt : q*t*q⁻¹=x⁻¹*b*x := by
    dsimp only [t]
    calc
      _ = (q*x*q⁻¹)*(q*b*q⁻¹)*(q*x*q⁻¹)⁻¹ := by group
      _ = x⁻¹*b*x := by rw [hqx,hqb,inv_inv]
  have hxx : x*x=x⁻¹ := mul_eq_one_iff_eq_inv.mp (by simpa only [pow_succ, pow_zero, one_mul] using hx3)
  have hxxi : x⁻¹*x⁻¹=x := by
    have hh := congrArg Inv.inv hxx
    simpa only [mul_inv_rev, inv_inv] using hh
  have hnorm : b*t*(x⁻¹*b*x)=1 := by
    calc
      _ = b*x*b*(x⁻¹*x⁻¹)*b*x := by dsimp [t]; group
      _ = (b*x)^3 := by rw [hxxi]; simp only [pow_succ, pow_zero]; group
      _ = 1 := p.cube hx hx3 hb.1
  have hs : (t*q)^2=t*(x⁻¹*b*x) := by
    calc
      _ = t*(q*t*q⁻¹)*(q*q) := by rw [pow_two]; group
      _ = t*(x⁻¹*b*x) := by rw [hqt,hq2,mul_one]
  refine ⟨t,isConj_iff.mpr ⟨x,rfl⟩,ht,?_⟩
  apply mul_left_cancel (a := b)
  rw [hs, ← mul_assoc, hnorm, p.square hb.1]

omit [Finite G] in
private theorem fusion_square (d : FusionEightData r) {v : G} (hv : v ∈ fusionCore r) : v^2=1 := by
  let := d.elementary
  exact elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv

/-- A fixed vector cannot lie in the opposite core: its square root would
then be a product of two elements of that core's elementary fusion eight. -/
public theorem fixed_vector_not_other_core (h : Hypotheses z) (d : FusionEightData z)
    (roots : ConjugateSquareRootsInCore z) (hr : IsConj z r) (hq : IsConj z q)
    (k : CubicEightContext r q X) (p : CubicFourData r q X)
    (hb : b ∈ fixedLine r q X) (hb1 : b ≠ 1) : b ∉ coreInG q := by
  intro hbQ
  have dr := fusion_data d hr
  have hbf : IsConj z b := hr.trans (dr.fusion b (p.moved_le hb.1) hb1)
  have hqQ := core_reciprocity h hq hbf hbQ
  obtain ⟨t,hbt,ht,hs⟩ := fixed_vector_square_root k p hb
  have hwQ := roots b hbf (t*q) hs
  have htQ : t ∈ coreInG b := (mul_mem_cancel_right hqQ).mp hwQ
  have hqb : IsConj b q := hbf.symm.trans hq
  have htF : t ∈ fusionCore b := subset_closure ⟨htQ,hbt⟩
  have hqF : q ∈ fusionCore b := subset_closure ⟨hqQ,hqb⟩
  have hwF := (fusionCore b).mul_mem htF hqF
  exact hb1 (hs.symm.trans (fusion_square (fusion_data d hbf) hwF))

omit [Finite G] in
private theorem two_group_cases (S : Subgroup G) (hc : Nat.card S = 2)
    {v b : G} (hv : v ∈ S) (hb : b ∈ S) (hb1 : b ≠ 1) : v=1 ∨ v=b := by
  by_cases hv1 : v=1
  · exact Or.inl hv1
  obtain ⟨s,_,hu⟩ := (Nat.card_eq_two_iff' (1 : S)).mp hc
  exact Or.inr (congrArg Subtype.val
    ((hu ⟨v,hv⟩ (fun he => hv1 (congrArg Subtype.val he))).trans
      (hu ⟨b,hb⟩ (fun he => hb1 (congrArg Subtype.val he))).symm))

omit [Finite G] in
private theorem base_not_moved (k : CubicEightContext r q X)
    (p : CubicFourData r q X) : r ∉ movedFour r X := by
  intro hr
  have hrC : r ∈ centralizer (X : Set G) :=
    (show r ∈ fusionCore r ⊓ centralizer (X : Set G) from
      k.cubic_fixed.symm ▸ mem_zpowers r).2
  have hr1 : r=1 := show r ∈ (⊥ : Subgroup G) from p.fixed_free ▸ ⟨hr,hrC⟩
  have ho := k.base_order
  simp [hr1] at ho

omit [Finite G] in
/-- The four fixed elements in the fusion eight are the base and its
products with the unique nonzero fixed moved vector. -/
public theorem fixed_fusion_cases (k : CubicEightContext r q X)
    (p : CubicFourData r q X) (hrq : Commute r q)
    (hb : b ∈ fixedLine r q X) (hb1 : b ≠ 1)
    {v : G} (hv : v ∈ fusionCore r) (hvq : v ∈ Centralizer q) :
    v=1 ∨ v=r ∨ v=b ∨ v=b*r := by
  have hn : zpowers r ≤ normalizer (movedFour r X : Set G) := by
    apply zpowers_le.mpr
    apply centralizer_le_normalizer
    intro t ht
    exact (p.commutes_base ht).eq
  have hv' : v ∈ (zpowers r : Set G) * (movedFour r X : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hn, p.decomposition]
    exact hv
  obtain ⟨s,hs,t,ht,rfl⟩ := hv'
  have hsC : s ∈ Centralizer q := (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hrq)) hs
  have htC : t ∈ Centralizer q := (mul_mem_cancel_left hsC).mp hvq
  have htL : t ∈ fixedLine r q X := ⟨ht,htC⟩
  have hr1 : r ≠ 1 := by intro he; simpa [he] using k.base_order
  have hs' := two_group_cases (zpowers r) (by rw [Nat.card_zpowers,k.base_order])
    hs (mem_zpowers r) hr1
  have ht' := two_group_cases (fixedLine r q X) p.line_card htL hb hb1
  rcases hs' with rfl | rfl <;> rcases ht' with rfl | rfl
  · exact Or.inl (one_mul 1)
  · exact Or.inr (Or.inr (Or.inl (one_mul _)))
  · exact Or.inr (Or.inl (mul_one _))
  · exact Or.inr (Or.inr (Or.inr (p.commutes_base hb.1).eq.symm))

/-- The compatibility calculation with the earlier square-root assertion
explicit. No conjugate-core intersection or braid relation is assumed. -/
public theorem compatible_fixed_vector_of_square_roots
    (h : Hypotheses z) (d : FusionEightData z) (roots : ConjugateSquareRootsInCore z)
    (hr : IsConj z r) (hq : IsConj z q) (hrq : Commute r q)
    (hqQ : q ∉ coreInG r)
    (k : CubicEightContext r q X) (p : CubicFourData r q X)
    {Y : Subgroup G} (k1 : CubicEightContext q r Y) (p1 : CubicFourData q r Y)
    (hb : b ∈ fixedLine r q X) (hb1 : b ≠ 1) : b*q*r ∈ movedFour q Y := by
  have dq := fusion_data d hq
  have hrQ : r ∉ coreInG q := fun hm => hqQ (core_reciprocity h hq hr hm)
  have hbQ := fixed_vector_not_other_core h d roots hr hq k p hb hb1
  obtain ⟨v,hv1,_⟩ := (Nat.card_eq_two_iff' (1 : fixedLine q r Y)).mp p1.line_card
  have hv : (v : G) ∈ fixedLine q r Y := v.property
  have hvne : (v : G) ≠ 1 := fun he => hv1 (Subtype.ext he)
  have hvQ := fixed_vector_not_other_core h d roots hq hr k1 p1 hv hvne
  have hq2 : q*q=1 := by simpa only [pow_two, k.involution_order] using pow_orderOf_eq_one q
  have hwQ : (v : G)*q ∈ coreInG r := product_mem_core h hr hv.2
    (mem_centralizer_singleton_iff.mpr hrq.symm) (p1.square hv.1) hq2
    (p1.commutes_base hv.1) hvQ hqQ
  have hwF : (v : G)*q ∈ fusionCore q :=
    (fusionCore q).mul_mem (p1.moved_le hv.1) k1.base_mem
  have hw1 : (v : G)*q ≠ 1 := by
    intro he
    have heq : (v : G)=q := mul_right_cancel (he.trans hq2.symm)
    have hvM : (v : G) ∈ movedFour q Y := hv.1
    rw [heq] at hvM
    exact base_not_moved k1 p1 hvM
  have hwFr : (v : G)*q ∈ fusionCore r := subset_closure
    ⟨hwQ, hr.symm.trans (hq.trans (dq.fusion _ hwF hw1))⟩
  have hwQq : (v : G)*q ∈ coreInG q := fusionCore_le q hwF
  have he : (v : G)*q=b*r := by
    rcases fixed_fusion_cases k p hrq hb hb1 hwFr (coreInG_le q hwQq) with h1 | h2 | h3 | h4
    · exact False.elim (hw1 h1)
    · exact False.elim (hrQ (h2 ▸ hwQq))
    · exact False.elim (hbQ (h3 ▸ hwQq))
    · exact h4
  have he' : b*q*r=(v : G) := by
    calc
      b*q*r = (b*r)*q := by rw [mul_assoc, hrq.symm.eq, ← mul_assoc]
      _ = ((v : G)*q)*q := by rw [← he]
      _ = v := by rw [mul_assoc,hq2,mul_one]
  exact he'.symm ▸ hv.1

/-- The selected source conjugate is precisely b*z, in both canonical cores.
This recovers the marked s of the source rather than choosing a fresh fused
involution after the calculation. -/
public theorem selected_fixed_vector_geometry_of_square_roots
    (h : Hypotheses z) (d : FusionEightData z)
    (roots : ∀ w : G, w^2=z → w ∈ coreInG z)
    {a : SourceGeometry h} (c : CommutingCubicData h a)
    (p : CubicFourData z c.u (cubicInG h)) (p1 : CubicFourData c.u z c.X1)
    (b : G) (hb : b ∈ fixedLine z c.u (cubicInG h)) (hb1 : b ≠ 1) :
    b = (a.g*z*a.g⁻¹)*z ∧
      a.g*z*a.g⁻¹ ∈ coreInG z ⊓ coreInG c.u ∧
      b*c.u*z ∈ movedFour c.u c.X1 := by
  obtain ⟨k,k1⟩ := cubicEightContexts h d c
  have R := conjugateSquareRootsInCore_of_base roots
  have hs : IsConj z (a.g*z*a.g⁻¹) := isConj_iff.mpr ⟨a.g,rfl⟩
  have hzQs := core_reciprocity_base h hs a.fused_mem
  have huQs : c.u ∈ coreInG (a.g*z*a.g⁻¹) := by
    have hu : a.u ∈ coreInG (a.g*z*a.g⁻¹) := by
      have hu := a.u_conjugate_core
      change a.u ∈ (coreInG z).map (MulAut.conj a.g).toMonoidHom at hu
      simpa only [map_coreInG, MulAut.conj_apply] using hu
    rcases c.u_choice with he | he
    · exact he ▸ hu
    · rw [he]
      exact (coreInG _).mul_mem hu hzQs
  have hsQu := core_reciprocity h hs c.u_fused huQs
  have hzQu : z ∉ coreInG c.u := fun hm =>
    selected_involution_not_core c (core_reciprocity h c.u_fused (IsConj.refl z) hm)
  have hbQu := fixed_vector_not_other_core h d R (IsConj.refl z) c.u_fused k p hb hb1
  have hsF : a.g*z*a.g⁻¹ ∈ fusionCore z := subset_closure ⟨a.fused_mem,hs⟩
  have hz1 : z ≠ 1 := by intro he; simpa [he] using h.involution
  have hs1 : a.g*z*a.g⁻¹ ≠ 1 := fun he => hz1 ((MulAut.conj a.g).map_eq_one_iff.mp he)
  have he : a.g*z*a.g⁻¹=b*z := by
    rcases fixed_fusion_cases k p c.u_commutes_z.symm hb hb1 hsF
        (coreInG_le c.u hsQu) with h1 | h2 | h3 | h4
    · exact False.elim (hs1 h1)
    · exact False.elim (hzQu (Eq.mp (congrArg (fun v : G => v ∈ coreInG c.u) h2) hsQu))
    · exact False.elim (hbQu (by rw [← h3]; exact hsQu))
    · exact h4
  have hz2 : z*z=1 := by simpa only [pow_two,h.involution] using pow_orderOf_eq_one z
  refine ⟨?_,⟨a.fused_mem,hsQu⟩,?_⟩
  · rw [he,mul_assoc,hz2,mul_one]
  · exact compatible_fixed_vector_of_square_roots h d R (IsConj.refl z) c.u_fused
      c.u_commutes_z.symm (selected_involution_not_core c) k p k1 p1 hb hb1

/-- Application to both permitted choices of the marked inverter and the
canonical fusion core at that inverter. The square-root premise remains an
upstream Lemma 2.3 obligation, not part of CubicFourData. -/
public theorem selected_compatible_fixed_vector_of_square_roots
    (h : Hypotheses z) (d : FusionEightData z)
    (roots : ∀ w : G, w^2=z → w ∈ coreInG z)
    {a : SourceGeometry h} (c : CommutingCubicData h a)
    (p : CubicFourData z c.u (cubicInG h)) (p1 : CubicFourData c.u z c.X1)
    (b : G) (hb : b ∈ fixedLine z c.u (cubicInG h)) (hb1 : b ≠ 1) :
    b*c.u*z ∈ movedFour c.u c.X1 := by
  exact (selected_fixed_vector_geometry_of_square_roots h d roots c p p1 b hb hb1).2.2

/-- The source fixed vector is `s*z`, where the marked `s = g*z*g⁻¹` lies
in both canonical cores. Its compatible vector belongs to the other moved
four. Lemma 2.3's square-root assertion is supplied by relative quaternion
normality, for both permitted choices of the source inverter. -/
public theorem selected_fixed_vector_geometry
    (h : Hypotheses z) (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z)
    {a : SourceGeometry h} (c : CommutingCubicData h a)
    (p : CubicFourData z c.u (cubicInG h)) (p1 : CubicFourData c.u z c.X1)
    (b : G) (hb : b ∈ fixedLine z c.u (cubicInG h)) (hb1 : b ≠ 1) :
    b = (a.g * z * a.g⁻¹) * z ∧
      a.g * z * a.g⁻¹ ∈ coreInG z ⊓ coreInG c.u ∧
      b * c.u * z ∈ movedFour c.u c.X1 := by
  exact selected_fixed_vector_geometry_of_square_roots h d
    (square_root_mem_coreInG h hn a) c p p1 b hb hb1

/-- The compatibility premise of `coxeterGluingData_of_local_calculations`,
with the earlier-source square-root assertion discharged. The two cubic
four-group calculations remain the consumer's independent inputs. -/
public theorem selected_compatible_fixed_vector
    (h : Hypotheses z) (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z)
    {a : SourceGeometry h} (c : CommutingCubicData h a)
    (p : CubicFourData z c.u (cubicInG h)) (p1 : CubicFourData c.u z c.X1)
    (b : G) (hb : b ∈ fixedLine z c.u (cubicInG h)) (hb1 : b ≠ 1) :
    b * c.u * z ∈ movedFour c.u c.X1 := by
  exact (selected_fixed_vector_geometry h hn d c p p1 b hb hb1).2.2

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.LocalGluing
