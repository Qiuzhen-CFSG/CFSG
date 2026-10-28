module
public import CFSG.Quasithin.Chapter1.Section03.ElementaryFusion
public import Theory.GroupTheory.PGroup.NormalExtraspecialPair
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.PResidual.NormalizedSupplement

/-!
# Fusion for both odd Xi quotient shapes

For normal X and Y, use their actual images modulo the ambient two-core.
The inverse image in X of the image of Y is invariant under the common
actor. Xi irreducibility makes its Frattini image trivial or full. In the
extraspecial case, triviality bounds the image intersection by p; the
normal extraspecial rank-two theorem identifies the images. Fullness gives
the same containment by Frattini's nongeneration theorem. Two-perfectness
then removes the ambient two-core and equal orders give X = Y.

For mutually normalizing X and Y, perform this argument in X∨Y∨T. This
retains the actual quotient maps and avoids asserting that an arbitrary
quotient preserves the original intersection. Odd rank is preserved by
the two-group kernel. The final point-centralizer application combines
this extraspecial branch with the earlier elementary branch.

Source: Aschbacher--Smith, proof of 9.4.1, printed pp.735--736.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1
variable {G : Type*} [Group G] [Finite G]

/-- Normal Xi factors with extraspecial quotients fuse under the odd rank-two
bound. Only the first factor needs Xi irreducibility. -/
theorem XiMember.eq_of_normal_extraspecial_quotients
    {p : ℕ} [Fact p.Prime] (ho : Odd p) {T X Y : Subgroup G}
    [X.Normal] [Y.Normal] (hX : XiMember T X)
    (hEX : IsExtraspecial p (XiQuotient X)) (hEY : IsExtraspecial p (XiQuotient Y))
    (hcX : Nat.card (XiQuotient X) = p ^ 3) (hcY : Nat.card (XiQuotient Y) = p ^ 3)
    (heX : Monoid.exponent (XiQuotient X) = p) (heY : Monoid.exponent (XiQuotient Y) = p)
    (hcard : Nat.card X = Nat.card Y)
    (hr : primeRank p (X ⊔ Y : Subgroup G) ≤ 2) : X = Y := by
  let _ := hEX
  let _ := hEY
  let q := QuotientGroup.mk' (pCore 2 G)
  let A := X.map q
  let B := Y.map q
  let _ : A.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let _ : B.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let eX : XiQuotient X ≃* A := coreQuotientEquivImage 2 X
  let eY : XiQuotient Y ≃* B := coreQuotientEquivImage 2 Y
  let _ : IsExtraspecial p A := hEX.of_mulEquiv eX
  let _ : IsExtraspecial p B := hEY.of_mulEquiv eY
  have finish (hAB : A ≤ B) : X = Y := by
    have hle : X ≤ Y ⊔ pCore 2 G := by
      have hh := map_le_iff_le_comap.mp hAB
      simpa only [B, q, comap_map_eq, QuotientGroup.ker_mk'] using hh
    have hXY := le_of_isPPerfect_of_le_sup_of_normalizes X Y (pCore 2 G)
      hX.perfect pCore_isPGroup le_normalizer_of_normal hle
    exact eq_of_le_of_card_ge hXY hcard.ge
  let K := B.comap (q.comp X.subtype)
  let qX := QuotientGroup.mk' (pCore 2 X)
  let r := QuotientGroup.mk' (frattini (XiQuotient X))
  let F := (K.map qX).map r
  have hF : ∀ t : T, ∀ a ∈ F, xiFrattiniAction T X hX.invariant t a ∈ F := by
    rintro t a ⟨b,⟨x,hx,rfl⟩,rfl⟩
    let z : X := ⟨(t : G) * x * (t : G)⁻¹,
      (mem_normalizer_iff.mp (hX.invariant t.property) x).mp x.property⟩
    have hz : z ∈ K := by
      change q ((t : G) * x * (t : G)⁻¹) ∈ B
      rw [map_mul,map_mul,map_inv]
      exact (inferInstance : B.Normal).conj_mem (q x) hx (q t)
    refine ⟨qX z,⟨z,hz,rfl⟩,?_⟩
    simp only [r,qX,xiFrattiniAction,MonoidHom.comp_apply,quotientAut_apply_mk]
    rfl
  rcases hX.irreducible F hF with hb | ht
  · have hsmall (x : X) (hx : x ∈ K) : qX x ∈ frattini (XiQuotient X) := by
      have hxF : r (qX x) ∈ F := mem_map_of_mem r (mem_map_of_mem qX hx)
      exact (QuotientGroup.eq_one_iff _).mp (mem_bot.mp (hb ▸ hxF))
    let f : (A ⊓ B : Subgroup (G ⧸ pCore 2 G)) → frattini (XiQuotient X) := fun y =>
      ⟨eX.symm ⟨y,y.property.1⟩,by
        obtain ⟨x,hx,hxy⟩ := y.property.1
        let xx : X := ⟨x,hx⟩
        have hxK : xx ∈ K := by
          change q x ∈ B
          rw [hxy]
          exact y.property.2
        have hxe : eX (qX xx) = ⟨y,y.property.1⟩ := by
          apply Subtype.ext
          exact (coreQuotientEquivImage_apply_mk 2 X xx).trans hxy
        rw [← hxe,eX.symm_apply_apply]
        exact hsmall xx hxK⟩
    have hf : Function.Injective f := by
      intro y z hyz
      apply Subtype.ext
      have hh := congrArg (fun c : frattini (XiQuotient X) => (eX c.val).val) hyz
      simpa only [f,eX.apply_symm_apply] using hh
    have hI : Nat.card (A ⊓ B : Subgroup (G ⧸ pCore 2 G)) ≤ p := by
      have hh := Nat.card_le_card_of_injective f hf
      rwa [IsExtraspecial.frattini_eq_center (p := p),IsExtraspecial.center_order_p p (XiQuotient X)] at hh
    have hr' : primeRank p (A ⊔ B : Subgroup (G ⧸ pCore 2 G)) ≤ 2 := by
      change primeRank p (X.map q ⊔ Y.map q : Subgroup _) ≤ 2
      rw [← Subgroup.map_sup,ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel ho q
        (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)]
      exact hr
    have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) ho
    have hAB := Subgroup.normal_extraspecial_pair_eq_of_join_rank_two hp2 A B
      ((Nat.card_congr eX.toEquiv).symm.trans hcX) ((Nat.card_congr eY.toEquiv).symm.trans hcY)
      ((Monoid.exponent_eq_of_mulEquiv eX).symm.trans heX)
      ((Monoid.exponent_eq_of_mulEquiv eY).symm.trans heY) hI hr'
    exact finish hAB.le
  · have himage : K.map qX = ⊤ := by
      apply frattini_nongenerating
      have hh := congrArg (Subgroup.comap r) ht
      simpa only [F,comap_map_eq,r,QuotientGroup.ker_mk',comap_top] using hh
    apply finish
    rintro _ ⟨x,hx,rfl⟩
    have hxmem : qX ⟨x,hx⟩ ∈ K.map qX := himage ▸ mem_top _
    obtain ⟨k,hk,hke⟩ := hxmem
    have hh : q k = q x :=
      (coreQuotientEquivImage_apply_mk 2 X k).symm.trans
        ((congrArg (fun u : XiQuotient X => (eX u).val) hke).trans
          (coreQuotientEquivImage_apply_mk 2 X ⟨x,hx⟩))
    exact hh ▸ hk


/-- The extraspecial fusion branch for mutually normalizing factors and a
common normalizing actor. Ambient normality is obtained inside their join. -/
theorem XiMember.eq_of_extraspecial_quotients
    {p : ℕ} [Fact p.Prime] (ho : Odd p) {T X Y : Subgroup G}
    (hX : XiMember T X) (hY : T ≤ normalizer (Y : Set G))
    (hXY : X ≤ normalizer (Y : Set G)) (hYX : Y ≤ normalizer (X : Set G))
    (hEX : IsExtraspecial p (XiQuotient X)) (hEY : IsExtraspecial p (XiQuotient Y))
    (hcX : Nat.card (XiQuotient X) = p ^ 3) (hcY : Nat.card (XiQuotient Y) = p ^ 3)
    (heX : Monoid.exponent (XiQuotient X) = p) (heY : Monoid.exponent (XiQuotient Y) = p)
    (hcard : Nat.card X = Nat.card Y)
    (hr : primeRank p (X ⊔ Y : Subgroup G) ≤ 2) : X = Y := by
  let H := X ⊔ Y ⊔ T
  have hXH : X ≤ H := le_sup_left.trans le_sup_left
  have hYH : Y ≤ H := le_sup_right.trans le_sup_left
  have hTH : T ≤ H := le_sup_right
  let X' := X.subgroupOf H
  let Y' := Y.subgroupOf H
  let T' := T.subgroupOf H
  let _ : X'.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (sup_le X.le_normalizer hYX) hX.invariant)
  let _ : Y'.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (sup_le hXY Y.le_normalizer) hY)
  have hX' : XiMember T' X' :=
    (mem_XiIn_iff_subgroupOf hTH hXH).mp ⟨hXH,hX⟩
  let eX : X' ≃* X := subgroupOfEquivOfLe hXH
  let eY : Y' ≃* Y := subgroupOfEquivOfLe hYH
  let qX : XiQuotient X' ≃* XiQuotient X :=
    QuotientGroup.congr _ _ eX (pCore_map_iso 2 eX)
  let qY : XiQuotient Y' ≃* XiQuotient Y :=
    QuotientGroup.congr _ _ eY (pCore_map_iso 2 eY)
  have hr' : primeRank p (X' ⊔ Y' : Subgroup H) ≤ 2 := by
    change primeRank p (X.subgroupOf H ⊔ Y.subgroupOf H : Subgroup H) ≤ 2
    rw [← subgroupOf_sup hXH hYH,
      primeRank_congr p (subgroupOfEquivOfLe (sup_le hXH hYH))]
    exact hr
  have he := hX'.eq_of_normal_extraspecial_quotients ho
    (hEX.of_mulEquiv qX.symm) (hEY.of_mulEquiv qY.symm)
    ((Nat.card_congr qX.toEquiv).trans hcX) ((Nat.card_congr qY.toEquiv).trans hcY)
    ((Monoid.exponent_eq_of_mulEquiv qX).trans heX)
    ((Monoid.exponent_eq_of_mulEquiv qY).trans heY)
    ((Nat.card_congr eX.toEquiv).trans (hcard.trans (Nat.card_congr eY.toEquiv).symm)) hr'
  have hh := congrArg (Subgroup.map H.subtype) he
  change (X.subgroupOf H).map H.subtype = (Y.subgroupOf H).map H.subtype at hh
  simpa only [map_subgroupOf_eq_of_le hXH,map_subgroupOf_eq_of_le hYH] using hh

/-- Both Xi quotient shapes identify a mutually normalizing conjugate under
the actual join's odd rank bound. -/
theorem XiMember.eq_conjugate_of_odd_quotient
    {p : ℕ} [Fact p.Prime] (ho : Odd p) {T X : Subgroup G}
    (hX : XiMember T X) (g : G)
    (hn : T ≤ normalizer (X.map (MulAut.conj g).toMonoidHom : Set G))
    (hXY : X ≤ normalizer (X.map (MulAut.conj g).toMonoidHom : Set G))
    (hYX : X.map (MulAut.conj g).toMonoidHom ≤ normalizer (X : Set G))
    (hq : XiOddQuotient p (XiQuotient X))
    (hr : primeRank p (X ⊔ X.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2) :
    X = X.map (MulAut.conj g).toMonoidHom := by
  rcases hq with ⟨he,hc⟩ | ⟨he,hc,hex⟩
  · exact hX.eq_conjugate_of_elementary_quotient ho g hn hXY hYX he hc hr
  · let e := X.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    let q := QuotientGroup.congr (pCore 2 X) _ e (pCore_map_iso 2 e)
    exact hX.eq_of_extraspecial_quotients ho hn hXY hYX he (he.of_mulEquiv q)
      hc ((Nat.card_congr q.toEquiv).symm.trans hc)
      hex ((Monoid.exponent_eq_of_mulEquiv q).symm.trans hex)
      (Nat.card_congr e.toEquiv) hr

/-- The literal point-fusion configuration identifies X with its conjugate.
Quasithinness supplies the rank bound for either odd quotient shape. -/
theorem XiMember.eq_conjugate_at_point
    (hqt : IsQuasithin G)
    {T X U : Subgroup G} {v w g : G} (hX : XiMember T X)
    (hv : orderOf v = 2) (hvU : v ∈ U)
    (hXU : X ≤ centralizer (U : Set G))
    (hNv : centralizer ({v} : Set G) ≤ normalizer (X : Set G))
    (hg : g ∈ normalizer (U : Set G))
    (hconj : MulAut.conj g v = w)
    (hTw : T ≤ centralizer ({w} : Set G)) :
    X = X.map (MulAut.conj g).toMonoidHom ∧
      centralizer ({w} : Set G) ≤ normalizer (X : Set G) := by
  obtain ⟨p,hp,ho,hq⟩ := hX.odd_quotient
  let _ : Fact p.Prime := ⟨hp⟩
  have hUw : w ∈ U := hconj ▸ (mem_normalizer_iff.mp hg v).mp hvU
  have hNw := pointCentralizer_normalizes_conjugate hNv hconj
  have hCU : centralizer (U : Set G) ≤ centralizer ({v} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr hvU)
  have hXw : X ≤ centralizer ({w} : Set G) :=
    hXU.trans (centralizer_le (Set.singleton_subset_iff.mpr hUw))
  have hYU : X.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) := by
    have hU : U.map (MulAut.conj g).toMonoidHom = U :=
      mem_normalizer_iff_map_conj_eq.mp hg
    have hh := (map_mono (f := (MulAut.conj g).toMonoidHom) hXU).trans
      (map_centralizer_le_centralizer_image (U : Set G) (MulAut.conj g).toMonoidHom)
    change X.map (MulAut.conj g).toMonoidHom ≤
      centralizer (U.map (MulAut.conj g).toMonoidHom : Set G) at hh
    rwa [hU] at hh
  have hr : primeRank p (X ⊔ X.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 := by
    exact (primeRank_mono p (sup_le (hXU.trans hCU) (hYU.trans hCU))).trans
      ((Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hqt) _
        (Theory.GroupTheory.isTwoLocal_involution_centralizer hv) p Fact.out ho)
  have heq := hX.eq_conjugate_of_odd_quotient ho g (hTw.trans hNw)
    (hXw.trans hNw) (hYU.trans (hCU.trans hNv)) hq hr
  exact ⟨heq, heq ▸ hNw⟩

end CFSG.Quasithin.Chapter1
