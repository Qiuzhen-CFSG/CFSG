module
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.SpecificGroups.Alternating.FiveSylowRadical
public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison.RankOne
public import Theory.Representation.OrthogonalFourPlusMatrix.SylowSingularLine
public import Theory.Representation.OrthogonalFourPlusMatrix.QuotientLocal.ComponentAction
public import Theory.Representation.OrthogonalFourPlusMatrix.InvolutionResidual.Preserving.Factors
public import Theory.Representation.SL2FourNaturalOrbits.PointCommutator

/-!
# Component interchange from the original point stabilizer

A two-subgroup normal in the stabilizer of a singular binary point cannot
preserve a determinant factor while moving the coefficient line. Restrict to
the factor-preserving part of the stabilizer. Its actual conjugation action
preserves the upper Sylow subgroup of SL₂(4), and the diagonal cubic fixing
the point acts nontrivially on that factor. The A₅ Sylow-radical theorem
therefore makes the normal two-actor inner on the factor. Commutation with
upper and lower root operators then makes its matrix action F₄-linear.

The automorphism theorem for a simple square turns failure to preserve the
first factor into interchange of both literal factor images. Inner matrix
coordinates transport the argument to the caller's original singular point.
`Interchange.lean` supplies its actual source consumer and discharges relative
normality using the original flag, rather than assuming component movement.

Source: Aschbacher--Smith, Lemma 14.4.9, printed pp.1009--1010;
the A₅ Sylow calculation reuses FiveSylowRadical.normal_two_action_inner.
-/

public noncomputable section
open Matrix Subgroup Module
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.PointExchange
open ClassicalOrthogonal.FourPlusMatrix ClassicalOrthogonal.FourPlusMatrix.Binary
open ClassicalOrthogonal.FourPlusMatrix.Binary.InvolutionResidual
open Theory.GroupTheory
attribute [local irreducible] Binary.action
local notation "SL" => Matrix.SpecialLinearGroup (Fin 2) Binary.F
local notation "GL" => (Binary.V ≃ₗ[ZMod 2] Binary.V)

private theorem left_injective : Function.Injective
    (Binary.linearAction.comp (MonoidHom.inl SL SL)) := by
  intro a b h
  have he : Binary.action (a,1) = Binary.action (b,1) := by
    apply LinearMap.ext
    intro v
    simpa only [MonoidHom.comp_apply,MonoidHom.inl_apply,Binary.linearAction_apply] using LinearEquiv.congr_fun h v
  exact congrArg Prod.fst (Binary.action_injective he)

private def leftEquiv : SL ≃* leftFactor := MonoidHom.ofInjective left_injective

private def leftConjugation {E : Type*} [Group E] (f : E →* GL)
    (hf : ∀ x, f x ∈ normalizer (leftFactor : Set GL)) : E →* MulAut SL :=
  (MulAut.congr leftEquiv.symm).toMonoidHom.comp
    (leftFactor.normalizerMonoidHom.comp (f.codRestrict _ hf))

private theorem leftConjugation_action {E : Type*} [Group E] (f : E →* GL)
    (hf : ∀ x, f x ∈ normalizer (leftFactor : Set GL)) (x : E) (a : SL) (v : Binary.V) :
    Binary.action (leftConjugation f hf x a,1) (f x v) =
      f x (Binary.action (a,1) v) := by
  have he : Binary.linearAction (leftConjugation f hf x a,1) =
      f x * Binary.linearAction (a,1) * (f x)⁻¹ := by
    exact congrArg Subtype.val (leftEquiv.apply_symm_apply _)
  have hh := congrArg (fun t : GL => t (f x v)) he
  change Binary.linearAction _ (f x v) = f x (Binary.linearAction (a,1) ((f x).symm (f x v))) at hh
  rw [LinearEquiv.symm_apply_apply] at hh
  simpa only [Binary.linearAction_apply] using hh

private theorem left_fixes_point (a : SL) :
    Binary.action (a,1) (Binary.pointMap 1) = Binary.pointMap 1 ↔
      a ∈ SpecialLinearGroup.upperUnipotent Binary.F := by
  constructor
  · intro h
    have he := (Displacement.fixed_iff_intertwines _ _).mp h
    have ha : a.val 0 0 = 1 := by
      simpa [Binary.pointMap,Matrix.mul_apply,Fin.sum_univ_two] using
        congrArg (fun M : Binary.V => M 0 1) he
    have hb : a.val 1 0 = 0 := by
      simpa [Binary.pointMap,Matrix.mul_apply,Fin.sum_univ_two] using
        congrArg (fun M : Binary.V => M 1 1) he
    have hd : a.val 1 1 = 1 := by
      have hd := a.property
      change a.val.det = 1 at hd
      simpa only [Matrix.det_fin_two,ha,hb,mul_zero,sub_zero,one_mul] using hd
    refine ⟨Multiplicative.ofAdd (a.val 0 1),?_⟩
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.upperUnipotentHom,SpecialLinearGroup.transvection_coe,ha,hb,hd]
  · rintro ⟨c,rfl⟩
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Binary.action_apply,Binary.pointMap,SpecialLinearGroup.upperUnipotentHom,
        SpecialLinearGroup.transvection_coe,Matrix.mul_apply,Fin.sum_univ_two]

private theorem leftConjugation_preserves_sylow {E : Type*} [Group E]
    (f : E →* GL) (hf : ∀ x, f x ∈ normalizer (leftFactor : Set GL))
    (hfix : ∀ x, f x (Binary.pointMap 1) = Binary.pointMap 1) (x : E) :
    (SpecialLinearGroup.upperUnipotent Binary.F).map
      (leftConjugation f hf x).toMonoidHom = SpecialLinearGroup.upperUnipotent Binary.F := by
  apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (leftConjugation f hf x).injective])
  rintro _ ⟨a,ha,rfl⟩
  apply (left_fixes_point _).mp
  change Binary.action (leftConjugation f hf x a,1) (Binary.pointMap 1) = _
  calc
    _ = Binary.action (leftConjugation f hf x a,1) (f x (Binary.pointMap 1)) := congrArg _ (hfix x).symm
    _ = f x (Binary.action (a,1) (Binary.pointMap 1)) := leftConjugation_action f hf x a _
    _ = Binary.pointMap 1 := by rw [(left_fixes_point a).mpr ha,hfix]

private theorem left_commutant_field_linear (t : GL)
    (ht : ∀ (a : SL) v, t (Binary.action (a,1) v) = Binary.action (a,1) (t v)) :
    ∀ (c : Binary.F) v, t (c • v) = c • t v := by
  let r (c : Binary.F) (v : Binary.V) :=
    Binary.action (SpecialLinearGroup.transvection zero_ne_one c,1) v - v
  let l (v : Binary.V) :=
    Binary.action (SpecialLinearGroup.transvection one_ne_zero (1 : Binary.F),1) v - v
  have hr (c : Binary.F) (v : Binary.V) : t (r c v) = r c (t v) := by
    dsimp only [r]
    rw [map_sub,ht]
  have hl (v : Binary.V) : t (l v) = l (t v) := by
    dsimp only [l]
    rw [map_sub,ht]
  have hs (c : Binary.F) (v : Binary.V) : c • v = r c (l v) + l (r c v) := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [r,l,Binary.action_apply,SpecialLinearGroup.transvection_coe,
        Matrix.mul_apply,Fin.sum_univ_two,Matrix.sub_apply,Matrix.add_apply,
        Matrix.smul_apply,smul_eq_mul]
  intro c v
  rw [hs,map_add,hr,hl,hl,hr,←hs]

private theorem inner_left_field_linear {E : Type*} [Group E]
    (f : E →* GL) (hf : ∀ x, f x ∈ normalizer (leftFactor : Set GL))
    (x : E) (hx : leftConjugation f hf x ∈ MulAut.innerSubgroup SL) :
    ∀ (c : Binary.F) v, f x (c • v) = c • f x v := by
  obtain ⟨a,ha⟩ := hx
  let s := Binary.linearAction (a⁻¹,1) * f x
  have hs : ∀ (b : SL) v, s (Binary.action (b,1) v) = Binary.action (b,1) (s v) := by
    intro b v
    have he := leftConjugation_action f hf x b v
    rw [←ha] at he
    have hh := congrArg (Binary.action (a⁻¹,1)) he
    change Binary.action (a⁻¹,1) (Binary.action (a*b*a⁻¹,1) (f x v)) = _ at hh
    have hm (p q : Binary.G) (w : Binary.V) :
        Binary.action p (Binary.action q w) = Binary.action (p*q) w :=
      (congrArg (fun z : Module.End (ZMod 2) Binary.V => z w) (map_mul Binary.action p q)).symm
    rw [hm] at hh
    simp only [Prod.mk_mul_mk,one_mul] at hh
    rw [show a⁻¹*(a*b*a⁻¹)=b*a⁻¹ by group] at hh
    dsimp only [s,LinearEquiv.mul_apply]
    simp only [Binary.linearAction_apply]
    rw [hm]
    simpa only [Prod.mk_mul_mk,one_mul] using hh.symm
  intro c v
  have h := left_commutant_field_linear s hs c v
  apply (Binary.linearAction (a⁻¹,1)).injective
  simp only [Binary.linearAction_apply]
  have hsm : Binary.action (a⁻¹,1) (c • f x v) = c • Binary.action (a⁻¹,1) (f x v) :=
    by simp only [Binary.action_apply,Matrix.mul_smul,Matrix.smul_mul]
  rw [hsm]
  simpa only [s,LinearEquiv.mul_apply,Binary.linearAction_apply] using h

private theorem normal_two_point_preserver_field_linear {E : Type*} [Group E] [Finite E]
    (f : E →* GL) (hf : ∀ x, f x ∈ normalizer (leftFactor : Set GL))
    (hfix : ∀ x, f x (Binary.pointMap 1) = Binary.pointMap 1)
    (R : Subgroup E) [R.Normal] (hR : IsPGroup 2 R)
    (c : E) (hc3 : c^3=1) (hc : leftConjugation f hf c ≠ 1) :
    ∀ r : R, ∀ (a : Binary.F) v, f r (a • v) = a • f r v := by
  let e := QuotientLocal.factorAlternatingEquiv
  let a := (MulAut.congr e).toMonoidHom.comp (leftConjugation f hf)
  let S := (SpecialLinearGroup.upperUnipotentSylow Binary.F 2).mapSurjective
    (f:=e.toMonoidHom) e.surjective
  have hS (x : E) : (S : Subgroup (alternatingGroup (Fin 5))).map
      (a x).toMonoidHom = S := by
    change ((SpecialLinearGroup.upperUnipotent Binary.F).map e.toMonoidHom).map
      (a x).toMonoidHom = _
    have hhom : (a x).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp (leftConjugation f hf x).toMonoidHom := by
      apply MonoidHom.ext
      intro b
      exact congrArg e (congrArg (leftConjugation f hf x) (e.symm_apply_apply b))
    rw [Subgroup.map_map,hhom,←Subgroup.map_map,leftConjugation_preserves_sylow f hf hfix]
    rfl
  have hcR : c ∈ pResidual 2 E := mem_pResidual_of_orderOf_coprime
    ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hc3))
  have hnon : ∃ d : pResidual 2 E, a d ≠ 1 := by
    refine ⟨⟨c,hcR⟩,fun h => hc ?_⟩
    exact (MulAut.congr e).injective (h.trans (MulAut.congr e).map_one.symm)
  have hi := Theory.SpecificGroups.Alternating.FiveSylowRadical.normal_two_action_inner
    S a hS (pResidual 2 E) R (isPPerfect_pResidual 2) hR hnon
  intro r
  apply inner_left_field_linear f hf r
  obtain ⟨b,hb⟩ := hi r
  refine ⟨e.symm b,?_⟩
  apply (MulAut.congr e).injective
  rw [MulAut.congr_conj,e.apply_symm_apply]
  exact hb

private def pointFixer (v : Binary.V) : Subgroup GL where
  carrier := {t | t v = v}
  one_mem' := rfl
  mul_mem' := by intro a b ha hb; change a (b v) = v; rw [hb,ha]
  inv_mem' := by
    intro a ha
    change a.symm v = v
    apply a.injective
    rw [a.apply_symm_apply]
    exact ha.symm

private theorem inner_normalizes_left (g : Binary.G) :
    Binary.linearAction g ∈ normalizer (leftFactor : Set GL) := by
  apply mem_normalizer_iff.mpr
  intro t
  constructor
  · rintro ⟨a,rfl⟩
    refine ⟨g.1*a*g.1⁻¹,?_⟩
    change Binary.linearAction (g.1*a*g.1⁻¹,1) =
      Binary.linearAction g * Binary.linearAction (a,1) * (Binary.linearAction g)⁻¹
    rw [←map_inv,←map_mul,←map_mul]
    congr 1
    apply Prod.ext <;> simp
  · intro ht
    obtain ⟨a,ha⟩ := ht
    refine ⟨g.1⁻¹*a*g.1,?_⟩
    have hh := congrArg (fun z : GL => (Binary.linearAction g)⁻¹*z*Binary.linearAction g) ha
    rw [show (Binary.linearAction g)⁻¹ *
      (Binary.linearAction g * t * (Binary.linearAction g)⁻¹) * Binary.linearAction g = t by group] at hh
    change (Binary.linearAction g)⁻¹ * Binary.linearAction (a,1) * Binary.linearAction g = t at hh
    rw [←map_inv,←map_mul,←map_mul] at hh
    change Binary.linearAction (g.1⁻¹*a*g.1,1) = t
    have he : g⁻¹ * (a,1) * g = (g.1⁻¹*a*g.1,1) := by
      apply Prod.ext <;> simp
    rwa [he] at hh

private theorem leftConjugation_inner_pair {E : Type*} [Group E]
    (f : E →* GL) (hf : ∀ x, f x ∈ normalizer (leftFactor : Set GL))
    (x : E) (g : Binary.G) (hx : f x = Binary.linearAction g) :
    leftConjugation f hf x = MulAut.conj g.1 := by
  apply MulEquiv.ext
  intro a
  apply left_injective
  have he : Binary.linearAction (leftConjugation f hf x a,1) =
      f x * Binary.linearAction (a,1) * (f x)⁻¹ :=
    congrArg Subtype.val (leftEquiv.apply_symm_apply _)
  change Binary.linearAction (leftConjugation f hf x a,1) =
    Binary.linearAction (g.1*a*g.1⁻¹,1)
  rw [he,hx,←map_inv,←map_mul,←map_mul]
  congr 1
  apply Prod.ext <;> simp

private def cubicPair : Binary.G :=
  (Representation.SL2FourNatural.PointCommutator.cubic,
    Representation.SL2FourNatural.PointCommutator.cubic⁻¹)

private theorem cubicPair_cube : cubicPair ^ 3 = 1 := by
  apply Prod.ext
  · exact Representation.SL2FourNatural.PointCommutator.cubic_pow_three
  · change Representation.SL2FourNatural.PointCommutator.cubic⁻¹ ^ 3 = 1
    rw [inv_pow,Representation.SL2FourNatural.PointCommutator.cubic_pow_three,inv_one]

private theorem cubicPair_point : Binary.action cubicPair (Binary.pointMap 1) = Binary.pointMap 1 := by
  decide +kernel

private theorem cubicPair_first_noncentral : MulAut.conj cubicPair.1 ≠ 1 := by
  intro h
  have he := MulEquiv.congr_fun h (Representation.SL2FourNatural.upper 1)
  have hn : cubicPair.1 * Representation.SL2FourNatural.upper 1 * cubicPair.1⁻¹ ≠
      Representation.SL2FourNatural.upper 1 := by decide +kernel
  exact hn he

/-- A normal two-actor fixing the marked singular point cannot combine
factor preservation with a nontrivial field twist. The original point
stabilizer, rather than just a Sylow subgroup, normalizes the actor. -/
private theorem point_normal_two_preserver_field_linear {E : Type*} [Group E] [Finite E]
    (f : E →* GL) (hinj : Function.Injective f)
    (hbase : Binary.linearAction.range ≤ f.range)
    (B : Subgroup E) (hB : IsPGroup 2 B)
    (hn : ∀ x : E, f x (Binary.pointMap 1) = Binary.pointMap 1 →
      x ∈ normalizer (B : Set E))
    (t : E) (ht : t ∈ B) (hfix : f t (Binary.pointMap 1) = Binary.pointMap 1)
    (hleft : f t ∈ normalizer (leftFactor : Set GL)) :
    ∀ (c : Binary.F) v, f t (c • v) = c • f t v := by
  let P := (pointFixer (Binary.pointMap 1)).comap f ⊓ (normalizer (leftFactor : Set GL)).comap f
  let R := B.subgroupOf P
  have hnR : P ≤ normalizer (B : Set E) := fun x hx => hn x hx.1
  let : R.Normal := normal_subgroupOf_of_le_normalizer hnR
  let fP := f.comp P.subtype
  have hfP (x : P) : fP x ∈ normalizer (leftFactor : Set GL) := x.property.2
  have hfixP (x : P) : fP x (Binary.pointMap 1) = Binary.pointMap 1 := x.property.1
  obtain ⟨c,hc⟩ := hbase (show Binary.linearAction cubicPair ∈ Binary.linearAction.range from ⟨_,rfl⟩)
  have hcP : c ∈ P := by
    exact ⟨by change f c _ = _; rw [hc]; exact (Binary.linearAction_apply _ _).trans cubicPair_point,
      by change f c ∈ normalizer (leftFactor : Set GL); rw [hc]; exact inner_normalizes_left _⟩
  let cP : P := ⟨c,hcP⟩
  have hc3 : cP^3=1 := by
    apply Subtype.ext
    apply hinj
    change f (c^3) = f 1
    rw [map_pow,hc,←map_pow,cubicPair_cube,map_one,map_one]
  have hcn : leftConjugation fP hfP cP ≠ 1 := by
    rw [leftConjugation_inner_pair fP hfP cP cubicPair hc]
    exact cubicPair_first_noncentral
  exact normal_two_point_preserver_field_linear fP hfP hfixP R hB.comap_subtype
    cP hc3 hcn ⟨⟨t,hfix,hleft⟩,ht⟩

private theorem singular_transitive (v w : Binary.V) (hv : v ≠ 0) (hw : w ≠ 0)
    (hdv : v.det = 0) (hdw : w.det = 0) : ∃ a : Binary.G, Binary.action a v = w := by
  obtain ⟨a,b,hv'⟩ := ComparisonAux.MatrixTwo.singular_nonzero_SL2_orbit v hv hdv
  obtain ⟨c,d,hw'⟩ := ComparisonAux.MatrixTwo.singular_nonzero_SL2_orbit w hw hdw
  refine ⟨(c,d)*(a,b)⁻¹,?_⟩
  have hv'' : v = Binary.action (a,b) ComparisonAux.MatrixTwo.E11 := by
    rw [Binary.action_apply]
    exact hv'
  have hw'' : w = Binary.action (c,d) ComparisonAux.MatrixTwo.E11 := by
    rw [Binary.action_apply]
    exact hw'
  rw [hv'',←Module.End.mul_apply,←map_mul]
  rw [inv_mul_cancel_right,←hw'']

/-- The point-normality argument is independent of the inner matrix coordinates. -/
private theorem singular_point_normal_two_preserver_fixes_line {E : Type*} [Group E] [Finite E]
    (f : E →* GL) (hinj : Function.Injective f)
    (hbase : Binary.linearAction.range ≤ f.range)
    (B : Subgroup E) (hB : IsPGroup 2 B)
    (v : Binary.V) (hv : v ≠ 0) (hvs : v.det = 0)
    (hn : ∀ x : E, f x v = v → x ∈ normalizer (B : Set E))
    (t : E) (ht : t ∈ B) (hfix : f t v = v)
    (hleft : f t ∈ normalizer (leftFactor : Set GL)) :
    ∀ c : Binary.F, f t (c • v) = c • v := by
  have hp0 : Binary.pointMap 1 ≠ 0 := by
    intro h
    have hh := congrArg (fun M : Binary.V => M 0 1) h
    exact one_ne_zero hh
  obtain ⟨g,hg⟩ := singular_transitive (Binary.pointMap 1) v hp0 hv
    (by simp [Binary.pointMap,Matrix.det_fin_two]) hvs
  let p := Binary.linearAction g
  let f' := (MulAut.conj p⁻¹).toMonoidHom.comp f
  have he (x : E) (w : Binary.V) : f' x w = p.symm (f x (p w)) := rfl
  have hpoint : p (Binary.pointMap 1) = v := (Binary.linearAction_apply _ _).trans hg
  have hbase' : Binary.linearAction.range ≤ f'.range := by
    rintro _ ⟨a,rfl⟩
    obtain ⟨x,hx⟩ := hbase (show Binary.linearAction (g*a*g⁻¹) ∈ Binary.linearAction.range from ⟨_,rfl⟩)
    refine ⟨x,?_⟩
    change p⁻¹ * f x * p = Binary.linearAction a
    rw [hx]
    dsimp only [p]
    rw [←map_inv,←map_mul,←map_mul]
    congr 1
    group
  have hn' (x : E) (hx : f' x (Binary.pointMap 1) = Binary.pointMap 1) :
      x ∈ normalizer (B : Set E) := by
    apply hn x
    have hh := congrArg p hx
    rw [he,p.apply_symm_apply,hpoint] at hh
    exact hh
  have htfix : f' t (Binary.pointMap 1) = Binary.pointMap 1 := by
    rw [he,hpoint,hfix,←hpoint,p.symm_apply_apply]
  have hleft' : f' t ∈ normalizer (leftFactor : Set GL) := by
    have hp := inner_normalizes_left g
    exact (normalizer _).mul_mem ((normalizer _).mul_mem ((normalizer _).inv_mem hp) hleft) hp
  have hs := point_normal_two_preserver_field_linear f'
    ((MulAut.conj p⁻¹).injective.comp hinj) hbase' B hB hn' t ht htfix hleft'
  intro c
  have hh := congrArg p (hs c (Binary.pointMap 1))
  rw [htfix] at hh
  change p (p.symm (f t (p (c • Binary.pointMap 1)))) = p (c • Binary.pointMap 1) at hh
  rw [p.apply_symm_apply] at hh
  have hp (a : Binary.F) (w : Binary.V) : p (a • w) = a • p w :=
    (matrixHom g).map_smul a w
  simpa only [hp,hpoint] using hh

private theorem swaps_of_not_normalize_left (t : GL)
    (ht : t ∈ normalizer (Binary.linearAction.range : Set GL))
    (hne : t ∉ normalizer (leftFactor : Set GL)) : SwapsFactors t := by
  have hi : Function.Injective Binary.linearAction := by
    intro a b h
    apply Binary.action_injective
    apply LinearMap.ext
    intro v
    simpa only [Binary.linearAction_apply] using LinearEquiv.congr_fun h v
  let e : Binary.G ≃* Binary.linearAction.range := MonoidHom.ofInjective hi
  let a : MulAut Binary.G := MulAut.congr e.symm
    (Binary.linearAction.range.normalizerMonoidHom ⟨t,ht⟩)
  have ha (g : Binary.G) : Binary.linearAction (a g) =
      t * Binary.linearAction g * t⁻¹ := by
    exact congrArg Subtype.val (e.apply_symm_apply _)
  have hcenter : center SL = ⊥ := by
    exact Subgroup.card_eq_one.mp
      (BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one (CharTwo.neg_eq 1))
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple SL := IsQuasisimple.of_mulEquiv QuotientLocal.factorAlternatingEquiv.symm
  rcases Theory.GroupTheory.AutomorphismSquare.normal_form hcenter a with
    ⟨b,c,he⟩ | ⟨b,c,he⟩
  · exfalso
    apply hne
    apply mem_normalizer_iff.mpr
    intro s
    constructor
    · rintro ⟨x,rfl⟩
      refine ⟨b x,?_⟩
      change Binary.linearAction (b x,1) = t * Binary.linearAction (x,1) * t⁻¹
      rw [←ha]
      simp [he,MulEquiv.prodCongr]
    · intro hs
      obtain ⟨x,hx⟩ := hs
      have hh : t * Binary.linearAction (b.symm x,1) * t⁻¹ = Binary.linearAction (x,1) := by
        rw [←ha]
        simp [he,MulEquiv.prodCongr]
      refine ⟨b.symm x,?_⟩
      exact (MulAut.conj t).injective (hh.trans hx)
  · constructor
    · apply le_antisymm
      · rintro _ ⟨_,⟨s,rfl⟩,rfl⟩
        refine ⟨c s,?_⟩
        change Binary.linearAction (1,c s) = t * Binary.linearAction (s,1) * t⁻¹
        rw [←ha]
        simp [he,MulEquiv.prodCongr]
      · rintro _ ⟨s,rfl⟩
        refine ⟨Binary.linearAction (c.symm s,1),⟨c.symm s,rfl⟩,?_⟩
        change t * Binary.linearAction (c.symm s,1) * t⁻¹ = Binary.linearAction (1,s)
        rw [←ha]
        simp [he,MulEquiv.prodCongr]
    · apply le_antisymm
      · rintro _ ⟨_,⟨s,rfl⟩,rfl⟩
        refine ⟨b s,?_⟩
        change Binary.linearAction (b s,1) = t * Binary.linearAction (1,s) * t⁻¹
        rw [←ha]
        simp [he,MulEquiv.prodCongr]
      · rintro _ ⟨s,rfl⟩
        refine ⟨Binary.linearAction (1,b.symm s),⟨b.symm s,rfl⟩,?_⟩
        change t * Binary.linearAction (1,b.symm s) * t⁻¹ = Binary.linearAction (s,1)
        rw [←ha]
        simp [he,MulEquiv.prodCongr]

/-- Movement of the singular coefficient line by a normal two-actor in its
binary point stabilizer forces interchange of the two actual determinant factors. -/
theorem swaps_of_point_normal_two {E : Type*} [Group E] [Finite E]
    (f : E →* GL) (hinj : Function.Injective f)
    (hbase : Binary.linearAction.range ≤ f.range)
    (B : Subgroup E) (hB : IsPGroup 2 B)
    (v : Binary.V) (hv : v ≠ 0) (hvs : v.det = 0)
    (hn : ∀ x : E, f x v = v → x ∈ normalizer (B : Set E))
    (t : E) (ht : t ∈ B) (hfix : f t v = v)
    (htn : f t ∈ normalizer (Binary.linearAction.range : Set GL))
    (hmove : ∃ c : Binary.F, f t (c • v) ≠ c • v) : SwapsFactors (f t) := by
  apply swaps_of_not_normalize_left (f t) htn
  intro hleft
  obtain ⟨c,hc⟩ := hmove
  exact hc (singular_point_normal_two_preserver_fixes_line f hinj hbase B hB v hv hvs
    hn t ht hfix hleft c)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.PointExchange

