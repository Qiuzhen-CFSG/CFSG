module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.FullRank
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupAction.FourGroupSylowCentralizer
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic

/-!
# The marked central quotient of the ordinary component

The three-rank-two component equals the literal prime-to-three residual
when its simple quotient has two-group outer automorphisms. Thus the original
K embeds in its fixed subgroup. Quotienting by the central two-core preserves
three-rank and carries the inner marked action to an actual two-central
involution in the specified model. In particular the covering center is
retained throughout the sporadic inspection.

Source: Aschbacher--Smith, proof of 15.2.15, printed p.1118;
A.3.18, printed pp.51--53, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 Candidates.ComponentStructure ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)
variable {D : Type*} [Group D] [Finite D]
include d

omit d in
include hsource in
/-- A.3.18 on the original component, allowing its central two-cover. -/
theorem component_eq_residual_of_quotient (hI : PlaneEscapes Mc ZS I)
    (e : (c.component ⧸ pCore 2 c.component) ≃* D)
    (hr : 2 ≤ primeRank 3 D) (ho : IsPGroup 2 (MulAut.Outer D)) :
    c.component = primeToResidual 3 I := by
  let eZ : (c.component ⧸ center c.component) ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq c.center_eq).trans e
  have hcop : Nat.Coprime 3 (Nat.card (center c.component)) := by
    obtain ⟨n,hn⟩ := c.center_two.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hrL : 2 ≤ primeRank 3 c.component := by
    rw [← primeRank_congr 3 e] at hr
    exact hr.trans (primeRank_quotient_le_of_isTwoGroup 3 (by decide)
      (pCore 2 c.component) pCore_isPGroup)
  exact (Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual_of_outer_twoGroup
    c.isComponent hcop hrL
    ((Chapter3.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin 3 (by decide) (by decide))
    eZ (by decide) ho).2

/-- The original rank-two K embeds in the marked fixed subgroup upstairs. -/
theorem fixed_three_rank_of_quotient (hI : PlaneEscapes Mc ZS I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (e : (c.component ⧸ pCore 2 c.component) ≃* D)
    (hr : 2 ≤ primeRank 3 D) (ho : IsPGroup 2 (MulAut.Outer D))
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹) :
    2 ≤ primeRank 3 a.fixedSubgroup := by
  let K := (pResidual 2 H).map H.subtype
  have hKL : K ≤ c.component.map I.subtype := by
    rw [component_eq_residual_of_quotient (hsource := hsource) c hI e hr ho]
    exact residual_le_escape_primeToResidual d hI
  let eL := c.component.equivMapOfInjective I.subtype I.subtype_injective
  let f : K →* c.component := eL.symm.toMonoidHom.comp (inclusion hKL)
  have hf (k : K) : ((f k : I) : G) = k := by
    exact congrArg Subtype.val (eL.apply_symm_apply ⟨k,hKL k.property⟩)
  have hfix (k : K) : f k ∈ a.fixedSubgroup := by
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    apply Subtype.ext
    rw [ha,hf]
    have hkMc : (k : G) ∈ Mc :=
      ((le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_left) k.property
    have hkz : (k : G) * z = z * k := mem_centralizer_singleton_iff.mp
      ((marked_centralizer d hI hz hzne).2.ge hkMc)
    rw [← hkz,mul_inv_cancel_right]
  let g := f.codRestrict a.fixedSubgroup hfix
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact (hf x).symm.trans ((congrArg (fun w : a.fixedSubgroup => ((w.val : I) : G)) h).trans (hf y))
  have hbound := _root_.primeRank_le_of_injective 3 g hg
  rw [PlaneUniquenessPreceding.LinearThree.residual_rank_two d] at hbound
  exact hbound

omit d hsource [Finite D] in
/-- The actual inner involution descends with its full Sylow marking. -/
theorem quotient_twoCentral_of_inner (e : (c.component ⧸ pCore 2 c.component) ≃* D)
    (a : MulAut c.component) (hai : TwoCentralInner a) :
    ∃ t : D, orderOf t = 2 ∧ DoubleCoverCentralizer.TwoCentral t ∧
      ∀ x : c.component, e (QuotientGroup.mk' _ (a x)) =
        t * e (QuotientGroup.mk' _ x) * t⁻¹ := by
  obtain ⟨⟨l,hl⟩,ha2,Q,hQ⟩ := hai
  subst a
  let q : c.component →* D := e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hq (x : c.component) : q x = 1 ↔ x ∈ center c.component := by
    change e (QuotientGroup.mk' _ x) = 1 ↔ _
    rw [e.map_eq_one_iff,QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff,c.center_eq]
  have ht2 : q l ^ 2 = 1 := by
    rw [←map_pow,hq]
    apply mem_center_iff.mpr
    intro x
    have hh := congrArg (fun b : MulAut c.component => b x)
      (show (MulAut.conj l) ^ 2 = 1 from ha2 ▸ pow_orderOf_eq_one (MulAut.conj l))
    change l * (l * x * l⁻¹) * l⁻¹ = x at hh
    have hh' : l^2 * x * (l^2)⁻¹ = x := by simpa only [pow_two,mul_inv_rev,mul_assoc] using hh
    exact (mul_inv_eq_iff_eq_mul.mp hh').symm
  have htne : q l ≠ 1 := by
    intro ht
    have hlc := (hq l).mp ht
    have he : MulAut.conj l = 1 := by
      apply MulEquiv.ext
      intro x
      change l * x * l⁻¹ = x
      exact mul_inv_eq_iff_eq_mul.mpr ((mem_center_iff.mp hlc x).symm)
    rw [he,orderOf_one] at ha2
    omega
  have ht : orderOf (q l) = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one ht2)).resolve_left
      (by simpa only [orderOf_eq_one_iff] using htne)
  have hqs : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let R := Q.mapSurjective (f := q) hqs
  have hc : q l ∈ centralizer (R : Set D) := by
    rintro x ⟨y,hy,rfl⟩
    rw [←map_mul,←map_mul]
    apply congrArg q
    exact (mul_inv_eq_iff_eq_mul.mp (hQ ⟨y,hy⟩)).symm
  have htR := Theory.GroupAction.mem_sylow_of_sq_eq_one_of_centralizes R ht2 hc
  refine ⟨q l,ht,⟨R,htR,mem_center_iff.mpr (fun x => Subtype.ext (hc x x.property))⟩,?_⟩
  intro x
  exact q.map_mul _ _ |>.trans (by simp only [map_mul,map_inv]; rfl)

/-- The literal quotient involution centralizer has three-rank at least two. -/
theorem quotient_centralizer_three_rank (hI : PlaneEscapes Mc ZS I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (e : (c.component ⧸ pCore 2 c.component) ≃* D)
    (hr : 2 ≤ primeRank 3 D) (ho : IsPGroup 2 (MulAut.Outer D))
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hai : TwoCentralInner a) :
    ∃ t : D, orderOf t = 2 ∧ DoubleCoverCentralizer.TwoCentral t ∧
      2 ≤ primeRank 3 (centralizer ({t} : Set D)) := by
  obtain ⟨t,ht,htc,hact⟩ := quotient_twoCentral_of_inner c e a hai
  let q : c.component →* D := e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hk : q.ker = pCore 2 c.component := by
    ext x
    change e (QuotientGroup.mk' _ x) = 1 ↔ _
    rw [e.map_eq_one_iff,QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
  have hle : a.fixedSubgroup.map q ≤ centralizer ({t} : Set D) := by
    rintro x ⟨y,hy,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := hact y
    rw [(MulAut.mem_fixedSubgroup _ _).mp hy] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  refine ⟨t,ht,htc,?_⟩
  have hlow := fixed_three_rank_of_quotient d c hI hz hzne e hr ho a ha
  have he := ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel
    (by decide : Odd 3) q (by rw [hk]; exact pCore_isPGroup) a.fixedSubgroup
  rw [←he] at hlow
  exact hlow.trans (primeRank_mono 3 hle)
end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
