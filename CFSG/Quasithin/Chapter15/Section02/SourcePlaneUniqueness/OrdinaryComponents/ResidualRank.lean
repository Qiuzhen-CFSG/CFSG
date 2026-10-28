module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.QuotientRank

/-!
# The original rank-two subgroup in a component residual

When a model-specific A.3.18 theorem identifies the selected component with
O^{3′}(I), the original K lies in its marked fixed subgroup. Its rank two
survives the central two-core quotient. This extends the existing outer-two
route to models whose outer group can contain odd field automorphisms.
The model consumers prove the residual identity on the same component.
Source: Aschbacher--Smith 15.2.24, pp.1117--1118, refs/quasithin.pdf.
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
/-- The original rank-two K embeds in the marked fixed subgroup upstairs. -/
theorem fixed_three_rank_of_residual (hI : PlaneEscapes Mc ZS I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (hres : c.component = primeToResidual 3 I)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹) :
    2 ≤ primeRank 3 a.fixedSubgroup := by
  let K := (pResidual 2 H).map H.subtype
  have hKL : K ≤ c.component.map I.subtype := by
    rw [hres]
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

/-- The literal quotient involution centralizer has three-rank at least two. -/
theorem quotient_centralizer_three_rank_of_residual (hI : PlaneEscapes Mc ZS I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (e : (c.component ⧸ pCore 2 c.component) ≃* D)
    (hres : c.component = primeToResidual 3 I)
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
  have hlow := fixed_three_rank_of_residual d c hI hz hzne hres a ha
  have he := ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel
    (by decide : Odd 3) q (by rw [hk]; exact pCore_isPGroup) a.fixedSubgroup
  rw [←he] at hlow
  exact hlow.trans (primeRank_mono 3 hle)

end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
