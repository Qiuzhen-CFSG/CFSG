module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CubicInverterObstruction
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CubicInvolutionFusion
public import Theory.SpecificGroups.Janko3.SourceRecognition.PlaneCubicWitness

/-!
# Genuine cubic nonfusion from the original plane complement

The derived cubic σ has an involutory inverter centralizing the original
scalar cubic s. If σ were conjugate to s, this pair would contradict the
proved projective inverter obstruction. The product sσ fixes an actual
plane involution, hence is conjugate to s by the original one-class fusion.
Thus σ and sσ are not conjugate in G. The same original complement and
field embedding supply every element; no split extension is an input.

Source: Baumeister, A geometry for groups of J₃-type (2007), Lemma 2.4.
-/

public noncomputable section
open Subgroup
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen
open Janko23.J3Recognition.Ambient

set_option maxHeartbeats 800000 in
/-- The actual derived cubic of the original complement is not fused with
its product with the original field cubic, even in the ambient group. -/
theorem literal_cubic_nonfusion
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (ha : ∀ (c : C) (x : A),
      a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j) :
    ∃ σ : C, orderOf σ = 3 ∧ σ ∈ _root_.commutator C ∧
      Commute (j cubic) ((σ : normalizer (A : Set G)) : G) ∧
      ((σ : normalizer (A : Set G)) : G) ∉ zpowers (j cubic) ∧
      ¬ IsConj ((σ : normalizer (A : Set G)) : G)
        (j cubic * ((σ : normalizer (A : Set G)) : G)) := by
  obtain ⟨σ, τ, hσ, hτ, hi, hd, hsσ, hsτ, hσout, v, hv, hfixed⟩ :=
    PlaneTransport.field_cubic_nonfusion_witness A C l a ha j hj
  let k : C →* G := (normalizer (A : Set G)).subtype.comp C.subtype
  have hk : Function.Injective k := Subtype.val_injective.comp Subtype.val_injective
  let s := j cubic
  change Commute s (k σ) at hsσ
  change Commute s (k τ) at hsτ
  change k σ ∉ zpowers s at hσout
  have hs : orderOf s = 3 := (orderOf_injective j hj.1 _).trans cubic_order
  have hσG : orderOf (k σ) = 3 := (orderOf_injective k hk σ).trans hσ
  have hτG : orderOf (k τ) = 2 := (orderOf_injective k hk τ).trans hτ
  have hnot : ¬ IsConj (k σ) s := by
    intro hconj
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    let e := MulAut.conj g
    have hes : e (k σ) = s := hg
    let N := normalizer (zpowers s : Set G)
    have hri : e (k τ) * s * (e (k τ))⁻¹ = s⁻¹ := by
      rw [← hes, ← map_inv, ← map_mul, ← map_mul]
      have hki := congrArg k hi
      simpa only [map_mul, map_inv] using congrArg e hki
    have hrN : e (k τ) ∈ N := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      rw [MonoidHom.map_zpowers]
      change zpowers (e (k τ) * s * (e (k τ))⁻¹) = zpowers s
      rw [hri, zpowers_inv]
    have hxs : Commute s (e s) := by
      nth_rw 1 [← hes]
      exact (hsσ.symm.map e.toMonoidHom)
    have hxN : e s ∈ N := cubic_centralizer_le_normalizer s
      (mem_centralizer_singleton_iff.mpr hxs.eq.symm)
    let r : N := ⟨e (k τ), hrN⟩
    let x : N := ⟨e s, hxN⟩
    have hr : orderOf r = 2 := (orderOf_coe r).symm.trans ((e.orderOf_eq _).trans hτG)
    have hx : orderOf x = 3 := (orderOf_coe x).symm.trans ((e.orderOf_eq _).trans hs)
    apply literal_cubic_inverter_not_commute_three P hc A C a j hj r x hr hri hx
    apply Subtype.ext
    exact (hsτ.symm.map e.toMonoidHom).eq
  have hprod : orderOf (s * k σ) = 3 := by
    apply orderOf_eq_prime
    · rw [hsσ.mul_pow, show s ^ 3 = 1 by simpa only [hs] using pow_orderOf_eq_one s,
        show k σ ^ 3 = 1 by simpa only [hσG] using pow_orderOf_eq_one (k σ), one_mul]
    · intro he
      rw [eq_inv_of_mul_eq_one_right he] at hσout
      exact hσout ((zpowers s).inv_mem (mem_zpowers s))
  have hsf : Commute s (j SingerField.fieldElement) :=
    (cubic_commutes_complement
      ⟨SingerField.fieldElement, (mem_pointComplement _).mpr rfl⟩).map j
  have hconj : IsConj (s * k σ) s :=
    literal_cubic_fusion_of_commuting_involutions P hc (s * k σ) s v
      (j SingerField.fieldElement) hprod hs ((orderOf_coe v).trans hv)
      hj.2.2.2.2.2.2.1 hfixed hsf
  exact ⟨σ, hσ, hd, hsσ, hσout, fun h => hnot (h.trans hconj)⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
