module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.Basic
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import Theory.GroupAction.SylowPointwiseInnerTransport
public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.LocalKernel

/-!
# Triality Sylow-fixing involutions through the actual local quotient

Normalize the fixed Sylow to the positive subgroup. Inner–coefficient coverage
then places the inner factor in its Borel and hence in the arms parabolic.
The original involution induces an automorphism on the literal local residual
modulo its intrinsic two-core, fixing the image Sylow pointwise. This quotient
is PSL₂(q³), so the proved rank-one Sylow-fixer theorem makes that action inner.
The local coefficient-detection theorem now places the original involution
in the local conjugation image. Sylow conjugacy and perfect-cover transport
return innerness on the original marked group.

This includes q = 2 and uses the cubic coefficient field throughout. No
multiplier or involution-centralizer classification is assumed or concluded.
Source: Aschbacher--Smith, proof of 1.1.5(3), printed p.502; GLS3 2.5.12
and the local quotient calculations used in F.1.12, printed pp.263–264.
-/

public section
open Subgroup
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.OuterOdd
open Triality.Standard.ParabolicOuterTwo

private theorem triality_standard_inner (n : ℕ) (hn : 0 < n)
    (a : MulAut (BinaryCarrier n hn)) (ha : a ^ 2 = 1)
    (hfix : ∀ x ∈ unipotent (binaryParameters n hn), a x = x) :
    a ∈ (MulAut.conj (G := BinaryCarrier n hn)).range := by
  let P := binaryParameters n hn
  have hmap : (unipotent P).map a.toMonoidHom = unipotent P := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change a x ∈ unipotent P
      rw [hfix x hx]
      exact hx
    · intro x hx
      exact ⟨x, hx, hfix x hx⟩
  obtain ⟨g, e, he⟩ := Coverage.binary_inner_coefficient n hn a
  have hg : g ∈ parabolic P .arms := by
    apply borel_le_parabolic P .arms
    rw [← ConcreteBruhat.normalizer_unipotent_eq_borel P rfl]
    apply mem_normalizer_iff_map_conj_eq.mpr
    calc
      (unipotent P).map (MulAut.conj g).toMonoidHom =
          ((unipotent P).map (coefficientAction P e).toMonoidHom).map
            (MulAut.conj g).toMonoidHom := by
              rw [show (unipotent P).map (coefficientAction P e).toMonoidHom =
                unipotent P from coefficient_unipotent P e]
      _ = (unipotent P).map a.toMonoidHom := by rw [map_map, he]; rfl
      _ = unipotent P := hmap
  let b : localStabilizer P .arms :=
    parabolicInner P .arms ⟨g, hg⟩ * coefficientStabilizer P .arms e
  have hb : b.val = a := he.symm
  have hb2 : b ^ (2 ^ 1) = 1 := by
    apply Subtype.ext
    change b.val ^ (2 ^ 1) = 1
    simpa only [pow_one, hb] using ha
  have hlocal : localQuotientAction P .arms b ∈
      MulAut.innerSubgroup (LocalTwoQuotient P .arms) := by
    let S := (unipotentSylow P rfl).subtype (unipotentSylow_le_localFactor P rfl .arms)
    let q := QuotientGroup.mk' (pCore 2 (localFactor P .arms))
    let Q := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
    have hQ : ∀ x ∈ Q, localQuotientAction P .arms b x = x := by
      rintro _ ⟨y, hy, rfl⟩
      rw [localQuotientAction_mk]
      apply congrArg q
      apply Subtype.ext
      change b.val y.val = y.val
      rw [hb]
      exact hfix y.val hy
    obtain ⟨x, _, hx⟩ := MulAut.fixing_sylow_inner_of_equiv
      (localFactorArmsQuotientEquivPSL2 P rfl)
      Theory.PSL2.aut_fixing_sylow_inner Q (localQuotientAction P .arms b) hQ
    exact ⟨x, hx.symm⟩
  obtain ⟨x, hx⟩ := local_inner_twoElement n hn .arms b 1 hb2 hlocal
  exact ⟨x.val, (congrArg Subtype.val hx).trans hb⟩

private theorem triality_sylow_inner (n : ℕ) (hn : 0 < n)
    (Q : Sylow 2 (BinaryCarrier n hn)) (a : MulAut (BinaryCarrier n hn))
    (ha : a ^ 2 = 1) (hfix : ∀ x ∈ Q, a x = x) :
    a ∈ (MulAut.conj (G := BinaryCarrier n hn)).range := by
  let U := unipotentSylow (binaryParameters n hn) rfl
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (BinaryCarrier n hn) Q U
  let e := MulAut.conj g
  have hm : (Q : Subgroup (BinaryCarrier n hn)).map e.toMonoidHom = U :=
    congrArg Sylow.toSubgroup hg
  have hb : (MulAut.congr e a) ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  have hU : ∀ x ∈ unipotent (binaryParameters n hn), MulAut.congr e a x = x := by
    intro x hx
    have hx' : x ∈ (Q : Subgroup (BinaryCarrier n hn)).map e.toMonoidHom := hm.symm ▸ hx
    obtain ⟨y, hy, rfl⟩ := hx'
    change e (a (e.symm (e y))) = e y
    rw [e.symm_apply_apply, hfix y hy]
  obtain ⟨x, hx⟩ := triality_standard_inner n hn (MulAut.congr e a) hb hU
  refine ⟨e.symm x, (MulAut.congr e).injective ?_⟩
  rw [MulAut.congr_conj, e.apply_symm_apply]
  exact hx

open Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
  {α : MulAut L} {P : Sylow 2 L}

/-- Every marked triality involution is inner, including the binary endpoint. -/
theorem MarkedInvolution.triality_inner (d : MarkedInvolution α P) {f : ℕ}
    (hf : 1 ≤ f) (h : IsTrialityGroupAt (2 ^ f) (L ⧸ center L)) :
    α ∈ (MulAut.conj (G := L)).range := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff (L ⧸ center L) f (by omega)).mp h
  obtain ⟨ho, _, Q, hQ⟩ := d.centralQuotient_model_inputs e
  apply (d.inner_and_center_of_quotient_inner e ?_).1
  exact triality_sylow_inner f (by omega) Q (MulAut.centralQuotientAction e α)
    (by simpa only [ho] using pow_orderOf_eq_one (MulAut.centralQuotientAction e α)) hQ

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
