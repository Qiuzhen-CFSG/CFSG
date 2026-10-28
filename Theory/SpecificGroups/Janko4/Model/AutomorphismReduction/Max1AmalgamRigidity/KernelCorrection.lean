module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1AmalgamRigidity.Core
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1AmalgamRigidity.Assembly
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore
public import Theory.Mathieu.M24.Properties.OuterRestriction
import Mathlib.Tactic.Group

/-!
# Correcting an automorphism on the literal max1 kernel

Every automorphism of the actual Janko matrix model can be corrected by an
inner automorphism to fix the embedded max1 kernel pointwise. Odd index
promotes the image of a local Sylow two-subgroup to an ambient Sylow. Sylow
conjugacy and the characteristicity of the intrinsic kernel then give a first
correction preserving its actual ambient image E. The equality N(E) = M
makes this correction preserve the literal max1 subgroup as well.

Restrict to M and descend to its quotient by K. Transport along the actual
quotient equivalence with the Witt-design M24, whose automorphisms are inner,
and lift a quotient conjugator back to M. The corrected restriction is the
identity on M/K, so the proved commutant theorem makes it fix K pointwise.
The two left-conjugation corrections combine as
`conj(m⁻¹) * conj(s⁻¹) * alpha = conj((s * m)⁻¹) * alpha`.

This supplies the first correction premise of
`conj_surjective_of_local_corrections`; it asserts only kernel fixation.
Source context: GLS3 Table 5.3i, printed p.270, with the literal ATLAS
max1 words and matrix provenance documented in `Cardinality.Subgroup`.
-/

set_option backward.isDefEq.respectTransparency true
public section

namespace Janko4.Max1AmalgamRigidity
open Subgroup
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup
  Cardinality.localKernel Cardinality.localX Cardinality.localY Cardinality.localKernelSeed

/-- Align ambient Sylows and transport intrinsic kernel characteristicity. -/
private theorem kernel_stabilizing_correction (alpha : MulAut Model) :
    ∃ s : Model, E.map (MulAut.conj s⁻¹ * alpha).toMonoidHom = E := by
  let P : Sylow 2 M := default
  let U : Subgroup Model := P.toSubgroup.map M.subtype
  have hodd : ¬ 2 ∣ U.index := by
    change ¬ 2 ∣ (P.toSubgroup.map M.subtype).index
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul P.not_dvd_index
      OuterReduction.max1_odd_index_unconditional
  let S : Sylow 2 Model := (P.isPGroup'.map M.subtype).toSylow hodd
  let T := S.mapSurjective (f := alpha.toMonoidHom) alpha.surjective
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq Model T S
  let beta : MulAut Model := MulAut.conj t * alpha
  have hbetaU : U.map beta.toMonoidHom = U := by
    change U.map ((MulAut.conj t).toMonoidHom.comp alpha.toMonoidHom) = U
    rw [← map_map]
    exact congrArg Sylow.toSubgroup ht
  let q : P ≃* U := P.toSubgroup.equivMapOfInjective M.subtype M.subtype_injective
  let gamma : MulAut U := (beta.subgroupMap U).trans (MulEquiv.subgroupCongr hbetaU)
  let u : MulAut P := (q.trans gamma).trans q.symm
  have hu (p : P) : ((u p : M) : Model) = beta (p : M) := by
    exact congrArg U.subtype (q.apply_symm_apply (gamma (q p)))
  have hKP : K ≤ P.toSubgroup :=
    (IsPGroup.of_card (n := 11)
      (Cardinality.localKernel_card matrixA_mul_self matrixB_pow_four)).le_sylow_of_normal P
  have hchar := LocalStructure.localKernel_sylow_characteristic P
  have hE : E.map beta.toMonoidHom = E := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨e, he, rfl⟩
      obtain ⟨k, hk, rfl⟩ := (mem_map (f := M.subtype) (K := K)).mp he
      let p : P := ⟨k, hKP hk⟩
      have hp : u p ∈ K.subgroupOf P.toSubgroup :=
        (characteristic_iff_le_comap.mp hchar u) hk
      exact mem_map.mpr ⟨u p, hp, hu p⟩
    · exact (Nat.card_congr (beta.subgroupMap E).toEquiv).le
  exact ⟨t⁻¹, by simpa only [inv_inv] using hE⟩

/-- Lift a conjugator from the actual Mathieu quotient to the literal max1. -/
private theorem quotient_inner_lift (phi : MulAut M)
    (hK : K.map phi.toMonoidHom = K) :
    ∃ m : M, ∀ g : M,
      QuotientGroup.mk' K (phi g) =
        QuotientGroup.mk' K m * QuotientGroup.mk' K g * (QuotientGroup.mk' K m)⁻¹ := by
  let theta : MulAut (M ⧸ K) := QuotientGroup.congr K K phi hK
  let e : M ⧸ K ≃* Sporadic.Mathieu.M24 :=
    LocalStructure.localQuotientEquivM24 matrixA_mul_self matrixB_pow_four
  let psi : MulAut Sporadic.Mathieu.M24 := (e.symm.trans theta).trans e
  obtain ⟨c, hc⟩ := Sporadic.Mathieu.M24OuterRestriction.conj_surjective psi
  obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective K (e.symm c)
  refine ⟨m, fun g => ?_⟩
  have htheta : theta (QuotientGroup.mk' K g) = QuotientGroup.mk' K (phi g) := rfl
  have hh := DFunLike.congr_fun hc (e (QuotientGroup.mk' K g))
  have hh' : c * e (QuotientGroup.mk' K g) * c⁻¹ =
      e (QuotientGroup.mk' K (phi g)) := by
    simpa only [MulAut.conj_apply, psi, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, htheta] using hh
  apply e.injective
  rw [map_mul, map_mul, map_inv, hm, e.apply_symm_apply]
  exact hh'.symm

/-- Every ambient automorphism admits an inner correction fixing the literal
embedded max1 kernel pointwise, with no additional hypotheses. -/
theorem kernel_correction (alpha : MulAut Model) :
    ∃ g : Model, ∀ e ∈ E, (MulAut.conj g⁻¹ * alpha) e = e := by
  obtain ⟨s, hs⟩ := kernel_stabilizing_correction alpha
  let beta : MulAut Model := MulAut.conj s⁻¹ * alpha
  have hbetaE : E.map beta.toMonoidHom = E := hs
  have hbetaM : M.map beta.toMonoidHom = M := by
    have hn := E.map_equiv_normalizer_eq beta
    rwa [hbetaE, normalizer_E_eq] at hn
  let phi : MulAut M := (beta.subgroupMap M).trans (MulEquiv.subgroupCongr hbetaM)
  have hphi (m : M) : (phi m : Model) = beta m := rfl
  have hphiK : K.map phi.toMonoidHom = K := by
    apply map_injective M.subtype_injective
    rw [map_map]
    change K.map (beta.toMonoidHom.comp M.subtype) = E
    rw [← map_map]
    exact hbetaE
  obtain ⟨m, hm⟩ := quotient_inner_lift phi hphiK
  let delta : MulAut M := MulAut.conj m⁻¹ * phi
  have hdelta (k : K) : delta (k : M) = k := by
    apply Max1RelativeRigidity.fixes_kernel_of_quotient_fixed delta
    intro h
    change QuotientGroup.mk' K (m⁻¹ * phi h * (m⁻¹)⁻¹) = QuotientGroup.mk' K h
    rw [map_mul, map_mul, map_inv, inv_inv, hm h]
    group
  refine ⟨s * (m : Model), ?_⟩
  intro e he
  obtain ⟨k, hk, rfl⟩ := (mem_map (f := M.subtype) (K := K)).mp he
  have hd := congrArg M.subtype (hdelta ⟨k, hk⟩)
  change (m : Model)⁻¹ * beta k * ((m : Model)⁻¹)⁻¹ = (k : Model) at hd
  change (s * (m : Model))⁻¹ * alpha k * ((s * (m : Model))⁻¹)⁻¹ = (k : Model)
  change (m : Model)⁻¹ * (s⁻¹ * alpha k * (s⁻¹)⁻¹) * ((m : Model)⁻¹)⁻¹ = _ at hd
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using hd

end Janko4.Max1AmalgamRigidity
