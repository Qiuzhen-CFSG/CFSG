module
public import Theory.Representation.SelfDualFrobeniusDegree
public import Theory.Mathieu.M22.CoverDegreeFive
public import Theory.AtlasPort.Algebra.SplitOctonion.NormGeometry
public import Theory.AtlasPort.LinearGroups.G2.Basic
public import Theory.Representation.CentralCoverSelfDualFlag
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport

/-!
# Self-dual degree bounds for full M₂₂ covers

The actual eleven-by-five Frobenius subgroup lifts through the full central
cover by the proved multiplier prime bounds. A faithful self-dual action
has two disjoint five-element character orbits, forcing degree at least ten.
The octonion norm pairing excludes G₂ in characteristic two. The literal
Geck-to-Clifford comparison and faithful eight-dimensional natural Spin
action exclude binary triality. Both pairings are nondegenerate in
characteristic two; neither exclusion discards the covering center.

The source consumer is `Chapter4.Section04.OddLocalMathieu.SelfDualModels`,
in the p.623 odd-local comparison of Aschbacher--Smith 4.4.3. The character
argument is G.7.2(2), pp.347--348, with duality, and the native Frobenius
subgroup is H.12.1, p.394. Imported ATLAS and Clifford calculations retain
their own source attribution and licenses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M22CentralCover
/-- Every faithful self-dual representation of a full perfect M₂₂ cover
has degree at least ten away from characteristic eleven. -/
theorem selfDual_degree_ge_ten
    {F E V : Type*} [Field F] [Group E] [Finite E]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (f : PerfectCentralCovering.Cover E M22)
    (ρ : Representation F E V) (hρ : Function.Injective ρ)
    (h11 : (11 : F) ≠ 0) (he : ρ.Equiv ρ.dual) : 10 ≤ Module.finrank F V := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨v,hv⟩ := exists_prime_orderOf_dvd_card' (G := M22) 5 (by rw [m22_order]; decide)
  obtain ⟨K,hK,hn,hfree⟩ := m22_exists_eleven_five v hv
  have h5cop : Nat.Coprime 5 (Nat.card f.toMonoidHom.ker) :=
    (Nat.prime_five.coprime_iff_not_dvd).mpr
      (M22UniversalMultiplier.not_dvd_kernel_of_ne_two_three f (by decide) (by decide) (by decide))
  have h11cop : Nat.Coprime 11 (Nat.card f.toMonoidHom.ker) :=
    (Nat.prime_eleven.coprime_iff_not_dvd).mpr
      (M22UniversalMultiplier.not_dvd_kernel_of_ne_two_three f (by decide) (by decide) (by decide))
  obtain ⟨C,hC,hCm,_,_,hiC⟩ := exists_prime_lift_of_central_coprime
    f.toMonoidHom f.surjective f.ker_le_center h5cop (zpowers v)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,hv,pow_one]))
  obtain ⟨P,hP,hPm,hN,_,hiP⟩ := exists_prime_lift_of_central_coprime
    f.toMonoidHom f.surjective f.ker_le_center h11cop K
    (IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hK))
  have hCc : Nat.card C = 5 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hiC).toEquiv]
    rw [MonoidHom.range_comp,range_subtype]
    rw [hCm,Nat.card_zpowers,hv]
  have hPc : Nat.card P = 11 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hiP).toEquiv]
    rw [MonoidHom.range_comp,range_subtype]
    rw [hPm,hK]
  let : IsCyclic P := isCyclic_of_prime_card hPc
  let : Nontrivial P := (Finite.one_lt_card_iff_nontrivial (α := P)).mp (by rw [hPc]; decide)
  have hCP : C ≤ normalizer (P : Set E) := by
    rw [←hN,←map_le_iff_le_comap,hCm]
    exact hn
  have hfreeP (c : C) (hc : c ≠ 1) (k : P)
      (hck : (c : E) * (k : E) * (c : E)⁻¹ = k) : k = 1 := by
    apply hiP
    change f.toMonoidHom (k : E) = f.toMonoidHom 1
    rw [map_one]
    apply hfree (f.toMonoidHom c) (hCm ▸ mem_map_of_mem _ c.property)
    · intro he
      exact hc (hiC (he.trans (map_one f.toMonoidHom).symm))
    · exact hPm ▸ mem_map_of_mem _ k.property
    · simpa only [map_mul,map_inv] using congrArg f.toMonoidHom hck
  simpa only [hCc] using
    Representation.double_card_le_finrank_of_selfDual_frobenius_of_field ρ P C
      (by rw [hPc]; decide) (by rw [hCc]; decide) hρ
      (by simpa only [hPc,Nat.cast_ofNat] using h11) hCP hfreeP he

end Sporadic.Mathieu.M22CentralCover

namespace Sporadic.Mathieu.M22CentralCover
open Subgroup Theory.GroupTheory Sporadic.Mathieu

private def cover {B : Type*} [Group B] [IsQuasisimple B]
    (e : (B ⧸ center B) ≃* M22) : PerfectCentralCovering.Cover B M22 where
  toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
  isPerfect := inferInstance
  ker_le_center := by rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']

/-- The norm pairing on the octonion eight-space excludes every full
quasisimple M₂₂ cover from a characteristic-two G₂ model. -/
theorem no_embedding_g2 {F B : Type*} [Field F] [CharP F 2]
    [Group B] [Finite B] [IsQuasisimple B]
    (e : (B ⧸ center B) ≃* M22) (j : B →* Atlas.G2.Model F)
    (hj : Function.Injective j) : False := by
  let r := (Atlas.G2.representation F).comp j
  let ρ : Representation F B (Atlas.SplitOctonion.Carrier F) := {
    toFun b := (r b).toLinearMap
    map_one' := congrArg LinearEquiv.toLinearMap r.map_one
    map_mul' b c := congrArg LinearEquiv.toLinearMap (r.map_mul b c) }
  have hρ : Function.Injective ρ := by
    intro b c he
    apply hj
    apply Subtype.ext
    apply LinearEquiv.ext
    exact LinearMap.congr_fun he
  have hpair : Function.Injective (@Atlas.SplitOctonion.normPolar F _) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    exact Atlas.SplitOctonion.normPolar_nondegenerate (fun y => congrArg (fun l => l y) hx)
  let d : ρ.Equiv ρ.dual := Representation.BinaryCoverSocle.selfDualOfPairing ρ
    Atlas.SplitOctonion.normPolar hpair (by
      intro b v w
      have hh := Atlas.SplitOctonion.automorphism_normPolar (j b) v (ρ b⁻¹ w)
      change Atlas.SplitOctonion.normPolar (ρ b v) (ρ b (ρ b⁻¹ w)) = _ at hh
      simpa only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply] using hh)
  have hb := M22CentralCover.selfDual_degree_ge_ten (cover e) ρ hρ
    (fun hh => (by decide : ¬2∣11) ((CharP.cast_eq_zero_iff F 2 11).mp hh)) d
  rw [Atlas.G2.carrier_finrank] at hb
  omega

open Theory.AlgebraicGroup Triality.SimplyConnected Triality.Standard
open Triality.BinaryDegree.CarrierTransport

/-- The faithful natural Spin action excludes every full quasisimple M₂₂
cover from the genuine binary triality carrier, including exponent one. -/
theorem no_embedding_binary_triality {B : Type*}
    [Group B] [Finite B] [IsQuasisimple B]
    (e : (B ⧸ center B) ≃* M22) (n : ℕ) (hn : 0 < n)
    (j : B →* BinaryCarrier n hn) (hj : Function.Injective j) : False := by
  let k := AlgebraicClosure (ZMod 2)
  let i := ((fixedSubgroup (binaryParameters n hn)).subtype.comp
    (elementarySubgroup (binaryParameters n hn)).subtype).comp
      (binaryElementaryEquiv n hn).symm.toMonoidHom
  have hi : Function.Injective i :=
    (Subgroup.subtype_injective _).comp ((Subgroup.subtype_injective _).comp
      (binaryElementaryEquiv n hn).symm.injective)
  let f := (GeckSpin.finiteComparison k (coefficientEmbedding k n hn)).comp (i.comp j)
  have hf : Function.Injective f := (GeckSpin.finiteComparison_injective k _).comp (hi.comp hj)
  let r := (naturalAction k).comp f
  have hr : Function.Injective r := (naturalAction_injective k).comp hf
  let ρ : Representation k B (QuadraticSpace k) := {
    toFun b := (r b).val.toLinearMap
    map_one' := congrArg (fun g : quadraticIsometrySubgroup (quadraticForm k) => g.val.toLinearMap) r.map_one
    map_mul' b c := congrArg (fun g : quadraticIsometrySubgroup (quadraticForm k) => g.val.toLinearMap)
      (r.map_mul b c) }
  have hρ : Function.Injective ρ := by
    intro b c he
    apply hr
    apply Subtype.ext
    apply LinearEquiv.ext
    exact LinearMap.congr_fun he
  let Q := quadraticForm k
  have hpair : Function.Injective Q.polarBilin :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mpr
      ((standardHyperbolicSplit (k := k) 4).polarBilin_surjective)
  have hpres (b : B) (v w : QuadraticSpace k) :
      Q.polarBilin ((r b).val v) ((r b).val w) = Q.polarBilin v w := by
    have hq := (mem_quadraticIsometrySubgroup _ _).mp (r b).property
    change ∀ v, Q ((r b).val v) = Q v at hq
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,←map_add,hq]
  let d : ρ.Equiv ρ.dual := Representation.BinaryCoverSocle.selfDualOfPairing ρ
    Q.polarBilin hpair (by
      intro b v w
      have hh := hpres b v (ρ b⁻¹ w)
      change Q.polarBilin (ρ b v) (ρ b (ρ b⁻¹ w)) = _ at hh
      simpa only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply] using hh)
  have hb := M22CentralCover.selfDual_degree_ge_ten (cover e) ρ hρ
    (fun hh => (by decide : ¬2∣11) ((CharP.cast_eq_zero_iff k 2 11).mp hh)) d
  have hd : Module.finrank k (QuadraticSpace k) = 8 := by
    change Module.finrank k ((Fin 4 → k) × (Fin 4 → k)) = 8
    simp [Module.finrank_prod]
  omega
end Sporadic.Mathieu.M22CentralCover
