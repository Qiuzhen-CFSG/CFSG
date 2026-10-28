module
public import Theory.Representation.PSL3Two.NaturalDualNormalizerMarking
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MiddleRecognition
public import Theory.SpecificGroups.BinaryLinear.FiveTwoLocalFive
public import Theory.Representation.BinaryGroupAction
public import Theory.ElementaryAbelian.Quotient

/-!
# Excluding the linear-five placed component for the binary doubled orbit

A normal natural--dual SL₃(2) action with a two-group kernel forces the
ambient action to embed in Aut(SL₃(2)), whose order is not divisible by nine.
In GL₅(2), the fixed space of an elementary subgroup of order 64 supplies a
proper maximal parabolic. If both the actor and the elementary subgroup are
normal there, that subgroup is the parabolic's entire two-core. The core is
self-centralizing, whereas every maximal parabolic has order divisible by
nine, giving a contradiction. Both middle dimensions and arbitrary flags
are retained.

The Chapter12 companion discharges the parabolic normality premise using
uniqueness of the original odd-actor residual's maximal two-local overgroup.
It retains the full component center and the whole marked orbit.
Source: Aschbacher--Smith 4.4.12, printed pp.621--622, as used in 7.3.4 and
7.6.1, pp.699,702, refs/quasithin.pdf.
-/

open Subgroup Representation
open scoped IsMulCommutative
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedLinear
open BinaryLinearThree

private theorem not_nine {P : Type*} [_root_.Group P] [Finite P]
    (η : Representation (ZMod 2) P NaturalDual.Space)
    (B : Subgroup P) [B.Normal]
    (q : B →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (he : ∀ b : B, η b = NaturalDual.action (q b))
    (hk : IsPGroup 2 η.ker) : ¬ 9 ∣ Nat.card P := by
  obtain ⟨a,ha,hker⟩ := NaturalDual.exists_automorphism_marking η B q hq he
  have hka : a.ker = η.ker := by ext x; exact hker x
  have hkr : IsPGroup 2 a.ker := hka.symm ▸ hk
  obtain ⟨n,hn⟩ := hkr.exists_card_eq
  have hc := a.ker.card_mul_index
  rw [index_ker,hn] at hc
  intro hd
  have hr : 9 ∣ Nat.card a.range :=
    ((by decide : Nat.Coprime 9 2).pow_right n).dvd_of_dvd_mul_left (hc.symm ▸ hd)
  have h9 := hr.trans a.range.card_subgroup_dvd_card
  rw [Nat.card_congr (MulAut.congr Matrix.PSL3Two.equiv).toEquiv,
    Matrix.PSL3Two.Automorphisms.card_aut] at h9
  norm_num at h9

private theorem not_nine_normal {P : Type*} [_root_.Group P] [Finite P]
    (U B : Subgroup P) [IsElementaryAbelian 2 U] [U.Normal] [B.Normal]
    (q : B →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (e : Additive U ≃ₗ[ZMod 2] NaturalDual.Space)
    (he : ∀ b : B, ∀ v : U,
      e (Additive.ofMul (MulAut.conjNormal b.val v)) =
        NaturalDual.action (q b) (e (Additive.ofMul v)))
    (hc : IsPGroup 2 (centralizer (U : Set P))) : ¬ 9 ∣ Nat.card P := by
  let ρ := elementaryRepresentation (p:=2) (MulAut.conjNormal : P →* MulAut U)
  let η : Representation (ZMod 2) P NaturalDual.Space := {
    toFun p := e.toLinearMap.comp ((ρ p).comp e.symm.toLinearMap)
    map_one' := by
      apply LinearMap.ext
      intro v
      change e (ρ 1 (e.symm v)) = v
      rw [map_one]
      exact e.apply_symm_apply v
    map_mul' p r := by
      apply LinearMap.ext
      intro v
      change e (ρ (p*r) (e.symm v)) = e (ρ p (e.symm (e (ρ r (e.symm v)))))
      rw [e.symm_apply_apply,map_mul]; rfl }
  have hk : η.ker ≤ centralizer (U : Set P) := by
    intro p hp
    apply mem_centralizer_iff.mpr
    intro v hv
    have hh := LinearMap.congr_fun hp (e (Additive.ofMul (⟨v,hv⟩ : U)))
    change e (ρ p (e.symm (e (Additive.ofMul (⟨v,hv⟩ : U))))) =
      e (Additive.ofMul (⟨v,hv⟩ : U)) at hh
    rw [e.symm_apply_apply] at hh
    have hh' := congrArg (fun x : Additive U => (x.toMul : P)) (e.injective hh)
    change p * v * p⁻¹ = v at hh'
    exact (mul_inv_eq_iff_eq_mul.mp hh').symm
  apply not_nine η B q hq _ (hc.to_le hk)
  intro b
  apply LinearMap.ext
  intro v
  change e (ρ b.val (e.symm v)) = NaturalDual.action (q b) v
  rw [show ρ b.val (e.symm v) = Additive.ofMul (MulAut.conjNormal b.val (e.symm v).toMul) from rfl,
    he]
  exact congrArg (NaturalDual.action (q b)) (e.apply_symm_apply v)

open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.MaximalOvergroups
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private theorem gl_card (n : ℕ) : Nat.card (LinearGroup n) =
    ∏ i : Fin n, (2^n - 2^i.val) := by
  rw [←Nat.card_congr (matrixEquivLinear n).toEquiv,Matrix.card_GL_field]
  simp

private theorem parabolic_nine (b : FiveBasis) (i : Fin 4) :
    9 ∣ Nat.card (flagStabilizer b {i}) := by
  apply dvd_trans _ (card_quotient_dvd_card (pCore 2 (flagStabilizer b {i})))
  rw [Nat.card_congr (singletonQuotientEquiv b i).toEquiv,Nat.card_prod,gl_card,gl_card]
  fin_cases i <;> decide

private theorem endpoint_five (b : FiveBasis) (i : Fin 4) (hi : i = 0 ∨ i = 3) :
    5 ∣ Nat.card (flagStabilizer b {i}) := by
  apply dvd_trans _ (card_quotient_dvd_card (pCore 2 (flagStabilizer b {i})))
  rw [Nat.card_congr (singletonQuotientEquiv b i).toEquiv,Nat.card_prod,gl_card,gl_card]
  rcases hi with rfl | rfl <;> decide

private theorem core_card_middle (b : FiveBasis) (i : Fin 4) (hi : i = 1 ∨ i = 2) :
    Nat.card (pCore 2 (flagStabilizer b {i})) ≤ 64 := by
  let e := (middle_flag_equiv b i hi).some.trans FiveParabolicRadical.matrixParabolicEquiv
  have hc := FiveParabolicRadical.normal_two_subgroup_card
    (pCore 2 (parabolic FiveParabolicRadical.plane)) pCore_isPGroup
  have he := Nat.card_congr ((pCore 2 (flagStabilizer b {i})).equivMapOfInjective
    e.toMonoidHom e.injective).toEquiv
  rw [show (pCore 2 (flagStabilizer b {i})).map e.toMonoidHom =
    pCore 2 (parabolic FiveParabolicRadical.plane) from pCore_map_iso 2 e] at he
  omega

private theorem normal_sixtyFour_core (b : FiveBasis) (i : Fin 4)
    (U : Subgroup (flagStabilizer b {i})) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 64) : U = pCore 2 (flagStabilizer b {i}) := by
  have hle : U ≤ pCore 2 (flagStabilizer b {i}) :=
    le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩
  by_cases hi : i = 1 ∨ i = 2
  · exact eq_of_le_of_card_ge hle (by rw [hU]; exact core_card_middle b i hi)
  · have hend : i = 0 ∨ i = 3 := by fin_cases i <;> simp_all
    let P := flagStabilizer b {i}
    let E := U.map P.subtype
    have hEP : E ≤ P := map_subtype_le _
    have hn : P ≤ normalizer (E : Set (LinearGroup 5)) := by
      apply (normal_subgroupOf_iff_le_normalizer hEP).mp
      change ((U.map P.subtype).comap P.subtype).Normal
      rw [comap_map_eq_self_of_injective P.subtype_injective]
      infer_instance
    have hsmall := FiveTwoLocalFive.card_le_sixteen E
      ((IsElementaryAbelian.isPGroup 2 U).map P.subtype)
      ((endpoint_five b i hend).trans (card_dvd_of_le hn))
    rw [card_map_of_injective P.subtype_injective,hU] at hsmall
    omega

private theorem no_flag_natural_dual (b : FiveBasis) (i : Fin 4)
    (U B : Subgroup (flagStabilizer b {i})) [U.Normal] [B.Normal]
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 64)
    (q : B →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (e : Additive U ≃ₗ[ZMod 2] NaturalDual.Space)
    (he : ∀ r : B, ∀ v : U,
      e (Additive.ofMul (MulAut.conjNormal r.val v)) =
        NaturalDual.action (q r) (e (Additive.ofMul v))) : False := by
  have hcore := normal_sixtyFour_core b i U hU
  have hc : centralizer (U : Set (flagStabilizer b {i})) ≤ U := by
    rw [hcore]
    let c := singletonEquiv b i
    have hh := centralizer_parabolic_twoCore_le (flagSpace_ne_bot b i) (flagSpace_ne_top b i)
    intro x hx
    have hcx : c x ∈ centralizer (pCore 2 (parabolic (flagSpace b i)) : Set _) := by
      rw [←pCore_map_iso 2 c]
      rintro _ ⟨y,hy,rfl⟩
      exact congrArg c (hx y hy)
    have hm := hh hcx
    rw [←pCore_map_iso 2 c] at hm
    exact (mem_map_iff_mem c.injective).mp hm
  exact not_nine_normal U B q hq e he
    ((IsElementaryAbelian.isPGroup 2 U).to_le hc) (parabolic_nine b i)

private def linearize {U V : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup V] [Module (ZMod 2) V]
    (e : Multiplicative U ≃* Multiplicative V) : U ≃ₗ[ZMod 2] V :=
  let a : U ≃+ V := {
    toFun v := (e (Multiplicative.ofAdd v)).toAdd
    invFun v := (e.symm (Multiplicative.ofAdd v)).toAdd
    left_inv v := e.symm_apply_apply v
    right_inv v := e.apply_symm_apply v
    map_add' v w := congrArg Multiplicative.toAdd (e.map_mul
      (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
  { a with map_smul' := ZMod.map_smul a }

/-- A faithful whole natural--dual orbit cannot lie in GL₅(2) when every
maximal parabolic containing its full actor normalizes both actor and orbit.
The source application proves this relative normality by ambient uniqueness. -/
public theorem no_linear_five_natural_dual
    {R : Type*} [_root_.Group R]
    (f : R →* LinearGroup 5) (q : R →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (u : Multiplicative NaturalDual.Space →* LinearGroup 5) (hu : Function.Injective u)
    (ha : ∀ r v, f r * u (Multiplicative.ofAdd v) * (f r)⁻¹ =
      u (Multiplicative.ofAdd (NaturalDual.action (q r) v)))
    (hn : ∀ (b : FiveBasis) (i : Fin 4), f.range ≤ flagStabilizer b {i} →
      (f.range.subgroupOf (flagStabilizer b {i})).Normal ∧
      u.range ≤ flagStabilizer b {i} ∧
      (u.range.subgroupOf (flagStabilizer b {i})).Normal) : False := by
  let E := u.range
  let : IsElementaryAbelian 2 (Multiplicative NaturalDual.Space) :=
    Representation.BinaryGroupAction.elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_surjective
    u.rangeRestrict u.rangeRestrict_surjective
  have hE : Nat.card E = 64 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hu).toEquiv]
    change Nat.card NaturalDual.Space = 64
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2)]
    norm_num [NaturalDual.Space,Module.finrank_prod]
  have hnorm : f.range ≤ normalizer (E : Set (LinearGroup 5)) := by
    apply le_set_normalizer_iff.mpr
    rintro _ ⟨r,rfl⟩ _ ⟨v,rfl⟩
    exact ⟨Multiplicative.ofAdd (NaturalDual.action (q r) v.toAdd),(ha r v.toAdd).symm⟩
  have hne : E ≠ ⊥ := by intro hh; rw [hh,card_bot] at hE; omega
  let W := BinaryLinear.fixedSpace E
  have hW0 : W ≠ ⊥ := BinaryLinear.fixedSpace_ne_bot (by norm_num [Space,Nat.card_fun])
    (IsElementaryAbelian.isPGroup 2 E)
  have hWt : W ≠ ⊤ := BinaryLinear.fixedSpace_ne_top hne
  have hlo : 0 < Module.finrank (ZMod 2) W := by
    have hh := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.mpr hW0)
    simpa only [finrank_bot] using hh
  have hhi := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hWt)
  rw [finrank_top,Module.finrank_fin_fun] at hhi
  let i : Fin 4 := ⟨Module.finrank (ZMod 2) W - 1,by omega⟩
  obtain ⟨b,hb⟩ := GeometricFlags.exists_flagSpace W i (by dsimp [i]; omega)
  have hP : flagStabilizer b {i} = parabolic W := by rw [flagStabilizer_singleton,hb]
  have hfP : f.range ≤ flagStabilizer b {i} := by
    rw [hP]
    exact hnorm.trans (normalizer_le_parabolic_fixedSpace E)
  obtain ⟨hB,hEP,hU⟩ := hn b i hfP
  let P := flagStabilizer b {i}
  let B := f.range.subgroupOf P
  let U := E.subgroupOf P
  let := hB
  let := hU
  let eB : B ≃* f.range := subgroupOfEquivOfLe hfP
  let eU : U ≃* E := subgroupOfEquivOfLe hEP
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_surjective eU.symm.toMonoidHom eU.symm.surjective
  have hk : f.rangeRestrict.ker ≤ q.ker := by
    intro r hr
    have hfr : f r = 1 := congrArg Subtype.val hr
    apply NaturalDual.action_injective
    apply LinearMap.ext
    intro v
    have he := ha r v
    rw [hfr,one_mul,inv_one,mul_one] at he
    have hh := congrArg Multiplicative.toAdd (hu he)
    change v = NaturalDual.action (q r) v at hh
    simpa only [map_one,Module.End.one_apply] using hh.symm
  let qB : f.range →* BinaryLinearThree.Group :=
    f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨q,hk⟩
  have hqB : Function.Surjective qB := by
    intro g
    obtain ⟨r,rfl⟩ := hq g
    exact ⟨f.rangeRestrict r,by simp [qB]⟩
  let v : Multiplicative NaturalDual.Space ≃* U := (MonoidHom.ofInjective hu).trans eU.symm
  let c := linearize ((MulEquiv.toMultiplicative_toAdditive :
    Multiplicative (Additive U) ≃* U).trans v.symm)
  apply no_flag_natural_dual b i U B
    ((Nat.card_congr eU.toEquiv).trans hE) (qB.comp eB.toMonoidHom)
    (hqB.comp eB.surjective) c
  intro r x
  obtain ⟨s,hs⟩ := f.rangeRestrict_surjective (eB r)
  obtain ⟨w,rfl⟩ := v.surjective x
  have hqr : qB (eB r) = q s := by rw [←hs]; simp [qB]
  have hfr : f s = r.val.val := congrArg Subtype.val hs
  have hc (z : Multiplicative NaturalDual.Space) : c (Additive.ofMul (v z)) = z.toAdd :=
    v.symm_apply_apply z
  have hact : MulAut.conjNormal r.val (v w) =
      v (Multiplicative.ofAdd (NaturalDual.action (q s) w.toAdd)) := by
    apply Subtype.ext
    apply Subtype.ext
    change r.val.val * u w * r.val.val⁻¹ = _
    rw [←hfr]
    exact ha s w.toAdd
  rw [hact,hc,hc]
  change _ = NaturalDual.action (qB (eB r)) w.toAdd
  rw [hqr]
  rfl
end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedLinear
end
