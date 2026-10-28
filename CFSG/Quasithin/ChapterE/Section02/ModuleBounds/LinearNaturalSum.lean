module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.LinearEquality.NaturalLift
public import Theory.SpecificGroups.SL2.LineBorelResidual
public import Theory.GroupTheory.PerfectCentralCoverAbelianSylow
public import Theory.Representation.SL2SylowFixedRecognition.Complementary

/-!
# Natural sums on the original two-conjugate linear core

Borel commutators move the whole Sylow image. Therefore the quotient by
P = (V intersect J)(V^g intersect J) is perfect. Its Sylow preimage is
abelian, and transfer kills the central two-kernel, proving J = P.
This includes the exceptional field of four elements without a multiplier
assumption. The literal P/Z action consequently descends through X/J.
Its two complementary Sylow fixed spaces give natural coordinates by G.1.7,
so the defining field degree divides the original actor rank.

The HermitianSourceLinearRanks consumer uses this to prove the missing
E.2.14 rank bound on the actual selected pair.
Source: Aschbacher–Smith E.2.14(2,3,7), printed pp.226–228, and
G.1.7, printed pp.329–330 (refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory NoncentralChiefRefinement Representation Representation.BinaryOffender
open scoped Matrix MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses

private theorem sylow_commutator_normalizer
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (R : Sylow 2 SL(2,F)) (hq : 4 ≤ Nat.card F) :
    ⁅(R : Subgroup SL(2,F)), normalizer (R : Set SL(2,F))⁆ = R := by
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq SL(2,F)
    (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2) R
  have hR : (R : Subgroup SL(2,F)) =
      (Matrix.SpecialLinearGroup.upperUnipotent F).map (MulAut.conj a).toMonoidHom :=
    (congrArg Sylow.toSubgroup ha).symm
  change ⁅(R : Subgroup SL(2,F)), normalizer ((R : Subgroup SL(2,F)) : Set SL(2,F))⁆ = R
  rw [hR,←map_equiv_normalizer_eq,←map_commutator,
    Matrix.SpecialLinearGroup.commutator_upperUnipotent_rankOneBorel hq]

/-- The selected linear-two core is exactly the product of its two original
intersections. Abelian Sylow transfer includes the exceptional field four. -/
theorem linear_pair_core_eq
    {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
    {T : Sylow 2 X} {V M : Subgroup X} {g : X}
    (h : TwoConjugate.Hypotheses T V M g)
    (hMN : M ≤ normalizer (V : Set X))
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card F = 2^m)
    (ξ : (X ⧸ TwoConjugate.J M) ≃* SL(2,F))
    (R : Sylow 2 SL(2,F))
    (hVS : V.map (ξ.toMonoidHom.comp (QuotientGroup.mk' (TwoConjugate.J M))) = R)
    (hMS : M.map (ξ.toMonoidHom.comp (QuotientGroup.mk' (TwoConjugate.J M))) =
      normalizer (R : Set SL(2,F))) :
    pCore 2 X = TwoConjugate.P V M g := by
  let := h.core_geometry.1
  let := h.elementary
  let P := TwoConjugate.P V M g
  let J := TwoConjugate.J M
  let q := QuotientGroup.mk' P
  have hPJ : P ≤ J := h.P_le_twoCore.trans h.twoCore_le_J
  let f : (X ⧸ P) →* SL(2,F) := QuotientGroup.lift P
    (ξ.toMonoidHom.comp (QuotientGroup.mk' J)) (by
      intro x hx
      change ξ (QuotientGroup.mk' J x) = 1
      exact ξ.map_eq_one_iff.mpr ((QuotientGroup.eq_one_iff x).mpr (hPJ hx)))
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨y,rfl⟩ := ξ.surjective z
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective J y
    exact ⟨q x,rfl⟩
  have hk : f.ker = J.map q := by
    apply comap_injective (QuotientGroup.mk'_surjective P)
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hPJ]
    ext x
    change ξ (QuotientGroup.mk' J x) = 1 ↔ x ∈ J
    rw [ξ.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hc : f.ker ≤ center (X ⧸ P) := by
    rw [hk]
    exact (map_mk_le_center_iff _ _).mpr (by rw [commutator_comm]; exact h.commutator_J_le_P)
  have hp : IsPGroup 2 f.ker := by
    rw [hk,show J = pCore 2 X from h.J_eq_twoCore_of_linear_two m hm hcard ξ]
    exact pCore_isPGroup.map q
  let E := V.map q
  let N := M.map q
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map q
  have hcomp : f.comp q = ξ.toMonoidHom.comp (QuotientGroup.mk' J) := by ext x; rfl
  have hER : E.map f = R := by dsimp only [E]; rw [map_map,hcomp]; exact hVS
  have hNR : N.map f = normalizer (R : Set SL(2,F)) := by
    dsimp only [N]; rw [map_map,hcomp]; exact hMS
  have hEN : N ≤ normalizer (E : Set (X ⧸ P)) :=
    (map_mono hMN).trans (V.le_normalizer_map q)
  have hEK : E ⊓ f.ker = ⊥ := by
    apply bot_unique
    rintro _ ⟨⟨v,hv,rfl⟩,hkf⟩
    have hvJ : v ∈ J := (QuotientGroup.eq_one_iff v).mp (ξ.map_eq_one_iff.mp hkf)
    exact (QuotientGroup.eq_one_iff v).mpr (show v ∈ P from (show TwoConjugate.B V M ≤ P from le_sup_left) ⟨hvJ,hv⟩)
  have hinj : Function.Injective (f.comp E.subtype) := by
    intro a b hab
    apply Subtype.ext
    apply mul_inv_eq_one.mp
    apply hEK.le
    exact ⟨E.mul_mem a.property (E.inv_mem b.property),by
      change f (a.val*b.val⁻¹) = 1
      rw [map_mul,map_inv,show f a = f b from hab,mul_inv_cancel]⟩
  have hfour : 4 ≤ Nat.card F := by
    rw [hcard]
    exact (show 2^2 ≤ 2^m from Nat.pow_le_pow_right (by decide) hm)
  have hEd : E ≤ _root_.commutator (X ⧸ P) := by
    intro v hv
    have hvf : f v ∈ (⁅E,N⁆).map f := by
      rw [map_commutator,hER,hNR,sylow_commutator_normalizer R hfour]
      exact hER ▸ mem_map_of_mem f hv
    obtain ⟨w,hw,he⟩ := hvf
    have hwE := (le_normalizer_iff_commutator_le_left.mp hEN) hw
    have heq : w = v := congrArg Subtype.val (hinj
      (show (f.comp E.subtype) ⟨w,hwE⟩ = (f.comp E.subtype) ⟨v,hv⟩ from he))
    rw [←heq]
    exact (commutator_mono le_top le_top) hw
  have hperfect : _root_.commutator (X ⧸ P) = ⊤ := by
    apply top_unique
    rw [←MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective P),
      MonoidHom.range_eq_map,←h.generate,Subgroup.map_sup]
    apply sup_le hEd
    rintro _ ⟨w,⟨v,hv,rfl⟩,rfl⟩
    change q (g*v*g⁻¹) ∈ _
    rw [map_mul,map_mul,map_inv]
    exact (inferInstance : (_root_.commutator (X ⧸ P)).Normal).conj_mem _
      (hEd (mem_map_of_mem q hv)) (q g)
  let : Group.IsPerfect (X ⧸ P) := ⟨hperfect⟩
  have hab : IsMulCommutative ((R : Subgroup SL(2,F)).comap f) := by
    have hpre : (R : Subgroup SL(2,F)).comap f = E ⊔ f.ker := by
      rw [←hER,comap_map_eq]
    rw [hpre]
    apply le_centralizer_iff_isMulCommutative.mp
    apply sup_le
    · exact le_centralizer_iff.mpr (sup_le E.le_centralizer
        (hc.trans (center_le_centralizer _)))
    · exact le_centralizer_iff.mpr (sup_le
        (le_centralizer_iff.mp (hc.trans (center_le_centralizer _)))
        (hc.trans (center_le_centralizer _)))
  have hnd := PerfectCentralCovering.not_dvd_card_kernel_of_abelian_sylow_preimage f hf hc R hab
  have hzero : f.ker = ⊥ := card_eq_one.mp (hp.card_eq_or_dvd.resolve_right hnd)
  have hJP : J ≤ P := by
    have hmap : J.map q = ⊥ := hk.symm.trans hzero
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hmap
  exact le_antisymm ((h.J_eq_twoCore_of_linear_two m hm hcard ξ).symm ▸ hJP) h.P_le_twoCore

/-- The original central core quotient is a sum of natural modules, with
its original quotient map and matrix marking. -/
theorem linear_pair_natural_coordinates
    {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
    {T : Sylow 2 X} {V M : Subgroup X} {g : X}
    (h : TwoConjugate.Hypotheses T V M g)
    (hMN : M ≤ normalizer (V : Set X))
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card F = 2^m)
    (ξ : (X ⧸ TwoConjugate.J M) ≃* SL(2,F))
    (R : Sylow 2 SL(2,F))
    (hVS : V.map (ξ.toMonoidHom.comp (QuotientGroup.mk' (TwoConjugate.J M))) = R)
    (hMS : M.map (ξ.toMonoidHom.comp (QuotientGroup.mk' (TwoConjugate.J M))) =
      normalizer (R : Set SL(2,F))) :
    letI := h.Z_normal
    letI := h.core_geometry.1
    let q := QuotientGroup.mk' (TwoConjugate.Z V g)
    letI := h.quotient_direct_sum.1
    letI := ZMod.algebra F 2
    ∃ (d : ℕ) (e : Additive ((TwoConjugate.P V M g).map q) ≃ₗ[ZMod 2] (Fin d → Fin 2 → F)),
      ∀ x u j, e (normalRepresentation ((TwoConjugate.P V M g).map q) (q x) u) j =
        (ξ (QuotientGroup.mk' (TwoConjugate.J M) x)).val *ᵥ (e u j) := by
  let := h.Z_normal
  let := h.core_geometry.1
  let := h.elementary
  let q := QuotientGroup.mk' (TwoConjugate.Z V g)
  let U := (TwoConjugate.P V M g).map q
  let := h.quotient_direct_sum.1
  let := ZMod.algebra F 2
  let ρ := normalRepresentation U
  let σ := ρ.comp q
  have hJP : TwoConjugate.J M = TwoConjugate.P V M g :=
    (h.J_eq_twoCore_of_linear_two m hm hcard ξ).trans
      (linear_pair_core_eq h hMN m hm hcard ξ R hVS hMS)
  have hk : TwoConjugate.J M ≤ σ.ker := by
    intro x hx
    change σ x = 1
    apply LinearMap.ext
    intro u
    apply Additive.toMul.injective
    apply Subtype.ext
    change q x * (u.toMul : X ⧸ TwoConjugate.Z V g) * (q x)⁻¹ = u.toMul
    have hxU : q x ∈ U := mem_map_of_mem q (hJP ▸ hx)
    have he := congrArg Subtype.val (mul_comm (⟨q x,hxU⟩ : U) u.toMul)
    change q x * (u.toMul : X ⧸ TwoConjugate.Z V g) = (u.toMul : X ⧸ TwoConjugate.Z V g) * q x at he
    rw [he,mul_inv_cancel_right]
  let τ := quotientOfLEKer σ (TwoConjugate.J M) hk
  let ψ := τ.comp ξ.symm.toMonoidHom
  let π := ξ.toMonoidHom.comp (QuotientGroup.mk' (TwoConjugate.J M))
  have hact (x : X) (u : Additive U) : ψ (π x) u = ρ (q x) u := by
    simp only [ψ,τ,π,σ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      ξ.symm_apply_apply,quotientOfLEKer_apply]
  let Bq := (TwoConjugate.B V M).map q
  let Aq := (TwoConjugate.A V M g).map q
  let SB : Submodule (ZMod 2) (Additive U) :=
    AddSubgroup.toZModSubmodule 2 (Bq.subgroupOf U).toAddSubgroup
  let SA : Submodule (ZMod 2) (Additive U) :=
    AddSubgroup.toZModSubmodule 2 (Aq.subgroupOf U).toAddSubgroup
  have hB : fixedSpace ψ (R : Subgroup _) = SB := by
    ext u
    constructor
    · intro hu
      have hC : (u.toMul : X ⧸ TwoConjugate.Z V g) ∈ centralizer (V.map q : Set _) := by
        rw [mem_centralizer_iff]
        rintro _ ⟨v,hv,rfl⟩
        have he := hu ⟨π v, hVS ▸ mem_map_of_mem π hv⟩
        change ψ (π v) u = u at he
        rw [hact] at he
        have he' := congrArg (fun z : Additive U => (z.toMul : X ⧸ TwoConjugate.Z V g)) he
        exact mul_inv_eq_iff_eq_mul.mp he'
      change (u.toMul : X ⧸ TwoConjugate.Z V g) ∈ Bq
      have hb := h.quotient_fixed_eq_B
      change U ⊓ centralizer (V.map q : Set _) = Bq at hb
      exact hb ▸ (show (u.toMul : X ⧸ TwoConjugate.Z V g) ∈
        U ⊓ centralizer (V.map q : Set _) from ⟨u.toMul.property,hC⟩)
    · intro hu r
      have hr : (r : SL(2,F)) ∈ V.map π := hVS.symm ▸ r.property
      obtain ⟨v,hv,he⟩ := hr
      change ψ (r : SL(2,F)) u = u
      rw [←he,hact]
      apply Additive.toMul.injective
      apply Subtype.ext
      have hc : (u.toMul : X ⧸ TwoConjugate.Z V g) ∈
          U ⊓ centralizer (V.map q : Set _) := h.quotient_fixed_eq_B.symm ▸ hu
      change q v * (u.toMul : X ⧸ TwoConjugate.Z V g) * (q v)⁻¹ = u.toMul
      rw [(mem_centralizer_iff.mp hc.2) (q v) (mem_map_of_mem q hv),mul_inv_cancel_right]
  let R' : Sylow 2 SL(2,F) := π g • R
  have hA : fixedSpace ψ (R' : Subgroup _) = SA := by
    change fixedSpace ψ ((R : Subgroup _).map (MulAut.conj (π g)).toMonoidHom) = SA
    rw [SL2SylowFixedRecognition.fixedSpace_conjugate,hB]
    ext u
    constructor
    · rintro ⟨v,hv,rfl⟩
      change ((ψ (π g) v).toMul : X ⧸ TwoConjugate.Z V g) ∈ Aq
      rw [hact]
      obtain ⟨b,hb,he⟩ := hv
      change q g * (v.toMul : X ⧸ TwoConjugate.Z V g) * (q g)⁻¹ ∈ Aq
      change q b = (v.toMul : X ⧸ TwoConjugate.Z V g) at he
      rw [←he,←map_inv,←map_mul,←map_mul]
      exact mem_map_of_mem q (mem_map_of_mem (MulAut.conj g).toMonoidHom hb)
    · intro hu
      obtain ⟨a,⟨b,hb,rfl⟩,he⟩ := hu
      have hbU : q b ∈ U := mem_map_of_mem q ((show TwoConjugate.B V M ≤
        TwoConjugate.P V M g from le_sup_left) hb)
      refine ⟨Additive.ofMul ⟨q b,hbU⟩,mem_map_of_mem q hb,?_⟩
      rw [hact]
      apply Additive.toMul.injective
      apply Subtype.ext
      change q g * q b * (q g)⁻¹ = (u.toMul : X ⧸ TwoConjugate.Z V g)
      change q (g*b*g⁻¹) = (u.toMul : X ⧸ TwoConjugate.Z V g) at he
      simpa only [map_mul,map_inv] using he
  have hcompl : IsCompl SB SA := by
    constructor
    · apply disjoint_iff.mpr
      apply bot_unique
      intro u hu
      have hz : (u.toMul : X ⧸ TwoConjugate.Z V g) = 1 :=
        h.quotient_direct_sum.2.2.le hu
      exact Additive.toMul.injective (Subtype.ext hz)
    · apply codisjoint_iff.mpr
      apply top_unique
      intro u _
      obtain ⟨p,hp,he⟩ := u.toMul.property
      obtain ⟨b,hb,a,ha,hba⟩ := Set.mem_mul.mp
        (h.core_geometry.2.1 ▸ (show p ∈ (TwoConjugate.P V M g : Set X) from hp))
      have hbU : q b ∈ U := mem_map_of_mem q ((show TwoConjugate.B V M ≤
        TwoConjugate.P V M g from le_sup_left) hb)
      have haU : q a ∈ U := mem_map_of_mem q ((show TwoConjugate.A V M g ≤
        TwoConjugate.P V M g from le_sup_right) ha)
      apply Submodule.mem_sup.mpr
      refine ⟨Additive.ofMul ⟨q b,hbU⟩,mem_map_of_mem q hb,
        Additive.ofMul ⟨q a,haU⟩,mem_map_of_mem q ha,?_⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      change q b * q a = (u.toMul : X ⧸ TwoConjugate.Z V g)
      rw [←map_mul,hba,he]
  obtain ⟨d,e,he⟩ := SL2SylowFixedRecognition.natural_of_complementary_sylow_fixed
    ψ R R' (by rw [hB,hA]; exact hcompl) m hm hcard
  refine ⟨d,e,?_⟩
  intro x u j
  rw [←hact x u]
  exact he (π x) u j

/-- Every original actor rank in the selected PSL₂ family is a multiple
of the defining field degree. -/
theorem linear_pair_actor_rank_dvd
    {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
    {T : Sylow 2 X} {V M : Subgroup X} {g : X}
    (h : TwoConjugate.Hypotheses T V M g)
    (hMN : M ≤ normalizer (V : Set X))
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card F = 2^m)
    (ξ : (X ⧸ TwoConjugate.J M) ≃* SL(2,F))
    (R : Sylow 2 SL(2,F))
    (hVS : V.map (ξ.toMonoidHom.comp (QuotientGroup.mk' (TwoConjugate.J M))) = R)
    (hMS : M.map (ξ.toMonoidHom.comp (QuotientGroup.mk' (TwoConjugate.J M))) =
      normalizer (R : Set SL(2,F))) :
    m ∣ Nat.log 2 ((TwoConjugate.Z V g).relIndex (TwoConjugate.A V M g)) := by
  let := h.Z_normal
  let := h.core_geometry.1
  let := h.quotient_direct_sum.1
  let := ZMod.algebra F 2
  obtain ⟨d,e,_⟩ := linear_pair_natural_coordinates h hMN m hm hcard ξ R hVS hMS
  have hF : Module.finrank (ZMod 2) F = m := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    exact (FiniteField.pow_finrank_eq_natCard 2 F).trans hcard
  have hd := e.finrank_eq
  rw [h.quotient_core_finrank_eq_twice_actor] at hd
  simp only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,hF] at hd
  exact ⟨d,by nlinarith⟩


end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
