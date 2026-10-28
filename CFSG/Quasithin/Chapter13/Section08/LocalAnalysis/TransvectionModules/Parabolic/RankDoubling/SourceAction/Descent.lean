module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.Actions

/-!
# Descent of actual conjugation on the doubling quotient

An ambient subgroup normalizing U₂ and V₂ acts on the literal U₂/V₂.
A commutator bound kills the indicated subgroup in this action, so an
isomorphism I₂/O₂(I₂) ≃ S₃ descends it to S₃. This construction retains
its formula on representatives and agrees with the canonical K₂-action.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.6, printed p.948, with the local quotient from 13.5.4(2).
The kernel bound is a separate hypothesis here; its source application
requires G.2.2 and does not follow merely from the local quotient type.
-/

public section

open Subgroup Module
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling.SourceAction
variable {G : Type*} [Group G]
variable (H V V₂ : Subgroup G)
  [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)]

noncomputable def conjugation (P : Subgroup G)
    (hPU : P ≤ normalizer (Source.U2 H V V₂ : Set G))
    (hP₂ : P ≤ normalizer (V₂ : Set G)) : P →* MulAut (Uhat H V V₂) :=
  (exists_quotient_conjugation_action P (Source.U2 H V V₂) V₂ hPU hP₂
    inferInstance).choose

omit [IsElementaryAbelian 2 V] in
theorem conjugation_mk (P : Subgroup G)
    (hPU : P ≤ normalizer (Source.U2 H V V₂ : Set G))
    (hP₂ : P ≤ normalizer (V₂ : Set G)) (p : P) (u : Source.U2 H V V₂) :
    conjugation H V V₂ P hPU hP₂ p
        (QuotientGroup.mk' (V₂.subgroupOf (Source.U2 H V V₂)) u) =
      QuotientGroup.mk' (V₂.subgroupOf (Source.U2 H V V₂))
        ⟨(p : G) * (u : G) * (p : G)⁻¹,
          (mem_normalizer_iff.mp (hPU p.property) u).mp u.property⟩ :=
  (exists_quotient_conjugation_action P (Source.U2 H V V₂) V₂ hPU hP₂
    inferInstance).choose_spec p u

noncomputable def linearAction (P : Subgroup G)
    (hPU : P ≤ normalizer (Source.U2 H V V₂ : Set G))
    (hP₂ : P ≤ normalizer (V₂ : Set G)) :
    Representation F P (Additive (Uhat H V V₂)) where
  toFun p := (conjugation H V V₂ P hPU hP₂ p).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext x
    change Additive.ofMul (conjugation H V V₂ P hPU hP₂ 1 x.toMul) = x
    rw [map_one]
    rfl
  map_mul' p q := by
    ext x
    change Additive.ofMul (conjugation H V V₂ P hPU hP₂ (p * q) x.toMul) = _
    rw [map_mul]
    rfl

theorem linearAction_mk (P : Subgroup G)
    (hPU : P ≤ normalizer (Source.U2 H V V₂ : Set G))
    (hP₂ : P ≤ normalizer (V₂ : Set G)) (p : P) (u : Source.U2 H V V₂) :
    linearAction H V V₂ P hPU hP₂ p (quotientMap H V V₂ (Additive.ofMul u)) =
      quotientMap H V V₂ (Additive.ofMul
        ⟨(p : G) * (u : G) * (p : G)⁻¹,
          (mem_normalizer_iff.mp (hPU p.property) u).mp u.property⟩) :=
  congrArg Additive.ofMul (conjugation_mk H V V₂ P hPU hP₂ p u)

/-- The ambient linear action restricts to exactly the previously constructed K₂-action. -/
theorem linearAction_K2 (P : Subgroup G)
    (hPU : P ≤ normalizer (Source.U2 H V V₂ : Set G))
    (hP₂ : P ≤ normalizer (V₂ : Set G)) (hKP : Source.K2 H V₂ ≤ P)
    (k : Source.K2 H V₂) :
    linearAction H V V₂ P hPU hP₂ ⟨k, hKP k.property⟩ = representation H V V₂ k := by
  ext x
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective
    (V₂.subgroupOf (Source.U2 H V V₂)) x.toMul
  have hx : quotientMap H V V₂ (Additive.ofMul u) = x := congrArg Additive.ofMul hu
  rw [← hx, linearAction_mk, representation_mk]

/-- A relative commutator layer, not an ambient normality assumption, supplies the kernel. -/
theorem linearAction_kills (P Q : Subgroup G)
    (hPU : P ≤ normalizer (Source.U2 H V V₂ : Set G))
    (hP₂ : P ≤ normalizer (V₂ : Set G))
    (hUQ : ⁅Source.U2 H V V₂, Q⁆ ≤ V₂) :
    Q.subgroupOf P ≤ (linearAction H V V₂ P hPU hP₂).ker := by
  have hk := quotient_conjugation_action_kills_commutator_layer P (Source.U2 H V V₂)
    V₂ Q inferInstance hPU hUQ (conjugation H V V₂ P hPU hP₂)
    (conjugation_mk H V V₂ P hPU hP₂)
  intro p hp
  have he : conjugation H V V₂ P hPU hP₂ p = 1 := hk hp
  apply MonoidHom.mem_ker.mpr
  ext x
  change Additive.ofMul (conjugation H V V₂ P hPU hP₂ p x.toMul) = x
  rw [he]
  rfl

/-- A single ambient commutator in V₂ fixes the corresponding quotient vector. -/
theorem linearAction_fixed (P : Subgroup G)
    (hPU : P ≤ normalizer (Source.U2 H V V₂ : Set G))
    (hP₂ : P ≤ normalizer (V₂ : Set G)) (p : P) (u : Source.U2 H V V₂)
    (hcomm : ⁅(p : G), (u : G)⁆ ∈ V₂) :
    linearAction H V V₂ P hPU hP₂ p (quotientMap H V V₂ (Additive.ofMul u)) =
      quotientMap H V V₂ (Additive.ofMul u) := by
  rw [linearAction_mk]
  apply congrArg Additive.ofMul
  apply QuotientGroup.eq_iff_div_mem.mpr
  change (p : G) * (u : G) * (p : G)⁻¹ / (u : G) ∈ V₂
  simpa only [div_eq_mul_inv, commutatorElement_def] using hcomm

/-- A killed commutator makes the two actual quotient operators commute. -/
theorem linearAction_commute (P Q : Subgroup G)
    (hPU : P ≤ normalizer (Source.U2 H V V₂ : Set G))
    (hP₂ : P ≤ normalizer (V₂ : Set G))
    (hUQ : ⁅Source.U2 H V V₂, Q⁆ ≤ V₂)
    (p q : P) (hpq : ⁅(p : G), (q : G)⁆ ∈ Q) :
    Commute (linearAction H V V₂ P hPU hP₂ p)
      (linearAction H V V₂ P hPU hP₂ q) := by
  let ρ := linearAction H V V₂ P hPU hP₂
  have he : ρ ⁅p,q⁆ = 1 := linearAction_kills H V V₂ P Q hPU hP₂ hUQ hpq
  have hm : ⁅p,q⁆ * (q * p) = p * q := by
    simp only [commutatorElement_def]
    group
  change ρ p * ρ q = ρ q * ρ p
  rw [← map_mul, ← hm, map_mul, he, one_mul, map_mul]

/-- Descend a representation along the actual local two-core quotient. -/
noncomputable def descend (I₂ : Subgroup G)
    (ρ : Representation F I₂ (Additive (Uhat H V V₂)))
    (hker : pCore 2 I₂ ≤ ρ.ker)
    (e : (I₂ ⧸ pCore 2 I₂) ≃* InvertedCubicTensor.S₃) :
    Representation F InvertedCubicTensor.S₃ (Additive (Uhat H V V₂)) :=
  (QuotientGroup.lift (pCore 2 I₂) ρ hker).comp e.symm.toMonoidHom

theorem descend_mk (I₂ : Subgroup G)
    (ρ : Representation F I₂ (Additive (Uhat H V V₂)))
    (hker : pCore 2 I₂ ≤ ρ.ker)
    (e : (I₂ ⧸ pCore 2 I₂) ≃* InvertedCubicTensor.S₃) (i : I₂) :
    descend H V V₂ I₂ ρ hker e (e (QuotientGroup.mk' (pCore 2 I₂) i)) = ρ i := by
  simp only [descend, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    e.symm_apply_apply]
  rfl

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling.SourceAction
