module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.Images
public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Commutator generation in local subgroup images

Pull the image of the action-difference space back to a subgroup of B.
Conjugation compatibility puts every commutator [r,d] in this pullback;
D = [D,R] then makes it contain D. Its quotient image is consequently the
whole local image. Only the literal quotient B/Z is elementary abelian,
and normality of Z is relative to B.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the two
commutator-generated planes in the proof of 13.8.6(4), printed p.948.
-/

public section

open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors
variable {G A : Type*} [Group G] [Group A]
variable (B Z : Subgroup G) [(Z.subgroupOf B).Normal]
  [IsElementaryAbelian 2 (B ⧸ Z.subgroupOf B)]
variable (P : Subgroup G) (π : P →* A)
  (hPB : P ≤ normalizer (B : Set G))
  (ρ : Representation (ZMod 2) A (Additive (B ⧸ Z.subgroupOf B)))
  (hρ : SectionConjugationAlong P B Z π hPB ρ)

/-- Commutator generation passes to the full difference space of the actual
local subgroup image in the elementary section. The numerator B and the
ambient group may be nonabelian. -/
theorem localImage_coinvariants_eq_top (R D : Subgroup G) (hRD : R ≤ normalizer (D : Set G))
    (hRP : R ≤ P) (hDB : D ≤ B) (hgen : D = ⁅D, R⁆) :
    Coinvariants.ker (localImage B Z P π hPB ρ hρ R D hRD).toRepresentation = ⊤ := by
  let S := localImage B Z P π hPB ρ hρ R D hRD
  let K := Coinvariants.ker S.toRepresentation
  let W := K.map S.toSubmodule.subtype
  have hcomm : ⁅R, D⁆ ≤ sectionPreimage B Z W := by
    apply commutator_le.mpr
    intro r hr d hd
    let p : P := ⟨r, hRP hr⟩
    let a : (R.subgroupOf P).map π := ⟨π p, p, hr, rfl⟩
    let b : B := ⟨d, hDB hd⟩
    let x : S.toSubmodule := ⟨Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf B) b), ⟨b, hd, rfl⟩⟩
    have hdiff : (ρ (π p) (x : Additive (B ⧸ Z.subgroupOf B)) - x) ∈ W :=
      ⟨S.toRepresentation a x - x, Coinvariants.sub_mem_ker a x, rfl⟩
    have hb : r * d * r⁻¹ ∈ B :=
      (mem_normalizer_iff.mp (hPB (hRP hr)) d).mp (hDB hd)
    have hc : ⁅r,d⁆ ∈ B := by
      simpa only [commutatorElement_def] using B.mul_mem hb (B.inv_mem (hDB hd))
    apply (mem_sectionPreimage B Z W ⟨⁅r,d⁆, hc⟩).mpr
    change ρ (π p) (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf B) b)) -
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf B) b) ∈ W at hdiff
    rw [hρ] at hdiff
    convert hdiff using 1
    change Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf B) ⟨⁅r,d⁆, hc⟩) =
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf B)
        ⟨r*d*r⁻¹, hb⟩ / QuotientGroup.mk' (Z.subgroupOf B) b)
    rw [← map_div]
    congr 2
    apply Subtype.ext
    simp only [commutatorElement_def, div_eq_mul_inv]
    rfl
  have hDW : D ≤ sectionPreimage B Z W := by
    rw [hgen, commutator_comm]
    exact hcomm
  have hSW : S.toSubmodule ≤ W :=
    (sectionImage_le_iff B Z D hDB W).mpr hDW
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := hSW x.property
  have he' : y = x := Subtype.ext he
  exact he' ▸ hy
end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors


