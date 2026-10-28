module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Models
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.SourceModule

/-!
# The actual quotient and its marked rank-two seed

The quotient map embeds the generating irreducible seed into every proper
H-subrepresentation quotient. Its L₀-fixed vectors, L₁,+ commutator identity,
and T-invariance survive in that same image. For a maximal denominator,
commutator generation and the monolith condition make the quotient faithful
and irreducible. The quadratic bound also descends, so the genuine B.4
alternatives apply. A three-cycle in L₀ then eliminates both exceptional
alternatives, conditional on the independently owned cubic normal form.

The source adapter uses the literal U_H/V₁ representation and seed. Neither
the normal-form input nor the marked-cycle input is claimed as established
by this conditional reduction.

Source: Aschbacher–Smith, 13.8.21–24, printed pp.957–959
(combined manuscript, 1 March 2004).
-/

public section
open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection
open PairsBranch PairsBranch.ModuleSelection
universe u
variable {H : Type*} {E : Type u} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  (ρ : Representation (ZMod 2) H E)

/-- Fixed vectors in a subspace descend to its literal quotient image. -/
theorem quotient_image_fixed (W : Subrepresentation ρ) (D : Submodule (ZMod 2) E)
    (L₀ : Subgroup H) (hfix : D ≤ fixedSpace ρ L₀) :
    D.map W.toSubmodule.mkQ ≤ fixedSpace W.quotientRepresentation L₀ := by
  rintro _ ⟨v, hv, rfl⟩ a
  change W.toSubmodule.mkQ (ρ a v) = W.toSubmodule.mkQ v
  exact congrArg W.toSubmodule.mkQ (hfix hv a)

/-- The linear commutator has its exact image under the quotient map. -/
theorem quotient_image_commutator (W : Subrepresentation ρ)
    (D : Submodule (ZMod 2) E) (X : Subgroup H) :
    (subspaceCommutator ρ D X).map W.toSubmodule.mkQ =
      subspaceCommutator W.quotientRepresentation (D.map W.toSubmodule.mkQ) X := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, hv, rfl⟩
    change W.toSubmodule.mkQ (ρ a v - v) ∈
      subspaceCommutator W.quotientRepresentation (D.map W.toSubmodule.mkQ) X
    rw [map_sub]
    exact Submodule.subset_span ⟨a, ha, W.toSubmodule.mkQ v, ⟨v, hv, rfl⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨ρ a v - v, Submodule.subset_span ⟨a, ha, v, hv, rfl⟩, map_sub _ _ _⟩

/-- All three local actions and the rank survive on the actual image of V₃. -/
theorem quotient_seed_data (L L₀ X T : Subgroup H)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (V : Subrepresentation (ρ.comp L.subtype)) [IsIrreducible V.toRepresentation]
    (hgen : SeedGenerates ρ V.toSubmodule)
    (hdim : Module.finrank (ZMod 2) V.toSubmodule = 2)
    (hstable : L ⊔ T ≤ subspaceStabilizer ρ V.toSubmodule)
    (hfix : V.toSubmodule ≤ fixedSpace ρ L₀)
    (hcomm : subspaceCommutator ρ V.toSubmodule X = V.toSubmodule) :
    let S := quotientSeed ρ L W V
    Module.finrank (ZMod 2) S.toSubmodule = 2 ∧
      L ⊔ T ≤ subspaceStabilizer W.quotientRepresentation S.toSubmodule ∧
      S.toSubmodule ≤ fixedSpace W.quotientRepresentation L₀ ∧
      subspaceCommutator W.quotientRepresentation S.toSubmodule X = S.toSubmodule := by
  refine ⟨quotientSeed_finrank ρ L W hW V hgen hdim,
    quotientSeed_stable ρ L W V (L ⊔ T) hstable,
    quotient_image_fixed ρ W V.toSubmodule L₀ hfix, ?_⟩
  change subspaceCommutator W.quotientRepresentation
    (V.toSubmodule.map W.toSubmodule.mkQ) X = V.toSubmodule.map W.toSubmodule.mkQ
  rw [← quotient_image_commutator, hcomm]

private theorem quadratic_quotient (W : Subrepresentation ρ) (A : Subgroup H)
    (hq : IsQuadratic ρ A) : IsQuadratic W.quotientRepresentation A := by
  intro a ha b hb q
  induction q using Submodule.Quotient.induction_on with
  | _ v =>
    change W.toSubmodule.mkQ (ρ a (ρ b v - v)) = W.toSubmodule.mkQ (ρ b v - v)
    rw [hq a ha b hb v]

variable [FiniteDimensional (ZMod 2) E]

/-- Select the natural quotient using a three-cycle in the marked centralizing
factor. Both remaining prerequisites are explicit; neither is a source input
that the final assembly may leave undischarged. -/
theorem natural_quotient_of_cubic_normal_form
    (φ : H →* Equiv.Perm (Fin 7)) (hφ : Function.Injective φ)
    (K L L₀ : Subgroup H) (hK : K.map φ = alternatingGroup (Fin 7))
    (hmonolith : ∀ N : Subgroup H, N.Normal → N ≠ ⊥ → K ≤ N)
    (hcomm : subspaceCommutator ρ ⊤ K = ⊤)
    (W : Subrepresentation ρ) (hW : IsCoatom W)
    (V : Subrepresentation (ρ.comp L.subtype)) [IsIrreducible V.toRepresentation]
    (hgen : SeedGenerates ρ V.toSubmodule)
    (hdim : Module.finrank (ZMod 2) V.toSubmodule = 2)
    (hfix : V.toSubmodule ≤ fixedSpace ρ L₀)
    (hcycle : ∃ g ∈ L₀, Equiv.Perm.IsThreeCycle (φ g))
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hclass : SmallQuadraticInput.{_, u} φ (componentInclusion φ hφ K hK))
    (hnormal : CubicNormalForm) : IsNatural W.quotientRepresentation φ := by
  let ι := componentInclusion φ hφ K hK
  have hfaith : Function.Injective W.quotientRepresentation :=
    faithful_of_nontrivial_on_monolith W.quotientRepresentation K hmonolith
      (nontrivial_on_quotient_of_generated ρ W K hW.1 hcomm)
  let : IsIrreducible W.quotientRepresentation := quotient_irreducible ρ W hW
  have hqbound : fixedCodim W.quotientRepresentation A ≤ 2 * rank A := by
    have hb := fixedCodim_quotient_add_subrepresentation_le ρ W A
    omega
  have halt : SmallModuleAlternatives W.quotientRepresentation φ ι :=
    hclass (E ⧸ W.toSubmodule) W.quotientRepresentation hfaith inferInstance
      A hA (quadratic_quotient ρ W A hq) hqbound
  let S := quotientSeed ρ L W V
  have hSdim : Module.finrank (ZMod 2) S.toSubmodule = 2 :=
    quotientSeed_finrank ρ L W hW.1 V hgen hdim
  have hS : S.toSubmodule ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at hSdim
    omega
  obtain ⟨v, hv, hne⟩ := (Submodule.ne_bot_iff S.toSubmodule).mp hS
  obtain ⟨g, hg, hthree⟩ := hcycle
  let a : A7 := ⟨φ g, hthree.mem_alternatingGroup⟩
  have hia : ι a = g := hφ (componentInclusion_compatible φ hφ K hK a)
  have hf := quotient_image_fixed ρ W V.toSubmodule L₀ hfix
  exact natural_of_fixed_threeCycle W.quotientRepresentation ι φ hnormal a hthree v hne
    (hf hv ⟨ι a, hia.symm ▸ hg⟩) halt

section Source
open scoped IsMulCommutative
variable {G : Type u} [Group G] [Finite G]
  (H K L₁ L₀ V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
  (hρ : CentralAction.IsSourceAction H V₃ V₁ ρ)

omit [Finite G] in
include hρ in
/-- The source centralization of V₃ by L₀ fixes the literal seed in U_H/V₁. -/
theorem source_seed_fixed_of_centralizes
    (hcentral : L₀ ≤ centralizer (V₃ : Set G)) :
    sourceImage H V₃ V₁ V₃ ≤ fixedSpace ρ (Source.starImage H L₀) := by
  rintro _ ⟨u, hu, rfl⟩ ⟨a, ha⟩
  obtain ⟨h, hh, rfl⟩ := ha
  change ρ (QuotientGroup.mk' (pCore 2 H) h)
    (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)) = _
  rw [hρ]
  apply congrArg Additive.ofMul
  apply congrArg (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)))
  apply Subtype.ext
  change h.val * u.val * h.val⁻¹ = u.val
  have he : u.val * h.val = h.val * u.val :=
    (mem_centralizer_iff.mp (hcentral hh)) u.val hu
  rw [← he, mul_inv_cancel_right]

/-- Source adapter: generation is proved from U_H = ⟨V₃^H⟩ and the actual
conjugation action, while the component commutator identity is transported from
13.8.21(4). The denominator is an actual maximal proper subrepresentation. -/
theorem source_natural_quotient_of_cubic_normal_form
    (hKH : K ≤ H) (hcomm : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (φ : Source.Hstar H →* Equiv.Perm (Fin 7)) (hφ : Function.Injective φ)
    (hK : (Source.starImage H K).map φ = alternatingGroup (Fin 7))
    (hmonolith : ∀ N : Subgroup (Source.Hstar H), N.Normal → N ≠ ⊥ →
      Source.starImage H K ≤ N)
    (W : Subrepresentation ρ) (hW : IsCoatom W)
    (hL : L₁ ≤ normalizer (V₃ : Set G))
    [IsIrreducible (sourceSeed H V₃ V₁ ρ hρ L₁ hL).toRepresentation]
    (hdim : Module.finrank (ZMod 2) (sourceImage H V₃ V₁ V₃) = 2)
    (hcentral : L₀ ≤ centralizer (V₃ : Set G))
    (hcycle : ∃ g ∈ Source.starImage H L₀, Equiv.Perm.IsThreeCycle (φ g))
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hclass : SmallQuadraticInput.{_, u} φ (componentInclusion φ hφ (Source.starImage H K) hK))
    (hnormal : CubicNormalForm) :
    IsNatural W.quotientRepresentation φ ∧ HasNaturalSubmodule W.quotientRepresentation φ := by
  have hn := natural_quotient_of_cubic_normal_form ρ φ hφ
    (Source.starImage H K) (Source.starImage H L₁) (Source.starImage H L₀) hK hmonolith
    (source_commutator_generated H V₃ V₁ ρ hρ K hKH hcomm) W hW
    (sourceSeed H V₃ V₁ ρ hρ L₁ hL)
    (source_seed_generates H V₃ V₁ ρ hρ) hdim
    (source_seed_fixed_of_centralizes H L₀ V₃ V₁ ρ hρ hcentral)
    hcycle A hA hq hbound hclass hnormal
  exact ⟨hn, hn.hasNaturalSubmodule⟩

end Source
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection
