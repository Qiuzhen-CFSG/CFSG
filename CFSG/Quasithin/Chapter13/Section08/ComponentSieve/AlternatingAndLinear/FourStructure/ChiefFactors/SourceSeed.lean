module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.Seed
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.ElementaryAbelian.VectorSpace

/-!
# The seed from the actual source quotient

The two-space is the image of V₃ in U_H/V₁, where U_H is its actual
H-conjugate span. Pulling an invariant subspace back to U_H and then into
the ambient group gives an H-normalized subgroup. If it contains V₃ it
contains U_H, proving generation. The quotient action is required to agree
with conjugation on every representative; no unrelated action is used.

Only normality of V₁ inside U_H is required. The parabolic invariance,
irreducibility and dimension of Ṽ₃ are the earlier source inputs on printed
p.957. Generation is proved here and supplies FourStructure.GeneratingSeed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), notation on pp.946–947 and 13.8.25 on pp.960–961.
-/

@[expose] public section

open scoped IsMulCommutative
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
variable {G : Type*} [Group G] (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

abbrev SourceSpace := Additive (Source.Utilde H V₃ V₁)

def sourceProjection : Source.UH H V₃ →* Source.Utilde H V₃ V₁ :=
  QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))

def sourceConjugate (h : H) (u : Source.UH H V₃) : Source.UH H V₃ :=
  ⟨(h : G) * u * (h : G)⁻¹,
    Subgroup.le_normalizer_iff.mp (Subgroup.le_normalizer_conjugateSpanBy V₃ H)
      h h.property u u.property⟩

def IsSourceAction (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁)) :
    Prop := ∀ h : H, ∀ u : Source.UH H V₃,
      ρ (QuotientGroup.mk' (pCore 2 H) h) (Additive.ofMul (sourceProjection H V₃ V₁ u)) =
        Additive.ofMul (sourceProjection H V₃ V₁ (sourceConjugate H V₃ h u))

def sourceSeedSpace : Submodule (ZMod 2) (SourceSpace H V₃ V₁) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup
    ((V₃.subgroupOf (Source.UH H V₃)).map (sourceProjection H V₃ V₁)))

theorem sourceSeedSpace_generates
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ) (W : Subrepresentation ρ)
    (hseed : sourceSeedSpace H V₃ V₁ ≤ W.toSubmodule) : W = ⊤ := by
  let J : Subgroup (Source.UH H V₃) :=
    (Subgroup.toAddSubgroup.symm W.toSubmodule.toAddSubgroup).comap (sourceProjection H V₃ V₁)
  let B : Subgroup G := J.map (Source.UH H V₃).subtype
  have hVB : V₃ ≤ B := by
    intro v hv
    let u : Source.UH H V₃ := ⟨v, le_conjugateSpanBy V₃ H hv⟩
    refine ⟨u, ?_, rfl⟩
    apply hseed
    exact ⟨u, hv, rfl⟩
  have hHB : H ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    rintro h hh b ⟨u, hu, rfl⟩
    refine ⟨sourceConjugate H V₃ ⟨h, hh⟩ u, ?_, rfl⟩
    change Additive.ofMul (sourceProjection H V₃ V₁ (sourceConjugate H V₃ ⟨h, hh⟩ u)) ∈ W
    rw [← hρ]
    exact W.apply_mem_toSubmodule _ hu
  have hUB : Source.UH H V₃ ≤ B := conjugateSpanBy_le hVB hHB
  apply top_unique
  intro v _
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
  obtain ⟨w, hw, hwu⟩ := hUB u.property
  have hwue : w = u := Subtype.ext hwu
  subst w
  change Additive.ofMul (sourceProjection H V₃ V₁ u) ∈ W at hw
  simpa [sourceProjection, hu] using hw

noncomputable def sourceSeed
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    (P T : Subgroup (Source.Hstar H)) (hTP : T ≤ P) (hT : IsPGroup 2 T)
    (hstable : ∀ g : P, ∀ v ∈ sourceSeedSpace H V₃ V₁, ρ g v ∈ sourceSeedSpace H V₃ V₁)
    (hirr : IsAtom (⟨sourceSeedSpace H V₃ V₁, hstable⟩ : Subrepresentation (ρ.comp P.subtype)))
    (hdim : Module.finrank (ZMod 2) (sourceSeedSpace H V₃ V₁) = 2) : GeneratingSeed ρ where
  parabolic := P
  sylow := T
  sylow_le := hTP
  sylow_two_group := hT
  space := ⟨sourceSeedSpace H V₃ V₁, hstable⟩
  irreducible := hirr
  dim_two := hdim
  generates := sourceSeedSpace_generates H V₃ V₁ ρ hρ
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
