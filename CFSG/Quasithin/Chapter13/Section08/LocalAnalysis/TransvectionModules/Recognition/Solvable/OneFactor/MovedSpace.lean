module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.Factors
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.OneFactor.ResidualTransport


/-!
# The two-dimensional moved space and the actual flag seed

The seed is the literal image of V₃ in U_H/V₁. Its cardinality is four
when the flag has orders two and eight. Conjugation carries group
commutators to representation displacements, so generation of V₃ modulo
V₁ puts this seed in the moved space. The natural one-factor model from
B.1.8 gives dimension two for that moved space, proving equality.

The local marked action must still supply the group commutator generation;
no module recognition or moved-space equality is assumed. The covered
source action is applied separately in `Covered`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Lemma 13.8.5, printed pp.947–948 (PDF pp.964–965).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.OneFactor
variable {G : Type*} [Group G] {H V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

theorem seedSpace_card (hV : V₁ ≤ V₃)
    (h₁ : Nat.card V₁ = 2) (h₃ : Nat.card V₃ = 8) :
    Nat.card (seedSpace H V₃ V₁) = 4 := by
  let U := Source.UH H V₃
  let q : U →* Source.Utilde H V₃ V₁ := QuotientGroup.mk' (V₁.subgroupOf U)
  let f : V₃ →* Source.Utilde H V₃ V₁ := q.comp (inclusion (le_conjugateSpanBy V₃ H))
  have hk : f.ker = V₁.subgroupOf V₃ := by
    ext v
    change q (inclusion (le_conjugateSpanBy V₃ H) v) = 1 ↔ _
    exact QuotientGroup.eq_one_iff _
  have hkcard : Nat.card f.ker = 2 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe hV).toEquiv, h₁]
  have hr : f.range = (V₃.subgroupOf U).map q := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨inclusion (le_conjugateSpanBy V₃ H) v, v.property, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  let e : f.range ≃ seedSpace H V₃ V₁ :=
    { toFun x := ⟨Additive.ofMul x, by
        change x.val ∈ (V₃.subgroupOf U).map q
        rw [← hr]
        exact x.property⟩
      invFun x := ⟨x.val.toMul, by
        rw [hr]
        exact x.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have hc := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [h₃, hkcard, Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
    Nat.card_congr e] at hc
  omega

theorem seedSpace_finrank [Finite G] (hV : V₁ ≤ V₃)
    (h₁ : Nat.card V₁ = 2) (h₃ : Nat.card V₃ = 8) :
    Module.finrank (ZMod 2) (seedSpace H V₃ V₁) = 2 := by
  have hc := seedSpace_card (H := H) hV h₁ h₃
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) (by simpa using hc)


theorem seedSpace_le_commutator_of_mod_line
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) (hV : V₁ ≤ V₃)
    (Y : Subgroup G) (hY : Y ≤ H) (hgen : V₃ ≤ ⁅V₃, Y⁆ ⊔ V₁) :
    seedSpace H V₃ V₁ ≤ subspaceCommutator ρ ⊤ (Source.starImage H Y) := by
  let S := subspaceCommutator ρ ⊤ (Source.starImage H Y)
  let U := Source.UH H V₃
  let q : U →* Source.Utilde H V₃ V₁ := QuotientGroup.mk' (V₁.subgroupOf U)
  let C := (S.toAddSubgroup.toSubgroup'.comap q).map U.subtype
  have hcomm : ⁅V₃, Y⁆ ≤ C := by
    apply commutator_le.mpr
    intro v hv y hy
    have hvU := le_conjugateSpanBy V₃ H hv
    have hc : ⁅v, y⁆ ∈ U :=
      le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy V₃ H)
        (commutator_mem_commutator hvU (hY hy))
    refine ⟨⟨⁅v, y⁆, hc⟩, ?_, rfl⟩
    change vector H V₃ V₁ _ ∈ S
    rw [vector_commutator ρ hρ ⟨v, hvU⟩ ⟨y, hY hy⟩]
    have hm : ρ (QuotientGroup.mk' (pCore 2 H) ⟨y, hY hy⟩)
        (vector H V₃ V₁ ⟨v, hvU⟩) - vector H V₃ V₁ ⟨v, hvU⟩ ∈ S :=
      Submodule.subset_span ⟨_, ⟨⟨y, hY hy⟩, hy, rfl⟩, _, Submodule.mem_top, rfl⟩
    simpa only [neg_sub] using S.neg_mem hm
  have hline : V₁ ≤ C := by
    intro v hv
    let u : U := ⟨v, le_conjugateSpanBy V₃ H (hV hv)⟩
    refine ⟨u, ?_, rfl⟩
    have he : q u = 1 := (QuotientGroup.eq_one_iff u).mpr hv
    change Additive.ofMul (q u) ∈ S
    rw [he]
    exact S.zero_mem
  have hseed : V₃ ≤ C := hgen.trans (sup_le hcomm hline)
  rintro w ⟨u, hu, he⟩
  obtain ⟨v, hv, hvu⟩ := hseed hu
  have hve : v = u := Subtype.ext hvu
  subst v
  change vector H V₃ V₁ u = w at he
  exact he ▸ hv

theorem seedSpace_le_commutator
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (Y : Subgroup G) (hY : Y ≤ H) (hgen : V₃ = ⁅V₃, Y⁆) :
    seedSpace H V₃ V₁ ≤ subspaceCommutator ρ ⊤ (Source.starImage H Y) := by
  rintro w ⟨u, hu, he⟩
  have hm := seed_mem_commutator ρ hρ Y hY hgen (⟨u, hu⟩ : V₃)
  change vector H V₃ V₁ u = w at he
  exact he ▸ hm

theorem movedSpace_eq_seedSpace_of_naturalTwo [Finite G]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hV : V₁ ≤ V₃) (h₁ : Nat.card V₁ = 2) (h₃ : Nat.card V₃ = 8)
    (K : Subgroup (Source.Hstar H)) [K.Normal] (d : NaturalTwo ρ K)
    (Y : Subgroup G) (hY : Y ≤ H) (hgen : V₃ ≤ ⁅V₃, Y⁆ ⊔ V₁)
    (hYK : Source.starImage H Y ≤ K) :
    subspaceCommutator ρ ⊤ K = seedSpace H V₃ V₁ := by
  apply (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · apply (seedSpace_le_commutator_of_mod_line ρ hρ hV Y hY hgen).trans
    apply Submodule.span_mono
    rintro _ ⟨y, hy, v, hv, rfl⟩
    exact ⟨y, hYK hy, v, hv, rfl⟩
  · rw [seedSpace_finrank hV h₁ h₃, d.moduleEquiv.finrank_eq]
    simp

/-- Once a source residual is identified, its literal image lies in K*.
The natural one-factor model and the marked action then identify the moved
space; no separate containment or moved-space premise is needed. -/
theorem movedSpace_eq_seedSpace_of_residual [Finite G]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hV : V₁ ≤ V₃) (h₁ : Nat.card V₁ = 2) (h₃ : Nat.card V₃ = 8)
    (K : Subgroup (Source.Hstar H)) [K.Normal]
    (d : ChapterB.SolvableFFFactors (ρ.comp K.subtype))
    (hJ : offenderSubgroup (ρ.comp K.subtype) = ⊤) (hc : d.count = 1)
    (Y : Subgroup G) (hres : preimageResidual H K = Y)
    (hgen : V₃ ≤ ⁅V₃, Y⁆ ⊔ V₁) :
    subspaceCommutator ρ ⊤ K = seedSpace H V₃ V₁ := by
  have hYK : Y ≤ starPreimage H K := hres ▸ preimageResidual_le H K
  have hYH : Y ≤ H := hYK.trans (starPreimage_le H K)
  exact movedSpace_eq_seedSpace_of_naturalTwo ρ hρ hV h₁ h₃ K
    (naturalTwo_of_count_one K d hJ hc) Y hYH hgen
    ((starImage_le_iff hYH K).mpr hYK)

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.OneFactor

end
