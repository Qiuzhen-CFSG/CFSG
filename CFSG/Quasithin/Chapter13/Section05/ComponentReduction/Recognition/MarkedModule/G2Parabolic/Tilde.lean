module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.Basic
public import Theory.Representation.BinaryOffender.ConjugationImage

/-!
# The exact tilde commutator premise for 13.5.14

The binary conjugation-image theorem turns full linear L₁-displacement into
surjectivity of the original [U_H,L₁] on U_H/V₁. Composing with the actual
inclusion into N_G(V₁)/V₁ gives the full tilde commutator equality. This
uses neither abelianness of U_H nor a splitting of its central extension.

Source: Aschbacher–Smith, 13.5.21(6) and its application to 13.5.14,
printed p.924 / PDF p.941.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.G2Parabolic
open Section08.Source
variable {G : Type*} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- Full displacement on the original module supplies precisely the tilde
commutator identity used by 13.5.14. -/
theorem tilde_generation_of_linear
    (hgen : subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H D.L₁) = ⊤) :
    D.tilde D.UH = ⁅D.tilde D.UH, D.tilde D.L₁⁆ := by
  have hLH : D.L₁ ≤ D.H := le_sup_left.trans h.local_le
  have hn : D.L₁ ≤ normalizer (D.UH : Set G) :=
    hLH.trans (le_normalizer_conjugateSpanBy D.Vplus D.H)
  let q := QuotientGroup.mk' (D.V₁.subgroupOf D.UH)
  let f : D.L₁ →* Hstar D.H :=
    (QuotientGroup.mk' (pCore 2 D.H)).comp (inclusion hLH)
  have hf : f.range = starImage D.H D.L₁ := by
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨y,rfl⟩; exact y.property
    · intro hx; exact ⟨⟨x,hx⟩,rfl⟩
  have hP : binarySubgroup (⊤ : Submodule (ZMod 2) (Action.Space D)) =
      (D.UH.subgroupOf D.UH).map q := by
    rw [subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    rfl
  have hact (x : D.L₁) (u : D.UH) :
      Action.starRepresentation D h (f x) (Additive.ofMul (q u)) =
        Additive.ofMul (q ⟨x.val * u.val * x.val⁻¹,
          le_normalizer_iff.mp hn x.val x.property u.val u.property⟩) :=
    Action.starRepresentation_apply D h (inclusion hLH x) u
  have hc := commutator_image_eq (Action.starRepresentation D h)
    D.UH D.UH D.L₁ hn le_rfl f q hact ⊤ hP
  rw [hf,hgen] at hc
  have hU := Action.UH_le_ambient D h
  have hL : D.L₁ ≤ D.g2.G₁ := hLH.trans h.g2_hypothesis.H_le
  have hC : ⁅D.UH,D.L₁⁆ ≤ D.UH := le_normalizer_iff_commutator_le_left.mp hn
  have he : D.tilde ⁅D.UH,D.L₁⁆ = ⁅D.tilde D.UH,D.tilde D.L₁⁆ := by
    have hr : (⁅D.UH,D.L₁⁆).subgroupOf D.g2.G₁ =
        ⁅D.UH.subgroupOf D.g2.G₁,D.L₁.subgroupOf D.g2.G₁⁆ := by
      apply map_injective D.g2.G₁.subtype_injective
      rw [map_subgroupOf_eq_of_le (hC.trans hU), map_commutator,
        map_subgroupOf_eq_of_le hU,map_subgroupOf_eq_of_le hL]
    change ((⁅D.UH,D.L₁⁆).subgroupOf D.g2.G₁).map _ = _
    rw [hr,map_commutator]
    rfl
  rw [← he]
  apply le_antisymm _ (map_mono (comap_mono hC))
  rintro x ⟨u,hu,rfl⟩
  let uU : D.UH := ⟨u.val,hu⟩
  have hmem : q uU ∈ (⁅D.UH,D.L₁⁆.subgroupOf D.UH).map q := by
    rw [hc]
    trivial
  obtain ⟨c,hc',hec⟩ := hmem
  have het := congrArg (Action.tildeMap D h) hec
  refine ⟨inclusion hU c, hc', ?_⟩
  exact het
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.G2Parabolic
