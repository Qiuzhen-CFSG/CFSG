module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The actual section and generating seed in the transvection argument

The actors are H*=H/O₂(H) and the vectors are in the literal U_H/V₁,
where U_H=⟨V₃^H⟩. Normality of V₁ is relative to U_H. `IsConjugation`
retains the action on representatives; it imposes no recognition conclusion.

We prove that the orbit of the actual V₃ image spans this section, that
V₃=[V₃,L₁] puts the seed in the L₁-commutator space, and that the earlier
centralizer bound C_H(U_H/V₁)≤O₂(H) makes the quotient action faithful.
Consequently the fixed-seed lemma in Basic applies without a new spanning
or faithfulness assumption. A transvection is specified by its nonzero
linear form and center vector, not by a group-family tag.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
combined manuscript of 1 March 2004, the setup on printed p.946 and
the last paragraph of Lemma 13.8.5 on printed p.948 (PDF p.965).
These are source-section transfer lemmas, not the full recognition theorem.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition
variable {G : Type*} [Group G] (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

abbrev vector (u : Source.UH H V₃) : Additive (Source.Utilde H V₃ V₁) :=
  Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)

abbrev seedVector (v : V₃) : Additive (Source.Utilde H V₃ V₁) :=
  vector H V₃ V₁ ⟨v, le_conjugateSpanBy V₃ H v.property⟩

def IsConjugation
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))) : Prop :=
  ∀ (h : H) (u : Source.UH H V₃),
    ρ (QuotientGroup.mk' (pCore 2 H) h) (vector H V₃ V₁ u) =
      vector H V₃ V₁ ⟨(h : G) * (u : G) * (h : G)⁻¹,
        le_normalizer_iff.mp (le_normalizer_conjugateSpanBy V₃ H)
          h h.property u u.property⟩

variable {H V₃ V₁}
variable (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
  (hρ : IsConjugation H V₃ V₁ ρ)
include hρ

theorem vector_commutator (u : Source.UH H V₃) (h : H) :
    vector H V₃ V₁ ⟨⁅(u : G), (h : G)⁆,
      le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy V₃ H)
        (commutator_mem_commutator u.property h.property)⟩ =
      vector H V₃ V₁ u - ρ (QuotientGroup.mk' (pCore 2 H) h) (vector H V₃ V₁ u) := by
  rw [hρ]
  have he : (⟨⁅(u : G), (h : G)⁆,
      le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy V₃ H)
        (commutator_mem_commutator u.property h.property)⟩ : Source.UH H V₃) =
      u * (⟨(h : G) * (u : G) * (h : G)⁻¹,
        le_normalizer_iff.mp (le_normalizer_conjugateSpanBy V₃ H)
          h h.property u u.property⟩ : Source.UH H V₃)⁻¹ := by
    apply Subtype.ext
    simp [commutatorElement_def, mul_assoc]
  dsimp only [vector]
  rw [he]
  simp only [map_mul, map_inv, ofMul_mul, ofMul_inv, sub_eq_add_neg]

theorem seed_orbit_spans :
    Submodule.span (ZMod 2)
      {x | ∃ a : Source.Hstar H, ∃ b ∈ Set.range (seedVector H V₃ V₁), x = ρ a b} = ⊤ := by
  let S := Submodule.span (ZMod 2)
    {x | ∃ a : Source.Hstar H, ∃ b ∈ Set.range (seedVector H V₃ V₁), x = ρ a b}
  let U := Source.UH H V₃
  let q : U →* Source.Utilde H V₃ V₁ := QuotientGroup.mk' (V₁.subgroupOf U)
  let C := (S.toAddSubgroup.toSubgroup'.comap q).map U.subtype
  have hUC : U ≤ C := by
    apply (Subgroup.closure_le C).mpr
    rintro x ⟨h, hh, v, hv, rfl⟩
    refine ⟨⟨h * v * h⁻¹,
      le_normalizer_iff.mp (le_normalizer_conjugateSpanBy V₃ H) h hh v
        (le_conjugateSpanBy V₃ H hv)⟩, ?_, rfl⟩
    change vector H V₃ V₁ _ ∈ S
    rw [← hρ ⟨h, hh⟩ ⟨v, le_conjugateSpanBy V₃ H hv⟩]
    exact Submodule.subset_span ⟨_, _, ⟨⟨v, hv⟩, rfl⟩, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf U) x.toMul
  obtain ⟨u', hu', he⟩ := hUC u.property
  have he' : u' = u := Subtype.ext he
  subst u'
  change Additive.ofMul (q u) ∈ S at hu'
  change q u = x.toMul at hu
  simpa only [hu, ofMul_toMul] using hu'

theorem seed_mem_commutator (L₁ : Subgroup G) (hL : L₁ ≤ H)
    (hgen : V₃ = ⁅V₃, L₁⁆) (v : V₃) :
    seedVector H V₃ V₁ v ∈ subspaceCommutator ρ ⊤ (Source.starImage H L₁) := by
  let S := subspaceCommutator ρ ⊤ (Source.starImage H L₁)
  let U := Source.UH H V₃
  let q : U →* Source.Utilde H V₃ V₁ := QuotientGroup.mk' (V₁.subgroupOf U)
  let C := (S.toAddSubgroup.toSubgroup'.comap q).map U.subtype
  have hcomm : ⁅V₃, L₁⁆ ≤ C := by
    apply commutator_le.mpr
    intro u hu l hl
    have huU := le_conjugateSpanBy V₃ H hu
    have hc : ⁅u, l⁆ ∈ U :=
      le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy V₃ H)
        (commutator_mem_commutator huU (hL hl))
    refine ⟨⟨⁅u, l⁆, hc⟩, ?_, rfl⟩
    change vector H V₃ V₁ _ ∈ S
    rw [vector_commutator ρ hρ ⟨u, huU⟩ ⟨l, hL hl⟩]
    have hm : ρ (QuotientGroup.mk' (pCore 2 H) ⟨l, hL hl⟩)
        (vector H V₃ V₁ ⟨u, huU⟩) - vector H V₃ V₁ ⟨u, huU⟩ ∈ S :=
      Submodule.subset_span ⟨_, ⟨⟨l, hL hl⟩, hl, rfl⟩, _, Submodule.mem_top, rfl⟩
    simpa only [neg_sub] using S.neg_mem hm
  obtain ⟨u, hu, he⟩ := hcomm (hgen.le v.property)
  have he' : u = (⟨v, le_conjugateSpanBy V₃ H v.property⟩ : U) := Subtype.ext he
  subst u
  exact hu

theorem faithful_of_centralizer_le_core
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H) :
    Function.Injective ρ := by
  apply ρ.ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
  let π := QuotientGroup.mk' (pCore 2 H)
  let C := (ρ.comp π).ker.map H.subtype
  have hCH : C ≤ H := map_subtype_le _
  have hcomm : ⁅Source.UH H V₃, C⁆ ≤ V₁ := by
    apply commutator_le.mpr
    intro u hu c hc
    obtain ⟨k, hk, rfl⟩ := hc
    have hv := vector_commutator ρ hρ ⟨u, hu⟩ k
    have hk' : ρ (π k) = 1 := hk
    rw [hk', Module.End.one_apply, sub_self] at hv
    have hz := (QuotientGroup.eq_one_iff
      (N := V₁.subgroupOf (Source.UH H V₃))
      (⟨⁅u, (k : G)⁆, le_normalizer_iff_commutator_le_left.mp
        (le_normalizer_conjugateSpanBy V₃ H)
        (commutator_mem_commutator hu k.property)⟩ : Source.UH H V₃)).mp hv
    exact hz
  have hCQ : C ≤ Source.QH H := hcentralizer.trans' (le_commutatorPreimage hCH
    (by rwa [commutator_comm]))
  have hh : (h : G) ∈ Source.QH H := hCQ ⟨h, hx, rfl⟩
  obtain ⟨h', hh', he⟩ := hh
  have he' : h' = h := Subtype.ext he
  subst h'
  exact (QuotientGroup.eq_one_iff h).mpr hh'

/-- The final propagation, with orbit generation proved for the actual section. -/
theorem normal_eq_bot_of_seed_fixed
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (K : Subgroup (Source.Hstar H)) [K.Normal]
    (hfixed : ∀ k ∈ K, ∀ v : V₃, ρ k (seedVector H V₃ V₁ v) = seedVector H V₃ V₁ v) :
    K = ⊥ := by
  apply normal_subgroup_eq_bot_of_fixed_generating_seed ρ
    (faithful_of_centralizer_le_core ρ hρ hcentralizer) K
    (Set.range (seedVector H V₃ V₁)) (seed_orbit_spans ρ hρ)
  rintro k hk _ ⟨v, rfl⟩
  exact hfixed k hk v

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition

open Representation
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition
variable {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]

/-- A nontrivial binary transvection, with its actual center and linear form. -/
def IsTransvection (ρ : Representation (ZMod 2) A E) (t : A) : Prop :=
  ∃ (f : Module.Dual (ZMod 2) E) (v : E),
    f ≠ 0 ∧ v ≠ 0 ∧ f v = 0 ∧ ∀ w, ρ t w = w + f w • v

theorem IsTransvection.ne_one {ρ : Representation (ZMod 2) A E} {t : A}
    (ht : IsTransvection ρ t) : t ≠ 1 := by
  rintro rfl
  obtain ⟨f, v, hf, hv, _, he⟩ := ht
  apply hf
  ext w
  have hw := he w
  rw [map_one, Module.End.one_apply] at hw
  have hz : f w • v = 0 := add_eq_left.mp hw.symm
  exact (smul_eq_zero.mp hz).resolve_right hv

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition

end
