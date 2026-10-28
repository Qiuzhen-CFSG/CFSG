module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.ElementaryAbelian.VectorSpace

/-!
# The literal source seed inside the component module

The space is the additive form of Source.Utilde, and the seed is the actual
image of V₃ in U_H/V₁. A compatible action is required to agree with
conjugation before quotienting. Normalization of V₃ proves invariance of
its image. Once F.9.18 supplies I = [Ũ_H,K], the identity Ṽ₃ = [Ṽ₃,L₁]
and L₁ ≤ K embed this seed in I by literal subspace inclusion. The map is
proved injective and equivariant, rather than postulated as a witness.

Source: Aschbacher–Smith, 13.8.21(2), printed p.956 (1 March 2004 manuscript).
The recognition of I and the earlier seed identities remain explicit inputs.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu
variable {G : Type*} [Group G]
variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (CFSG.Quasithin.Chapter13.Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (CFSG.Quasithin.Chapter13.Section08.Source.Utilde H V₃ V₁)]
open CFSG.Quasithin.Chapter13.Section08
/-- The additive carrier of the actual source quotient. -/
abbrev SourceSpace := Additive (Source.Utilde H V₃ V₁)
/-- The literal image of V₃ under U_H → U_H/V₁. -/
def seedSpace : Submodule (ZMod 2) (SourceSpace H V₃ V₁) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup
    ((V₃.subgroupOf (Source.UH H V₃)).map
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)))))

def conjugateSource (h : H) (u : Source.UH H V₃) : Source.UH H V₃ :=
  ⟨h.val * u.val * h.val⁻¹,
    le_normalizer_iff.mp (le_normalizer_conjugateSpanBy V₃ H) h.val h.property
      u.val u.property⟩

/-- Quotient action with its required conjugation compatibility. -/
structure SourceAction where
  representation : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁)
  conjugation : ∀ (h : H) (u : Source.UH H V₃),
    representation (QuotientGroup.mk' (pCore 2 H) h)
      (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)) =
    Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
      (conjugateSource H V₃ h u))

variable {H V₃ V₁}
def SourceAction.onH (d : SourceAction H V₃ V₁) :
    Representation (ZMod 2) H (SourceSpace H V₃ V₁) :=
  d.representation.comp (QuotientGroup.mk' (pCore 2 H))

/-- Local normalization descends to invariance of the actual seed. -/
theorem source_seed_stable (d : SourceAction H V₃ V₁) (P : Subgroup G)
    (hn : P ≤ normalizer (V₃ : Set G)) :
    ∀ p : P.subgroupOf H, ∀ v ∈ seedSpace H V₃ V₁,
      d.onH p.val v ∈ seedSpace H V₃ V₁ := by
  intro p v hv
  obtain ⟨u, hu, he⟩ := hv
  change QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u = v.toMul at he
  have he' : v = Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) :=
    congrArg Additive.ofMul he.symm
  rw [he']
  change d.representation _ _ ∈ _
  rw [d.conjugation]
  exact ⟨conjugateSource H V₃ p.val u,
    le_normalizer_iff.mp hn p.val.val p.property u.val hu, rfl⟩

def seedRepresentation
    (ρ : Representation (ZMod 2) H (SourceSpace H V₃ V₁))
    (P : Subgroup H)
    (hstable : ∀ p : P, ∀ v ∈ seedSpace H V₃ V₁, ρ p.val v ∈ seedSpace H V₃ V₁) :
    Subrepresentation (ρ.comp P.subtype) where
  toSubmodule := seedSpace H V₃ V₁
  apply_mem_toSubmodule := hstable

section General
variable {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
  (ρ : Representation (ZMod 2) A E) (K L : Subgroup A)
  (I : Subrepresentation ρ) (S : Submodule (ZMod 2) E)

/-- The two commutator identities force the actual seed into I. -/
theorem seed_le_component (hLK : L ≤ K)
    (hI : I.toSubmodule = subspaceCommutator ρ ⊤ K)
    (hS : S = subspaceCommutator ρ S L) : S ≤ I.toSubmodule := by
  rw [hS, hI]
  apply Submodule.span_mono
  rintro _ ⟨l, hl, v, _, rfl⟩
  exact ⟨l, hLK hl, v, Submodule.mem_top, rfl⟩

def seedEmbedding (hLK : L ≤ K)
    (hI : I.toSubmodule = subspaceCommutator ρ ⊤ K)
    (hS : S = subspaceCommutator ρ S L) : S →ₗ[ZMod 2] I.toSubmodule :=
  Submodule.inclusion (seed_le_component ρ K L I S hLK hI hS)

theorem seedEmbedding_injective (hLK : L ≤ K)
    (hI : I.toSubmodule = subspaceCommutator ρ ⊤ K)
    (hS : S = subspaceCommutator ρ S L) :
    Function.Injective (seedEmbedding ρ K L I S hLK hI hS) :=
  Submodule.inclusion_injective _

theorem seedEmbedding_equivariant (P : Subgroup A)
    (S : Subrepresentation (ρ.comp P.subtype))
    (hLK : L ≤ K) (hI : I.toSubmodule = subspaceCommutator ρ ⊤ K)
    (hS : S.toSubmodule = subspaceCommutator ρ S.toSubmodule L)
    (p : P) (s : S.toSubmodule) :
    seedEmbedding ρ K L I S.toSubmodule hLK hI hS (S.toRepresentation p s) =
      I.toRepresentation p.val (seedEmbedding ρ K L I S.toSubmodule hLK hI hS s) := rfl
end General
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu
