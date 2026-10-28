module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Generation and the surviving seed in the actual source quotient

The binary action is explicitly tied to conjugation on U_H/V₁, where
U_H is the H-conjugate span of V₃. Closure induction proves that the
literal image of V₃ generates this quotient. Relative normality of the
central-cover residual then propagates its seed commutator identity to
the entire quotient, without asserting that identity before quotienting.

An irreducible seed injects into every proper invariant quotient: a zero
projection would put the generating seed inside the denominator. The
actual quotient projection retains rank two and the local action. In a
six-dimensional quotient, maximality of the local parabolic identifies
it with the stabilizer of this surviving seed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.8.21(2), printed p.956, and the paragraph before 13.8.22 on p.957.
The action, local irreducibility and maximal parabolic remain explicit
source inputs. This module does not recognize a six-dimensional section.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction
variable {G : Type*} [Group G]
variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

def quotientVector (u : Source.UH H V₃) : Additive (Source.Utilde H V₃ V₁) :=
  Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)

def conjugateVector (h : H) (u : Source.UH H V₃) : Source.UH H V₃ :=
  ⟨h.val * u.val * h.val⁻¹,
    le_normalizer_iff.mp (le_normalizer_conjugateSpanBy V₃ H) h.val h.property
      u.val u.property⟩

/-- The actual action of H/O₂(H) on U_H/V₁, with its conjugation equation. -/
structure QuotientAction where
  line_le : V₁ ≤ Source.UH H V₃
  seed_le : V₃ ≤ H
  representation : Representation (ZMod 2) (Source.Hstar H)
    (Additive (Source.Utilde H V₃ V₁))
  conjugation : ∀ (h : H) (u : Source.UH H V₃),
    representation (QuotientGroup.mk' (pCore 2 H) h) (quotientVector H V₃ V₁ u) =
      quotientVector H V₃ V₁ (conjugateVector H V₃ h u)

def seedVector (v : V₃) : Additive (Source.Utilde H V₃ V₁) :=
  quotientVector H V₃ V₁ ⟨v.val, le_conjugateSpanBy V₃ H v.property⟩

def seedSpace : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) :=
  Submodule.span (ZMod 2) (Set.range (seedVector H V₃ V₁))

theorem seedSpace_generates (act : QuotientAction H V₃ V₁)
    (D : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁)))
    (hD : ∀ g v, v ∈ D → act.representation g v ∈ D)
    (hseed : seedSpace H V₃ V₁ ≤ D) : D = ⊤ := by
  apply top_unique
  intro v hv
  clear hv
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
    (V₁.subgroupOf (Source.UH H V₃)) v.toMul
  change quotientVector H V₃ V₁ u ∈ D
  rcases u with ⟨u, hu⟩
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨h, hh, z, hz, rfl⟩
    have hs : seedVector H V₃ V₁ ⟨z, hz⟩ ∈ D :=
      hseed (Submodule.subset_span ⟨⟨z, hz⟩, rfl⟩)
    have hm := hD (QuotientGroup.mk' (pCore 2 H) ⟨h, hh⟩) _ hs
    rw [seedVector, act.conjugation] at hm
    exact hm
  | one => exact D.zero_mem
  | mul x y hx hy ihx ihy => exact D.add_mem ihx ihy
  | inv x hx ih => exact D.neg_mem ih

/-- A quotient seed identity generates precisely the quotient U_H/V₁. -/
theorem residual_generates_quotient (act : QuotientAction H V₃ V₁)
    (K : Subgroup G) (hKH : K ≤ H) [(K.subgroupOf H).Normal]
    (hseed : subspaceCommutator act.representation (seedSpace H V₃ V₁)
      (Source.starImage H (coverResidualIn K)) = seedSpace H V₃ V₁) :
    subspaceCommutator act.representation ⊤ (Source.starImage H (coverResidualIn K)) = ⊤ := by
  have hn := coverResidualIn_normal H K hKH
  let := hn
  have hi : (Source.starImage H (coverResidualIn K)).Normal :=
    hn.map (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
  let := hi
  apply seedSpace_generates H V₃ V₁ act
  · have htop : (⊤ : Subgroup (Source.Hstar H)) ≤
        subspaceStabilizer act.representation ⊤ := by
      apply le_subspaceStabilizer
      intro a ha v hv
      exact Submodule.mem_top
    have hnorm : (⊤ : Subgroup (Source.Hstar H)) ≤
        normalizer (Source.starImage H (coverResidualIn K) : Set (Source.Hstar H)) := by
      rw [normalizer_eq_top]
    have hs := subspaceCommutator_invariant_normalizer act.representation htop hnorm
    exact fun g v hv => (hs (mem_top g) v).2 hv
  · rw [← hseed]
    exact subspaceCommutator_mono_left act.representation le_top _

theorem seedSpace_stable (act : QuotientAction H V₃ V₁) (P : Subgroup G)
    (hP : P ≤ normalizer (V₃ : Set G)) :
    ∀ p ∈ Source.starImage H P, ∀ v ∈ seedSpace H V₃ V₁,
      act.representation p v ∈ seedSpace H V₃ V₁ := by
  rintro _ ⟨p, hp, rfl⟩ v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    rcases hv with ⟨z, rfl⟩
    rw [seedVector, act.conjugation]
    apply Submodule.subset_span
    refine ⟨⟨p.val * z.val * p.val⁻¹, ?_⟩, rfl⟩
    exact (mem_normalizer_iff.mp (hP hp) z.val).mp z.property
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (seedSpace H V₃ V₁).add_mem ihx ihy
  | smul a v hv ih =>
    simpa only [map_smul] using (seedSpace H V₃ V₁).smul_mem a ih

def seedRepresentation (act : QuotientAction H V₃ V₁) (P : Subgroup G)
    (hP : P ≤ normalizer (V₃ : Set G)) :
    Subrepresentation (act.representation.comp (Source.starImage H P).subtype) where
  toSubmodule := seedSpace H V₃ V₁
  apply_mem_toSubmodule p := by
    intro v hv
    exact seedSpace_stable H V₃ V₁ act P hP p.val p.property v hv

/-- The restricted projection of the literal irreducible seed is injective. -/
theorem seed_injective_in_proper_quotient (act : QuotientAction H V₃ V₁)
    (P : Subgroup G) (hP : P ≤ normalizer (V₃ : Set G))
    [IsIrreducible (seedRepresentation H V₃ V₁ act P hP).toRepresentation]
    (I : Subrepresentation act.representation) (hI : I ≠ ⊤) :
    Function.Injective (I.toSubmodule.mkQ.domRestrict (seedSpace H V₃ V₁)) := by
  let f : IntertwiningMap (seedRepresentation H V₃ V₁ act P hP).toRepresentation
      (I.quotientRepresentation.comp (Source.starImage H P).subtype) := {
    toLinearMap := I.toSubmodule.mkQ.domRestrict (seedSpace H V₃ V₁)
    isIntertwining' g := by ext v; rfl }
  rcases IsIrreducible.injective_or_eq_zero f with hf | hf
  · exact hf
  · exfalso
    apply hI
    apply Subrepresentation.toSubmodule_injective
    apply seedSpace_generates H V₃ V₁ act I.toSubmodule
    · exact fun g v hv => I.apply_mem_toSubmodule g hv
    · intro v hv
      apply (Submodule.Quotient.mk_eq_zero I.toSubmodule).mp
      exact DFunLike.congr_fun hf ⟨v, hv⟩

theorem quotient_seed_finrank (act : QuotientAction H V₃ V₁)
    (P : Subgroup G) (hP : P ≤ normalizer (V₃ : Set G))
    [IsIrreducible (seedRepresentation H V₃ V₁ act P hP).toRepresentation]
    (I : Subrepresentation act.representation) (hI : I ≠ ⊤)
    (hseed : Module.finrank (ZMod 2) (seedSpace H V₃ V₁) = 2) :
    Module.finrank (ZMod 2) ((seedSpace H V₃ V₁).map I.toSubmodule.mkQ) = 2 := by
  have hr := LinearMap.finrank_range_of_inj
    (seed_injective_in_proper_quotient H V₃ V₁ act P hP I hI)
  rw [LinearMap.range_domRestrict] at hr
  exact hr.trans hseed

theorem quotient_seed_stable (act : QuotientAction H V₃ V₁)
    (P : Subgroup G) (hP : P ≤ normalizer (V₃ : Set G))
    (I : Subrepresentation act.representation) :
    Source.starImage H P ≤ subspaceStabilizer I.quotientRepresentation
      ((seedSpace H V₃ V₁).map I.toSubmodule.mkQ) := by
  apply le_subspaceStabilizer
  rintro p hp _ ⟨v, hv, rfl⟩
  exact ⟨act.representation p v, seedSpace_stable H V₃ V₁ act P hP p hp v hv, rfl⟩

theorem quotient_seed_generates (act : QuotientAction H V₃ V₁)
    (I : Subrepresentation act.representation)
    (D : Submodule (ZMod 2) ((Additive (Source.Utilde H V₃ V₁)) ⧸ I.toSubmodule))
    (hD : ∀ g v, v ∈ D → I.quotientRepresentation g v ∈ D)
    (hseed : (seedSpace H V₃ V₁).map I.toSubmodule.mkQ ≤ D) : D = ⊤ := by
  have hc : D.comap I.toSubmodule.mkQ = ⊤ := by
    apply seedSpace_generates H V₃ V₁ act
    · intro g v hv
      exact hD g (I.toSubmodule.mkQ v) hv
    · intro v hv
      exact hseed ⟨v, hv, rfl⟩
  apply top_unique
  intro v _
  obtain ⟨u, rfl⟩ := I.toSubmodule.mkQ_surjective v
  exact (show I.toSubmodule.mkQ u ∈ D from
    (show u ∈ D.comap I.toSubmodule.mkQ from hc ▸ Submodule.mem_top))

/-- A maximal local subgroup stabilizing the surviving seed is its full
stabilizer, because that rank-two seed generates the six-dimensional quotient. -/
theorem quotient_seed_stabilizer (act : QuotientAction H V₃ V₁)
    (P : Subgroup G) (hP : P ≤ normalizer (V₃ : Set G))
    (hmax : IsCoatom (Source.starImage H P))
    [IsIrreducible (seedRepresentation H V₃ V₁ act P hP).toRepresentation]
    (I : Subrepresentation act.representation) (hI : I ≠ ⊤)
    (hseed : Module.finrank (ZMod 2) (seedSpace H V₃ V₁) = 2)
    (hdim : Module.finrank (ZMod 2)
      ((Additive (Source.Utilde H V₃ V₁)) ⧸ I.toSubmodule) = 6) :
    subspaceStabilizer I.quotientRepresentation
      ((seedSpace H V₃ V₁).map I.toSubmodule.mkQ) = Source.starImage H P := by
  rcases hmax.le_iff.mp (quotient_seed_stable H V₃ V₁ act P hP I) with he | he
  · exfalso
    have ht := quotient_seed_generates H V₃ V₁ act I _ (by
      intro g v hv
      have hg : g ∈ subspaceStabilizer I.quotientRepresentation
          ((seedSpace H V₃ V₁).map I.toSubmodule.mkQ) := he ▸ mem_top g
      exact (hg v).mpr hv) le_rfl
    have hs := quotient_seed_finrank H V₃ V₁ act P hP I hI hseed
    rw [ht, finrank_top, hdim] at hs
    omega
  · exact he

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction
