module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition.Offenders
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition.Models
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.Sieve
public import CFSG.Quasithin.ChapterA.Section01.Representations.HomogeneousBridge

/-!
# The unique noncentral constituent in the G₂ sieve

The literal 13.8.22 alternatives give a strong offender or a transvection
whenever a proper ambient submodule is noncentral. Both are impossible by
the proved derived-G₂ exclusions. Homogeneous existence and the complete
F.9.18 alternatives then construct an invariant Irr⁺ member; the paired
case is excluded by its actual group model. This member must be the whole
module. Its quotient by fixed vectors is irreducible, allowing a central
cover of the natural module rather than incorrectly asserting irreducibility
of the whole source module.

The genuine earlier F.9.18 outputs and critical geometry remain explicit.
Source: Aschbacher–Smith 13.8.22 and 13.8.27, printed pp.957, 963.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition
open FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases

variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) (L : Subgroup D) [L.Normal] [IsQuasisimple L]

omit [Finite D] in
/-- A self-centralizing normal component lies in every nontrivial normal subgroup. -/
theorem monolith (hc : centralizer (L : Set D) = ⊥) :
    ∀ N : Subgroup D, N.Normal → N ≠ ⊥ → L ≤ N := by
  intro N hN hn
  let := hN
  have hL : IsComponent D L := ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩
  rcases hL.normal_dichotomy N with h | h
  · exact h
  · have hNC : N ≤ centralizer (L : Set D) :=
      commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm N L).trans h)
    exact (hn (bot_unique (hNC.trans hc.le))).elim

/-- The critical line and codimension bound force every proper ambient submodule
 to be component-central. No irreducibility of the original module is assumed. -/
theorem proper_submodules_central
    (hc : centralizer (L : Set D) = ⊥)
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hgen : subspaceCommutator ρ ⊤ L = ⊤)
    (A : Subgroup D) (hA : IsElementaryTwo A) (B : Submodule (ZMod 2) V)
    (hcritical : B ≤ fixedSpace ρ A ∨ ∃ S : Submodule (ZMod 2) V,
      IsAtom S ∧ ∀ a ∈ A, ∀ d ∈ B, ρ a d - d ∈ S)
    (hdim : Module.finrank (ZMod 2) (V ⧸ B) ≤ rank A)
    (W : Subrepresentation ρ) : W = ⊤ ∨ W.toSubmodule ≤ fixedSpace ρ L := by
  by_cases hW : W = ⊤
  · exact Or.inl hW
  right
  by_contra hn
  have hKW : ∃ k ∈ L, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w := by
    by_contra! h
    apply hn
    intro v hv k
    exact congrArg Subtype.val (h k k.property ⟨v, hv⟩)
  have hKQ := Seven.PairsBranch.nontrivial_on_quotient_of_generated ρ W L hW hgen
  have hWf := faithful_of_nontrivial_on_monolith W.toRepresentation L (monolith L hc) hKW
  have hQf := faithful_of_nontrivial_on_monolith W.quotientRepresentation L (monolith L hc) hKQ
  have hnW := no_strong W.toRepresentation L hWf hc e
  have hnQ := no_strong W.quotientRepresentation L hQf hc e
  rcases hcritical with hfixed | ⟨S, hS, hcomm⟩
  · obtain ⟨C, _, _, hC⟩ := strong_submodule_offender_of_fixed_subspace
      ρ W B hQf hA hfixed hdim
    exact hnW ⟨C, hC⟩
  · have ht := Seven.PairsBranch.transvection_alternative_of_no_strong
      ρ W B S hS hWf hQf hA hcomm hdim hnW hnQ
    obtain ⟨a, ha, hne⟩ : ∃ a ∈ A, a ≠ 1 := by
      by_contra! h
      exact hA.1 (eq_bot_iff.mpr h)
    let : IsElementaryAbelian 2 A := hA.2
    have hp : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
    rcases ht with ht | ht
    · exact no_transvection W.toRepresentation L hWf hc e a hne hp (ht a ha hne)
    · exact no_transvection W.quotientRepresentation L hQf hc e a hne hp (ht a ha hne)

omit [Finite D] in
/-- The full F.9.18 alternatives supply an invariant Irr⁺ constituent. The
 paired case is excluded by its actual carrier, and both other cases retain invariance. -/
theorem invariant_constituent (hf : Function.Injective ρ)
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (P : Sylow 2 D) (hLP : L ⊔ (P : Subgroup D) = ⊤)
    (earlier : OrbitInputs ρ L P hLP) :
    ∃ I : Subrepresentation ρ, IsIrrPlus ρ L I.toSubmodule := by
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  obtain ⟨I, hI⟩ := ChapterA.exists_chapter15_isIrrPlusWith_of_faithful ρ hf L P
    ((nontrivial_iff_ne_bot L).mp inferInstance) le_normalizer_of_normal P.isPGroup'
  have hs : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ I := by
    rcases earlier.alternatives I hI with hs | ⟨he, _⟩ | hp
    · exact hs
    · rw [← hLP]
      apply sup_le hI.invariant
      rw [← he]
      exact orbitSpan_invariant ρ P I
    · apply False.elim
      apply not_pairCarrier e
      rcases hp.model with hm | ⟨he, _⟩
      · exact hm.pairCarrier
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr he))))
  exact ⟨⟨I, fun g _ hv => (hs (mem_top g) _).2 hv⟩, hI.isIrrPlus⟩

/-- The whole original module belongs to Irr⁺(L,V). Its literal quotient by
 component-fixed vectors, rather than the whole module, is irreducible. -/
theorem whole_isIrrPlus (hf : Function.Injective ρ)
    (hc : centralizer (L : Set D) = ⊥)
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hgen : subspaceCommutator ρ ⊤ L = ⊤)
    (P : Sylow 2 D) (hLP : L ⊔ (P : Subgroup D) = ⊤)
    (earlier : OrbitInputs ρ L P hLP)
    (A : Subgroup D) (hA : IsElementaryTwo A) (B : Submodule (ZMod 2) V)
    (hcritical : B ≤ fixedSpace ρ A ∨ ∃ S : Submodule (ZMod 2) V,
      IsAtom S ∧ ∀ a ∈ A, ∀ d ∈ B, ρ a d - d ∈ S)
    (hdim : Module.finrank (ZMod 2) (V ⧸ B) ≤ rank A) :
    IsIrrPlus ρ L ⊤ := by
  obtain ⟨I, hI⟩ := invariant_constituent ρ L hf e P hLP earlier
  rcases proper_submodules_central ρ L hc e hgen A hA B hcritical hdim I with ht | hfix
  · rw [ht] at hI
    exact hI
  · exact (hI.not_le_fixedSpace ρ hfix).elim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition
