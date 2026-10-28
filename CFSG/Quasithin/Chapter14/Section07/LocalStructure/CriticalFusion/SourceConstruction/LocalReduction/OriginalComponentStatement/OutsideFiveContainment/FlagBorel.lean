module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.CyclicFlag
public import Theory.Representation.BinaryPermutation.FiveBorelFixed
public import Theory.Representation.BinaryPermutation.FiveTensorLowRank
public import Theory.Representation.BinaryConjugationSection.FixedImage

/-!
# The original component Borel preserves the original plane

On the five-by-three tensor module, an alternating-five Sylow normalizer
fixes every vector fixed by that Sylow subgroup. This follows on each of
the two five-point coordinates. A component-fixed direct summand does not
change the conclusion.

Apply this calculation to the literal section U_I/V₁ and the original
Sylow intersection with a normal component C. The original flag makes
V₂/V₁ a nonzero T-fixed line. Its fixation by the actual component Borel
therefore gives [B₀,V₂] ≤ V₁ and B₀ ≤ G₂. The only module input is the
marked tensor decomposition on this same component and section; no Borel
conjugate or flag marking is supplied.

Source: Aschbacher–Smith 14.7.46, printed p.1063, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open BinaryLinearThree.ParabolicCyclic
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment
open Chapter12.Section08 CriticalFusion.Source AlternatingSevenSource EightSource
universe u v w

/-- The same Sylow normalizer fixes its fixed space in the five-by-three tensor. -/
theorem tensor_normalizer_fixes
    (P : Sylow 2 (alternatingGroup (Fin 5)))
    (a : alternatingGroup (Fin 5)) (ha : a ∈ normalizer (P : Set _))
    (z : FiveTensorLowRank.Space)
    (hz : ∀ g ∈ P, FiveTensorLowRank.action (g.val, 1) z = z) :
    FiveTensorLowRank.action (a.val, 1) z = z := by
  let e := ThreeTensor.pairEquiv (V := core (Fin 5))
  have hfix (g : alternatingGroup (Fin 5)) (hg : g ∈ P) :
      coreRepresentation (Fin 5) g.val (e z).1 = (e z).1 ∧
      coreRepresentation (Fin 5) g.val (e z).2 = (e z).2 := by
    have hh := congrArg e (hz g hg)
    change ThreeTensor.pairEquiv
      (ThreeTensor.action (coreRepresentation (Fin 5)) (g.val, 1) z) = _ at hh
    rw [ThreeTensor.pairEquiv_equivariant] at hh
    exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
  have h₁ := FiveBorelFixed.normalizer_fixes P a ha (e z).1
    (fun g => (hfix g.val g.property).1)
  have h₂ := FiveBorelFixed.normalizer_fixes P a ha (e z).2
    (fun g => (hfix g.val g.property).2)
  apply e.injective
  change ThreeTensor.pairEquiv
    (ThreeTensor.action (coreRepresentation (Fin 5)) (a.val, 1) z) = _
  rw [ThreeTensor.pairEquiv_equivariant]
  exact Prod.ext h₁ h₂

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {I : Subgroup G}
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  {W₀ : Type w} [AddCommGroup W₀] [Module (ZMod 2) W₀]
  {ρ : Representation (ZMod 2) I W}

/-- The original component Borel fixes the literal plane quotient. The displayed
subgroup is exactly `componentSylowNormalizer T I C`, with its actual T∩C. -/
theorem local_component_tensor_borel_fixes_plane
    (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (s : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (C : Subgroup I) [C.Normal]
    (π : C →* alternatingGroup (Fin 5)) (hπ : Function.Surjective π)
    (f : W ≃ₗ[ZMod 2] (FiveTensorLowRank.Space × W₀))
    (hf : ∀ c : C, ∀ x : W,
      f (ρ c.val x) = (FiveTensorLowRank.action ((π c).val, 1) (f x).1, (f x).2)) :
    s.imageSpace (F.Vi 2) ≤ fixedSpace ρ
      (C ⊓ normalizer ((T : Subgroup G).subgroupOf I ⊓ C : Set I)) := by
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal C
  let Q := P.mapSurjective hπ
  intro x hx b
  let c : C := ⟨b.val, b.property.1⟩
  have hc : c ∈ normalizer (P : Set C) := by
    apply mem_normalizer_iff.mpr
    intro k
    rw [hP]
    have hb : b.val ∈ normalizer (((T : Subgroup G).subgroupOf I ⊓ C : Subgroup I) : Set I) :=
      b.property.2
    have hh := mem_normalizer_iff.mp hb (k : I)
    change ((k : I) ∈ (S : Subgroup I)) ↔ (c.val * k.val * c.val⁻¹ ∈ (S : Subgroup I))
    simpa only [S, c, Sylow.coe_subtype, mem_inf, C.mul_mem_cancel_left b.property.1,
      C.mul_mem_cancel_right (C.inv_mem b.property.1), k.property, and_true] using hh
  have hπc : π c ∈ normalizer (Q : Set _) :=
    (P : Subgroup C).le_normalizer_map π (mem_map_of_mem π hc)
  have hfixed : ∀ g ∈ Q, FiveTensorLowRank.action (g.val, 1) (f x).1 = (f x).1 := by
    intro g hg
    obtain ⟨k, hk, rfl⟩ := hg
    have hkT : ((k : I) : G) ∈ (T : Subgroup G) := by
      rw [hP] at hk
      exact hk
    have hxfix : ρ k.val x = x :=
      local_quotient_plane_sylow_fixed s (IntertwiningMap.id ρ) k.val hkT x ⟨x,hx,rfl⟩
    exact congrArg Prod.fst ((hf k x).symm.trans (congrArg f hxfix))
  apply f.injective
  change f (ρ c.val x) = f x
  rw [hf c x]
  exact Prod.ext (tensor_normalizer_fixes Q (π c) hπc (f x).1 hfixed) rfl

/-- The actual quotient kernel lifts Borel fixation to the original plane,
so its normalizer is the original G₂. -/
theorem local_component_tensor_borel_plane_control
    (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (s : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (C : Subgroup I) [C.Normal]
    (π : C →* alternatingGroup (Fin 5)) (hπ : Function.Surjective π)
    (f : W ≃ₗ[ZMod 2] (FiveTensorLowRank.Space × W₀))
    (hf : ∀ c : C, ∀ x : W,
      f (ρ c.val x) = (FiveTensorLowRank.action ((π c).val, 1) (f x).1, (f x).2)) :
    let B₀ := (C ⊓ normalizer ((T : Subgroup G).subgroupOf I ⊓ C : Set I)).map I.subtype
    ⁅B₀,F.Vi 2⁆ ≤ F.Vi 1 ∧ B₀ ≤ F.Gi 2 := by
  let B := C ⊓ normalizer ((T : Subgroup G).subgroupOf I ⊓ C : Set I)
  have hfixed := local_component_tensor_borel_fixes_plane hI s C π hπ f hf
  have he : (B.map I.subtype).subgroupOf I = B :=
    comap_map_eq_self_of_injective I.subtype_injective B
  have hcomm : ⁅B.map I.subtype,F.Vi 2⁆ ≤ F.Vi 1 :=
    s.commutator_le_of_imageSpace_fixed (B.map I.subtype) (F.Vi 2)
      (map_subtype_le _) ((F.le_seed 2).trans (le_conjugateSpanBy V I))
      (by rwa [he])
  exact ⟨hcomm, le_normalizer_iff_commutator_le_right.mpr
    (hcomm.trans (F.monotone (by decide : 1 ≤ 2)))⟩

/-- The original nonzero T-fixed line and its actual component Borel are
retained together. The tensor decomposition is the remaining module input. -/
theorem local_component_tensor_flag_borel_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (s : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (C : Subgroup I) [C.Normal]
    (π : C →* alternatingGroup (Fin 5)) (hπ : Function.Surjective π)
    (f : W ≃ₗ[ZMod 2] (FiveTensorLowRank.Space × W₀))
    (hf : ∀ c : C, ∀ x : W,
      f (ρ c.val x) = (FiveTensorLowRank.action ((π c).val, 1) (f x).1, (f x).2)) :
    let B₀ := (C ⊓ normalizer ((T : Subgroup G).subgroupOf I ⊓ C : Set I)).map I.subtype
    (∃ x : W, x ∈ s.imageSpace (F.Vi 2) ∧ x ≠ 0 ∧ orbitSpan ρ ⊤ x = ⊤ ∧
      ∀ t : I, (t : G) ∈ (T : Subgroup G) → ρ t x = x) ∧
      ⁅B₀,F.Vi 2⁆ ≤ F.Vi 1 ∧ B₀ ≤ F.Gi 2 :=
  ⟨local_exists_sylow_fixed_cyclic_at h hI s,
    local_component_tensor_borel_plane_control hI s C π hπ f hf⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment
