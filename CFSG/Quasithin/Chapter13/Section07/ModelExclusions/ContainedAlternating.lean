module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.ComponentNormality
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.AssemblySupport
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
/-!
# Full alternating actions in the original contained-component branch

The original13.7.5 component normality and commutator generation supply
the actual inputs to the six/seven-letter module-cover classification.
F.9 identifies the kernel on U_H/V₁ with O₂(H), so the full H* action is
faithful. The concrete module normalizers embed H* in the corresponding
symmetric group, compatibly with the original K/O₂(K) coordinates.
The sign homomorphism then makes H*/K* a two-group; the prescribed Sylow
subgroup gives H=KT. No transvection or product conclusion is assumed.

Source: Aschbacher–Smith,13.7.6(3), printed pp.938–939. The original
point/plane markings, local covering alternative and chief-factor count
remain subsequent steps of that lemma.
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]

private theorem tilde_faithful
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) : Function.Injective ρ := by
  apply faithful_of_centralizer_le_core ρ hρ
  intro x hx
  change x ∈ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).QH
  rw [← hF9.kernel_UH_eq_QH]
  apply (hF9.mem_kernel_iff hF9.UH_le_H).mpr
  refine ⟨commutatorPreimage_le _ _ _ hx, ?_⟩
  intro u hu
  rw [← commutatorElement_inv]
  apply V₁.inv_mem
  exact commutator_commutatorPreimage_le H (Section08.Source.UH H V₃) V₁
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
      (commutator_mem_commutator hx hu)

private theorem product_of_alternating_embedding {n : ℕ}
    (hTH : (T : Subgroup G) ≤ H) (hKH : K ≤ H)
    (hKn : (Section08.Source.starImage H K).Normal)
    (f : Section08.Source.Hstar H →* Equiv.Perm (Fin n)) (hf : Function.Injective f)
    (eK : Section08.Source.starImage H K ≃* alternatingGroup (Fin n))
    (hfK : ∀ k : Section08.Source.starImage H K, f k = (eK k).val) :
    (H : Set G) = (K : Set G) * (T : Set G) := by
  let := hKn
  let A := Section08.Source.starImage H K
  let s := Equiv.Perm.sign.comp f
  have hk : s.ker = A := by
    ext x
    constructor
    · intro hx
      have hfx : f x ∈ alternatingGroup (Fin n) := hx
      obtain ⟨k, he⟩ := eK.surjective ⟨f x, hfx⟩
      have hfk : f k = f x := (hfK k).trans (congrArg Subtype.val he)
      exact hf hfk ▸ k.property
    · intro hx
      change Equiv.Perm.sign (f x) = 1
      rw [hfK ⟨x,hx⟩]
      exact (eK ⟨x,hx⟩).property
  have hp : IsPGroup 2 ℤˣ := fun x => ⟨1, by simp [Int.units_sq]⟩
  have hq : IsPGroup 2 (Section08.Source.Hstar H ⧸ A) := by
    exact (hp.to_subgroup s.range).of_equiv
      ((QuotientGroup.quotientKerEquivRange s).symm.trans (QuotientGroup.quotientMulEquivOfEq hk))
  let S := (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hS : (S : Subgroup (Section08.Source.Hstar H)) = Section08.Source.starImage H (T : Subgroup G) := rfl
  have hsup : A ⊔ Section08.Source.starImage H (T : Subgroup G) = ⊤ := by
    rw [← hS, sup_comm]
    exact S.sup_eq_top_of_quotient_isPGroup A hq
  apply product_of_star_product_sylow T H K hTH hKH
  intro x
  obtain ⟨k, hk, t, ht, he⟩ := mem_sup_of_normal_left.mp (hsup.symm ▸ mem_top x)
  exact ⟨k, hk, t, ht, he.symm⟩

include d

/-- The original seven-letter section determines the whole module and H=KT. -/
theorem contained_seven_full_action
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 7)) eK) :
    (H : Set G) = (K : Set G) * (T : Set G) ∧
    ∃ (f : Section08.Source.Hstar H →* Equiv.Perm (Fin 7))
      (eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 7)),
      Function.Injective f ∧
      (∀ k : Section08.Source.starImage H K, f k = (componentModelEquiv hKH hK eK k).val) ∧
      ∀ a v, eV (ρ a v) = BinaryPermutation.coreRepresentation (Fin 7) (f a) (eV v) := by
  obtain ⟨hKn, hgen⟩ := component_normal_and_span_of_one_le d hH hF9 hKH hK hL₁K
  have hNi := (normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  let : (Section08.Source.starImage H K).Normal :=
    Subgroup.Normal.map hNi (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
  obtain ⟨eV, heV⟩ := seven_core_of_section hKH hK ρ hρ hgen.symm eK hs
  obtain ⟨f, hf, hfK, hfV⟩ := SevenExtension.faithful_extension
    (Section08.Source.starImage H K) ρ (tilde_faithful hF9 ρ hρ)
    (componentModelEquiv hKH hK eK) eV heV
  exact ⟨product_of_alternating_embedding hF9.T_le_H hKH inferInstance f hf
    (componentModelEquiv hKH hK eK) hfK, f, eV, hf, hfK, hfV⟩

/-- Both original six-letter covering modules extend to the full actor, with H=KT. -/
theorem contained_six_full_action
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK) :
    (H : Set G) = (K : Set G) * (T : Set G) ∧
    ((∃ (f : Section08.Source.Hstar H →* Equiv.Perm (Fin 6))
      (eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6)),
      Function.Injective f ∧
      (∀ k : Section08.Source.starImage H K, f k = (componentModelEquiv hKH hK eK k).val) ∧
      ∀ a v, eV (ρ a v) = BinaryPermutation.naturalRepresentation (Fin 6) (f a) (eV v)) ∨
    (∃ (f : Section08.Source.Hstar H →* Equiv.Perm (Fin 6))
      (eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6)),
      Function.Injective f ∧
      (∀ k : Section08.Source.starImage H K, f k = (componentModelEquiv hKH hK eK k).val) ∧
      ∀ a v, eV (ρ a v) = BinaryPermutation.coreRepresentation (Fin 6) (f a) (eV v))) := by
  obtain ⟨hKn, hgen⟩ := component_normal_and_span_of_one_le d hH hF9 hKH hK hL₁K
  have hNi := (normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  let : (Section08.Source.starImage H K).Normal :=
    Subgroup.Normal.map hNi (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
  rcases alternatingSix_module_of_section hKH hK ρ hρ hgen.symm eK hs with ⟨eV, heV⟩ | ⟨eV, heV⟩
  · obtain ⟨f, hf, hfK, hfV, _⟩ := Section08.ComponentSieve.SixAndG2.NaturalSix.faithful_extension
      (Section08.Source.starImage H K) ρ (tilde_faithful hF9 ρ hρ)
      (componentModelEquiv hKH hK eK) eV (fun k v => by
        simpa only [modelActor_componentModelEquiv, BinaryPermutation.alternatingCoreRepresentation, MonoidHom.comp_apply, Subgroup.subtype_apply] using heV (componentModelEquiv hKH hK eK k) v)
    exact ⟨product_of_alternating_embedding hF9.T_le_H hKH inferInstance f hf
      (componentModelEquiv hKH hK eK) hfK, Or.inl ⟨f, eV, hf, hfK, hfV⟩⟩
  · obtain ⟨f, hf, hfK, hfV, _⟩ :=
      Section08.TransvectionParabolic.Marking.CompatibleFlags.AugmentationExtension.faithful_extension
        (Section08.Source.starImage H K) ρ (tilde_faithful hF9 ρ hρ)
        (componentModelEquiv hKH hK eK) eV (fun k v => by
          simpa only [modelActor_componentModelEquiv, BinaryPermutation.alternatingCoreRepresentation, MonoidHom.comp_apply, Subgroup.subtype_apply] using heV (componentModelEquiv hKH hK eK k) v)
    exact ⟨product_of_alternating_embedding hF9.T_le_H hKH inferInstance f hf
      (componentModelEquiv hKH hK eK) hfK, Or.inr ⟨f, eV, hf, hfK, hfV⟩⟩

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
