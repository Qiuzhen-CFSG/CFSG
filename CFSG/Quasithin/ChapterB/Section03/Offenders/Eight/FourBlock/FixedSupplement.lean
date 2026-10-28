module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.FourBlock.SeedCore
public import Theory.Representation.BinaryOffender.FixedSummandCoordinates
public import Theory.Representation.BinaryPermutation.EightNormalizer
public import Theory.Representation.BinaryOffender.NormalizerConjugateDimension
/-!
# Orthogonal seed-core exclusion with a fixed supplement

Extend the marked normal A₈ action on its natural six-space to the full
permutation action. A fixed direct supplement preserves the offender's
fixed codimension and the literal pointwise seed stabilizer. The projected
moving Sylow-fixed seed then contradicts the four-block core exclusion.

Source application: Aschbacher--Smith 15.1.28, printed p.1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
namespace CFSG.Quasithin.ChapterB.Offenders.Eight.FourBlock
variable {D U F : Type*} [Group D] [Finite D] [AddCommGroup U]
  [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  [AddCommGroup F] [Module (ZMod 2) F] [FiniteDimensional (ZMod 2) F]

omit [Finite D] [FiniteDimensional (ZMod 2) U] in
/-- Remove a fixed summand without changing the original seed stabilizer. -/
theorem no_split_seed_core_offender (σ : Representation (ZMod 2) D U)
    (f : D →* Equiv.Perm (Fin 8)) (hfi : Function.Injective f)
    (hH : alternatingGroup (Fin 8) ≤ f.range)
    (E : U ≃ₗ[ZMod 2] natural (Fin 8) × F)
    (he : ∀ g v, E (σ g v) = (naturalRepresentation (Fin 8) (f g) (E v).1, (E v).2))
    (P : Submodule (ZMod 2) U) (Q : Sylow 2 (alternatingGroup (Fin 8)))
    (hn : P.map (splitSeedProjection E) ≠ ⊥)
    (hf : P.map (splitSeedProjection E) ≤ fixedSpace (alternatingNaturalRepresentation (Fin 8)) Q)
    {A : Subgroup D} (hA : IsOffender σ A)
    (hcore : A ≤ (subspaceKernel σ P ⊤).pCoreIn 2) : False := by
  let τ := naturalRepresentation (Fin 8)
  let P' := P.map (splitSeedProjection E)
  have hfix (g : D) (v : U) : σ g v = v ↔ τ (f g) (splitSeedProjection E v) =
      splitSeedProjection E v := by
    rw [← E.injective.eq_iff, he]
    exact Prod.ext_iff.trans (and_iff_left rfl)
  have hk : (subspaceKernel σ P ⊤).map f = subspaceKernel τ P' f.range := by
    ext a
    constructor
    · rintro ⟨g,hg,rfl⟩
      refine ⟨⟨g,rfl⟩,?_⟩
      rintro _ ⟨v,hv,rfl⟩
      exact (hfix g v).mp (hg.2 v hv)
    · rintro ⟨⟨g,rfl⟩,hg⟩
      exact ⟨g,⟨mem_top _,fun v hv => (hfix g v).mpr (hg _ (Submodule.mem_map_of_mem hv))⟩,rfl⟩
  have hc : A.map f ≤ (subspaceKernel τ P' f.range).pCoreIn 2 := by
    rw [← hk,← map_pCoreIn_of_injective 2 _ f hfi]
    exact map_mono hcore
  let τ' := τ.prod (Representation.trivial (ZMod 2) (Equiv.Perm (Fin 8)) F)
  have ha' := hA.map_equivariant σ τ' f hfi E he
  have hz : fixedCodim (Representation.trivial (ZMod 2) (Equiv.Perm (Fin 8)) F) (A.map f) = 0 := by
    have htop : fixedSpace (Representation.trivial (ZMod 2) (Equiv.Perm (Fin 8)) F) (A.map f) = ⊤ := by
      apply top_unique
      intro v _ a
      rfl
    rw [fixedCodim,htop]
    exact Module.finrank_zero_of_subsingleton
  have ha : IsOffender τ (A.map f) := by
    refine ⟨ha'.1,?_⟩
    simpa only [τ',fixedCodim_prod,hz,add_zero] using ha'.2
  exact no_seed_core_offender f.range hH Q P' hn hf ha hc

/-- A faithful action with an invariant supplement and a marked natural A8
submodule cannot have an offender in a moving Sylow-fixed seed core. -/
theorem no_natural_seed_core_offender (σ : Representation (ZMod 2) D U)
    (hσ : Function.Injective σ) (S : Subrepresentation σ)
    (K : Subgroup D) [K.Normal] (e : K ≃* alternatingGroup (Fin 8))
    (E : S.toSubmodule ≃ₗ[ZMod 2] natural (Fin 8))
    (he : ∀ g : K, ∀ v, E (S.toRepresentation g v) =
      alternatingNaturalRepresentation (Fin 8) (e g) (E v))
    (hsupp : S.toSubmodule ⊔ σ.invariants = ⊤)
    (P : Submodule (ZMod 2) U) (R : Sylow 2 K)
    (hfixed : P ≤ fixedSpace (σ.comp K.subtype) R)
    (hmoving : ¬ P ≤ Representation.invariants (σ.comp K.subtype))
    {A : Subgroup D} (hA : IsOffender σ A)
    (hcore : A ≤ (subspaceKernel σ P ⊤).pCoreIn 2) : False := by
  have hz : (alternatingNaturalRepresentation (Fin 8)).invariants = ⊥ := by
    apply invariants_eq_bot_of_faithful_irreducible
    · exact (naturalRepresentation_injective (Fin 8) (by decide)).comp Subtype.val_injective
    · exact alternatingNatural_isIrreducible (by decide)
  have hc : IsCompl S.toSubmodule σ.invariants := by
    apply isCompl_iff.mpr
    refine ⟨Submodule.disjoint_def.mpr ?_,codisjoint_iff.mpr hsupp⟩
    intro v hv hfv
    have hez : E ⟨v,hv⟩ ∈ (alternatingNaturalRepresentation (Fin 8)).invariants := by
      intro a
      obtain ⟨g,rfl⟩ := e.surjective a
      rw [← he]
      exact congrArg E (Subtype.ext (hfv g))
    rw [hz,Submodule.mem_bot] at hez
    exact congrArg (fun v : S.toSubmodule => (v : U)) (E.injective (hez.trans E.map_zero.symm))
  obtain ⟨f,hfe,hf,_⟩ := EightNormalizer.exists_ambient_hom S.toRepresentation K
    e.toMonoidHom e.surjective E he
  let q := S.fixedSummandCoordinates hc
  let X := q.trans (E.prodCongr (LinearEquiv.refl (ZMod 2) σ.invariants))
  have hX (g : D) (v : U) : X (σ g v) =
      (naturalRepresentation (Fin 8) (f g) (X v).1,(X v).2) := by
    have hh := S.fixedSummandCoordinates_intertwines hc g v
    change (E (q (σ g v)).1,(q (σ g v)).2) = _
    rw [hh]
    exact Prod.ext (hf g (q v).1) rfl
  have hfi : Function.Injective f := by
    intro g h heq
    apply hσ
    apply LinearMap.ext
    intro v
    apply X.injective
    rw [hX,hX,heq]
  have hH : alternatingGroup (Fin 8) ≤ f.range := by
    intro a ha
    obtain ⟨g,hg⟩ := e.surjective ⟨a,ha⟩
    exact ⟨g,(hfe g).trans (congrArg Subtype.val hg)⟩
  let Q := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hn : P.map (splitSeedProjection X) ≠ ⊥ := by
    intro hbot
    apply hmoving
    intro v hv g
    have hzero : splitSeedProjection X v = 0 := by
      have hm := Submodule.mem_map_of_mem (f := splitSeedProjection X) hv
      rwa [hbot,Submodule.mem_bot] at hm
    apply X.injective
    change X (σ g v) = X v
    rw [hX]
    apply Prod.ext
    · change naturalRepresentation (Fin 8) (f g) (splitSeedProjection X v) = splitSeedProjection X v
      rw [hzero,map_zero]
    · rfl
  have hp : P.map (splitSeedProjection X) ≤
      fixedSpace (alternatingNaturalRepresentation (Fin 8)) Q := by
    rintro _ ⟨v,hv,rfl⟩ a
    have ha : (a : alternatingGroup (Fin 8)) ∈ (R : Subgroup K).map e.toMonoidHom := a.property
    obtain ⟨g,hg,heq⟩ := ha
    have hh := congrArg Prod.fst ((hX g v).symm.trans
      (congrArg X (hfixed hv ⟨g,hg⟩)))
    change naturalRepresentation (Fin 8) a.val.val (splitSeedProjection X v) = splitSeedProjection X v
    rw [← heq]
    change naturalRepresentation (Fin 8) (e g).val (X v).1 = (X v).1
    change naturalRepresentation (Fin 8) (f g) (X v).1 = (X v).1 at hh
    rw [hfe g] at hh
    exact hh
  exact no_split_seed_core_offender σ f hfi hH X hX P Q hn hp hA hcore
end CFSG.Quasithin.ChapterB.Offenders.Eight.FourBlock
