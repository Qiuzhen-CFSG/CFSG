module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.SymmetricSixSource.KernelLength
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.SymmetricSixSource.ResidualMarking
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.SymmetricSixModel
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.ParabolicApplication
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.ClosurePair

/-!
# Three noncentral binary chief factors in the original S₆ case

The marked seed plane identifies the actual star image of L₁ with a
conjugate syntheme A₄. Every cubic subgroup of that residual acts without
fixed vectors on the four-dimensional natural S₆ quotient, giving cubic
length two. The original point and component-fixed layers are central for
this actor, and [Q_H,K]=U_H transfers that length to Q_H∩L₁. The A₄ quotient
contributes one further noncentral binary chief factor. Thus every complete
chief series of the unchanged original L₁ has count three.

All marking, commutator and containment inputs are discharged from the
original source configuration and its natural central quotient. No model
identification of the whole U_H or splitting of its central layers is used.
Source: Aschbacher–Smith 13.5.24, printed p.925.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.SymmetricSixSource
open Recognition Recognition.Configuration Recognition.MarkedModule Recognition.MarkedModule.AlternatingParabolics
open Section08.Source Section08.SourceCompletion SymmetricSixModel
variable {G : Type*} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

theorem marked_closure_length_two {K : Subgroup G}
    (hKH : K ≤ D.H) (hLK : D.L₁ ≤ K)
    (f : Catalogue.actor D K ≃* Equiv.Perm (Fin 6))
    (fV : CentralQuotient.Space D h K ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (hfV : ∀ b : Catalogue.actor D K, ∀ u,
      centralProjection D h fV (Action.starRepresentation D h b.val u) =
        BinaryPermutation.naturalRepresentation (Fin 6) (f b) (centralProjection D h fV u))
    (c : starImage D.H K ≃* alternatingGroup (Fin 6))
    (hc : ∀ k, (c k).val = f ⟨k.val, mem_sup_left k.property⟩)
    (g : alternatingGroup (Fin 6))
    (hg : ((starImage D.H D.L₁).subgroupOf (starImage D.H K)).map c.toMonoidHom =
      residual.map (MulAut.conj g).toMonoidHom)
    (A : Subgroup G) (hAL : A ≤ D.L₁) (hA : Nat.card A = 3) :
    conjugationCubicLength A D.UH = 2 := by
  have hAK := hAL.trans hLK
  have hAH := hAK.trans hKH
  let aK : A →* starImage D.H K := (starActor D A hAH).codRestrict _
    (fun x => ⟨inclusion hAH x, hAK x.property, rfl⟩)
  let aB : A →* Catalogue.actor D K := (inclusion le_sup_left).comp aK
  let a6 := c.toMonoidHom.comp aK
  have haK : Function.Injective aK := by
    intro x y he
    apply starMap_injective_cubic D A hAH hA
    have he' : starActor D A hAH x = starActor D A hAH y :=
      congrArg (fun z : starImage D.H K => z.val) he
    exact Subtype.ext he'
  have ha6 : Function.Injective a6 := c.injective.comp haK
  have hrange : a6.range ≤ residual.map (MulAut.conj g).toMonoidHom := by
    rw [←hg]
    rintro _ ⟨x,rfl⟩
    exact ⟨aK x, ⟨inclusion hAH x,hAL x.property,rfl⟩,rfl⟩
  have hn : Representation.BinaryFixedPoints.fixedIndex
      ((BinaryPermutation.naturalRepresentation (Fin 6)).comp (f.toMonoidHom.comp aB)) = 16 := by
    have he : (BinaryPermutation.naturalRepresentation (Fin 6)).comp (f.toMonoidHom.comp aB) =
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)).comp a6 := by
      apply MonoidHom.ext
      intro x
      apply LinearMap.ext
      intro u
      change BinaryPermutation.naturalRepresentation (Fin 6) (f (aB x)) u =
        BinaryPermutation.naturalRepresentation (Fin 6) (c (aK x)).val u
      rw [hc]
      rfl
    rw [he]
    exact conjugate_fixedIndex a6 ha6 hA g hrange
  calc
    conjugationCubicLength A D.UH = Nat.log 4
        (Representation.BinaryFixedPoints.fixedIndex
          ((BinaryPermutation.naturalRepresentation (Fin 6)).comp (f.toMonoidHom.comp aB))) :=
      closure_length_through_central_projection D h A hAK hKH hA f fV hfV aB (fun _ => rfl)
    _ = 2 := by rw [hn]; decide

/-- Three noncentral binary chief factors on the literal original local residual. -/
theorem source_count_three {V₂ M : Subgroup G}
    (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hU : ¬IsMulCommutative D.UH)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hc : centralizer (D.Vplus : Set G) ≤ M ⊓ normalizer (D.V : Set G))
    (K : Subgroup G) (s : Selected D K) (hLK : D.L₁ ≤ K)
    (f : Catalogue.actor D K ≃* Equiv.Perm (Fin 6))
    (fV : CentralQuotient.Space D h K ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (hfV : ∀ b : Catalogue.actor D K, ∀ u,
      centralProjection D h fV (Action.starRepresentation D h b.val u) =
        BinaryPermutation.naturalRepresentation (Fin 6) (f b) (centralProjection D h fV u))
    (A : Subgroup G) (hAL : A ≤ D.L₁) (hA : Nat.card A = 3)
    (t : NoncentralChiefRefinement.ChiefSeries D.L₁) (h0 : t.head = ⊥) (h1 : t.last = ⊤) :
    t.noncentralTwoCount = 3 := by
  have hi := NormalBranch.SourceOrthogonal.seed_index d
  have hSQ := (Chapter1.Section02.uniqueness_local_quotient_sqtk
    d.counterexample.qtke (OriginalSix.selected_H_mem h)).stronglyQuasithin
  have hm := OriginalSix.source_local_component_commutator d h e h1221 hc K s
  obtain ⟨S,hS,hirr⟩ := OriginalSix.source_local_seed_irreducible d h hU
  let := hirr
  have hmodule := source_module_conditions h hi hU
    (NormalBranch.ReturningPlane.module_card d)
    (by rw [OriginalSix.residual_eq_sourceOne d h];
        exact (Section07.ModelExclusions.seed_commutator_point_residual d).symm)
  obtain ⟨c,hc,g,hg⟩ := symmetric_six_residual_marking D h s hSQ hLK hm S hS
    hmodule.2.2 hmodule.2.1.symm f fV hfV
  have hLC : starImage D.H D.L₁ ≤ starImage D.H K := map_mono (comap_mono hLK)
  let eL : starImage D.H D.L₁ ≃* alternatingGroup (Fin 4) :=
    ((subgroupOfEquivOfLe hLC).symm.trans
      (c.subgroupMap ((starImage D.H D.L₁).subgroupOf (starImage D.H K)))).trans
      ((MulEquiv.subgroupCongr hg).trans (conjugateResidualEquiv g))
  have hgroup := group_conclusions s h hSQ hi hU hLK (OriginalSix.seed_identity d h) hm
    (selected_actor_normalization s h hi hU).2
  have htilde := symmetric_six_tilde_generation D h s d.counterexample.qtke.properK hSQ
    hLK (OriginalSix.seed_identity d h) hm S hS hmodule.2.2 hmodule.2.1.symm f fV hfV
  have hUL : D.UH ≤ D.L₁ :=
    (OriginalSix.ClosurePair.closure_reduction_of_tilde d h htilde).2.1.trans (pCoreIn_le 2 D.L₁)
  rw [count_eq_kernel_length_add_one D h eL A hAL hA t h0 h1,
    kernel_length_eq_closure D h A hAL hLK hA hgroup.2.2.2 hUL,
    marked_closure_length_two D h s.le_H hLK f fV hfV c hc g hg A hAL hA]

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.SymmetricSixSource
