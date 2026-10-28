module

public import Theory.Representation.AlternatingSevenFiveRestriction.DeletedMoved
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveSection
/-!
# The original A₅ quotient marking on a deleted A₇ moved space

Transport the local component through its actual alternating-seven image.
The image marking is the original quotient by the two-core on every
original element. The deleted restriction theorem therefore identifies the
literal moved subspace with the deleted five-letter module for that marking.
The final theorem transports these coordinates back to any given original
module, retaining its original action and actual moved subspace.

Source: Aschbacher–Smith, 10.2.9, printed pp.751–752, the deleted A₇
row; the fixed-pair restriction is C.5.13, printed p.163.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open BinaryPermutation
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings

/-- The original quotient marking identifies the literal moved subspace in deleted A₇. -/
theorem alternatingSeven_five_section_moved_equiv
    {G : Type*} [Group G] [Finite G]
    (f : G →* alternatingGroup (Fin 7)) (hf : Function.Surjective f)
    (hks : Group.IsSolvable f.ker) (S : Sylow 2 G) (L : Subgroup G)
    (hL : L ∈ localCComponents S) (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    ∃ E : subspaceCommutator ((alternatingNaturalRepresentation (Fin 7)).comp f) ⊤ L ≃ₗ[ZMod 2]
        natural (Fin 5), ∀ (l : L) v,
      (E.symm (alternatingNaturalRepresentation (Fin 5)
        (e (QuotientGroup.mk' (pCore 2 L) l)) v) : natural (Fin 7)) =
        alternatingNaturalRepresentation (Fin 7) (f l) (E.symm v) := by
  let d := alternatingGroup.SevenFiveSection.imageFiveEquiv f L hk e
  obtain ⟨E,hE⟩ := exists_five_natural_moved_equiv (L.map f) d (S.mapSurjective hf)
    (alternatingSeven_five_section_image_normalized f hf hks S L hL hk e)
  let E' := (LinearEquiv.ofEq _ _
    (subspaceCommutator_comp_map (alternatingNaturalRepresentation (Fin 7)) f ⊤ L)).trans E
  refine ⟨E',?_⟩
  intro l v
  have h := hE (f.subgroupMap L l) v
  rw [alternatingGroup.SevenFiveSection.imageFiveEquiv_apply] at h
  exact h

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The same identification on an original module with given deleted-A₇ coordinates. -/
theorem alternatingSeven_five_section_moved_equiv_of_equivariant
    {G : Type*} [Group G] [Finite G]
    (f : G →* alternatingGroup (Fin 7)) (hf : Function.Surjective f)
    (hks : Group.IsSolvable f.ker) (S : Sylow 2 G) (L : Subgroup G)
    (hL : L ∈ localCComponents S) (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (ρ : Representation (ZMod 2) G V) (F : V ≃ₗ[ZMod 2] natural (Fin 7))
    (hF : ∀ g v, F (ρ g v) = alternatingNaturalRepresentation (Fin 7) (f g) (F v)) :
    ∃ E : subspaceCommutator ρ ⊤ L ≃ₗ[ZMod 2] natural (Fin 5),
      ∀ (l : L) v,
      (E.symm (alternatingNaturalRepresentation (Fin 5)
        (e (QuotientGroup.mk' (pCore 2 L) l)) v) : V) = ρ l (E.symm v) := by
  obtain ⟨E,hE⟩ := alternatingSeven_five_section_moved_equiv f hf hks S L hL hk e
  let M := subspaceCommutator ((alternatingNaturalRepresentation (Fin 7)).comp f) ⊤ L
  have hm : subspaceCommutator ρ ⊤ L = M.map F.symm.toLinearMap := by
    have hh := subspaceCommutator_map_embedding ρ
      ((alternatingNaturalRepresentation (Fin 7)).comp f) (MonoidHom.id G) F.symm.toLinearMap
      (fun g v => by
        apply F.injective
        change F (ρ g (F.symm v)) =
          F (F.symm (alternatingNaturalRepresentation (Fin 7) (f g) v))
        rw [hF, F.apply_symm_apply, F.apply_symm_apply]) L ⊤
    simpa only [Submodule.map_top, LinearEquiv.range, Subgroup.map_id] using hh
  let T := ((LinearEquiv.ofEq _ _ hm).trans
    (Submodule.equivMapOfInjective F.symm.toLinearMap F.symm.injective M).symm).trans E
  refine ⟨T,?_⟩
  intro l v
  apply F.injective
  change F (F.symm (E.symm (alternatingNaturalRepresentation (Fin 5)
    (e (QuotientGroup.mk' (pCore 2 L) l)) v))) = F (ρ l (F.symm (E.symm v)))
  rw [F.apply_symm_apply, hF, F.apply_symm_apply]
  exact hE l v
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
