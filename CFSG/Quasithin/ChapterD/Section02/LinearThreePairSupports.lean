module
public import CFSG.Quasithin.ChapterD.Section02.LinearThreeSimpleTypes
public import Theory.Representation.BinaryTensorThree.Recognition
public import Theory.Representation.BinaryOffender.CommutingPerfectSupports

/-!
# Full supports for two normal linear-three factors

If both factor restrictions of a simple product constituent have natural
binary-three types, movement by both factors reconstructs a tensor marking.
Excluding that marking therefore forces one factor to act trivially.
Clifford restriction applies this separation to each irreducible ambient
section. Commuting perfect displacement then lifts it through arbitrary
extensions, without assuming that the original representation is semisimple.
The product coordinates retain the literal inclusions of both factors;
they need not be conjugate in the ambient group.

The original normal-pair consumer in Chapter14 supplies the tensor exclusion.
Recognition of its two families of natural types remains with
qt-e-suitable-component-supports. This module proves their support consequence,
not the source recognition premise.
Source: Aschbacher--Smith D.3.7, F.9.18 and14.6.22(2),
printed pp.197--199,325--326,1038.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD
universe u
variable {G V : Type u} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

/-- Natural types and the absence of tensor constituents separate the two
literal factor actions on a simple constituent. -/
theorem natural_pair_constituent_single_factor
    (σ : Representation (ZMod 2) G V) (N D E : Subgroup G)
    [Group.IsPerfect D] [Group.IsPerfect E]
    (p : N ≃* (D × E)) (hp : ∀ d c, (p.symm (d,c)).val = d.val * c.val)
    (htD : NaturalLinearThreeTypes σ D) (htE : NaturalLinearThreeTypes σ E)
    (U : Subrepresentation (σ.comp N.subtype)) (hi : IsIrreducible U.toRepresentation)
    (hno : ∀ b : N ≃* BinaryTensorThree.Factor × BinaryTensorThree.Factor,
      ¬ Nonempty (Representation.Equiv U.toRepresentation
        (BinaryTensorThree.baseRepresentation.comp b.toMonoidHom))) :
    D.subgroupOf N ≤ U.toRepresentation.ker ∨ E.subgroupOf N ≤ U.toRepresentation.ker := by
  have hleft (d : D) : (p.symm (d,1)).val = d.val := by simpa using hp d 1
  have hright (c : E) : (p.symm (1,c)).val = c.val := by simpa using hp 1 c
  let ρ : Representation (ZMod 2) (D × E) U.toSubmodule := U.toRepresentation.comp p.symm.toMonoidHom
  let : IsIrreducible ρ :=
    (irreducible_comp_surjective_iff p.symm.toMonoidHom p.symm.surjective U.toRepresentation).mpr hi
  have hsep : ρ.comp (MonoidHom.inl D E) = 1 ∨ ρ.comp (MonoidHom.inr D E) = 1 := by
    by_cases hl : ρ.comp (MonoidHom.inl D E) = 1
    · exact Or.inl hl
    right
    by_contra hc
    obtain ⟨b,⟨f⟩⟩ := BinaryTensorThree.exists_marking_of_moving_natural_types ρ hl hc
      (natural_linear_three_of_nested_conjugate σ D N htD U
        (p.symm.toMonoidHom.comp (MonoidHom.inl D E)) 1
        (fun d => by simpa using hleft d))
      (natural_linear_three_of_nested_conjugate σ E N htE U
        (p.symm.toMonoidHom.comp (MonoidHom.inr D E)) 1
        (fun c => by simpa using hright c))
    apply hno (p.trans b)
    refine ⟨Representation.Equiv.mk f.toLinearEquiv ?_⟩
    intro n
    have hf := f.isIntertwining' (p n)
    simpa only [ρ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,p.symm_apply_apply,
      MulEquiv.trans_apply] using hf
  rcases hsep with hl | hc
  · left
    intro d hd
    have hh := congrArg (fun f : Representation (ZMod 2) D U.toSubmodule => f ⟨d,hd⟩) hl
    change U.toRepresentation (p.symm (⟨d,hd⟩,1)) = 1 at hh
    have he : p.symm (⟨d,hd⟩,1) = d := Subtype.ext (hleft ⟨d,hd⟩)
    rwa [he] at hh
  · right
    intro c hcMem
    have hh := congrArg (fun f : Representation (ZMod 2) E U.toSubmodule => f ⟨c,hcMem⟩) hc
    change U.toRepresentation (p.symm (1,⟨c,hcMem⟩)) = 1 at hh
    have he : p.symm (1,⟨c,hcMem⟩) = c := Subtype.ext (hright ⟨c,hcMem⟩)
    rwa [he] at hh

/-- Separation of the simple factor actions lifts through all nonsplit
extensions for two normal perfect factors. -/
theorem natural_normal_pair_full_supports_centralize
    (ρ : Representation (ZMod 2) G V) (N D E : Subgroup G)
    [N.Normal] [D.Normal] [E.Normal] [Group.IsPerfect D] [Group.IsPerfect E]
    (p : N ≃* (D × E)) (hp : ∀ d c, (p.symm (d,c)).val = d.val * c.val)
    (htypes : ∀ (S : Subrepresentation ρ) (L : Subrepresentation S.toRepresentation),
      IsIrreducible L.quotientRepresentation →
      NaturalLinearThreeTypes L.quotientRepresentation D ∧ NaturalLinearThreeTypes L.quotientRepresentation E)
    (hno : ∀ (S : Subrepresentation ρ) (L : Subrepresentation S.toRepresentation)
      (U : Subrepresentation (L.quotientRepresentation.comp N.subtype))
      (b : N ≃* BinaryTensorThree.Factor × BinaryTensorThree.Factor),
      ¬ Nonempty (Representation.Equiv U.toRepresentation
        (BinaryTensorThree.baseRepresentation.comp b.toMonoidHom))) :
    subspaceCommutator ρ ⊤ D ≤ fixedSpace ρ E := by
  have hleft (d : D) : (p.symm (d,1)).val = d.val := by simpa using hp d 1
  have hright (c : E) : (p.symm (1,c)).val = c.val := by simpa using hp 1 c
  have hDN : D ≤ N := by
    intro d hd
    simpa only [hleft] using (p.symm (⟨d,hd⟩,1)).property
  have hEN : E ≤ N := by
    intro c hc
    simpa only [hright] using (p.symm (1,⟨c,hc⟩)).property
  have hcomm : ∀ d ∈ D, ∀ c ∈ E, Commute d c := by
    intro d hd c hc
    have hh : Commute ((⟨d,hd⟩ : D),(1 : E)) ((1 : D),(⟨c,hc⟩ : E)) := by
      show ((⟨d,hd⟩ : D),(1 : E)) * ((1 : D),(⟨c,hc⟩ : E)) = _
      simp
    have hh' := congrArg Subtype.val (hh.map p.symm.toMonoidHom).eq
    simpa only [Subgroup.coe_mul,MulEquiv.coe_toMonoidHom,hleft,hright,Commute,SemiconjBy] using hh'
  apply (subspaceCommutator_eq_bot_iff ρ _ E).mp
  apply mixed_commutator_eq_bot_of_irreducible_sections ρ D E hcomm
    (fun g => Or.inl ⟨normal_iff_map_conj_eq.mp inferInstance g,
      normal_iff_map_conj_eq.mp inferInstance g⟩)
  intro S L hL
  let σ := L.quotientRepresentation
  let : IsSemisimpleModule (MonoidAlgebra (ZMod 2) N) (Representation.asModule (σ.comp N.subtype)) :=
    NormalConstituentDisplacement.restriction_semisimple σ hL N
  apply mixed_commutator_eq_bot_of_semisimple_restriction σ N D E hDN hEN
  intro U hi
  exact natural_pair_constituent_single_factor σ N D E p hp
    (htypes S L hL).1 (htypes S L hL).2 U hi (hno S L U)

end CFSG.Quasithin.ChapterD
