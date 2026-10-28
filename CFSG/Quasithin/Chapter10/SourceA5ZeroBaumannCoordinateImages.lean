module
public import CFSG.Quasithin.Chapter10.SourceA5ZeroBaumannFactor
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerPairSections
public import Theory.GroupTheory.RestrictedCentralizerImage

/-!
# Literal zero-center Baumann coordinate images

The marked Baumann preimage maps to the literal product of the two transposition
four-groups.  Restricting the actual centralizer section to that image identifies
the image of the original centralizer with the corresponding opposite S₅ axis.
The two residual-axis alternatives are retained exactly as supplied by the
original paired-axis theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false in
theorem source_a5_zero_baumann_coordinate_images
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    let H := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
    let U := D.moduleSubgroup.subgroupOf H
    letI := (source_parabolic_module_reduced D).normal
    letI := (source_parabolic_module_reduced D).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let α := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let Y := offenderSubgroup α
    let A := L.subgroupOf H
    let R := ChapterB.baumann (S : Subgroup H)
    ∃ d : ChapterB.SourceInduction.SourceTwoFactorCase (α.comp Y.subtype),
      ∃ c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)),
      ∃ a b : Equiv.Perm (Fin 5),
      R = ((((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
        ((ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom)).map
          (Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom)).comap q ∧
      ((A.map q = (factorResidual q Y d.first).map q ∧
        (R ⊓ centralizer (A : Set H)).map q =
          (((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
            ((ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom)).map
            (Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom) ⊓
          d.second.map Y.subtype) ∨
       (A.map q = (factorResidual q Y d.second).map q ∧
        (R ⊓ centralizer (A : Set H)).map q =
          (((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
            ((ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom)).map
            (Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom) ⊓
          d.first.map Y.subtype)) := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf H
  have hU := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let A := L.subgroupOf H
  let R := ChapterB.baumann (S : Subgroup H)
  obtain ⟨d,c,hex,hN,haxis⟩ := source_a5_zero_original_centralizer_axes D e hn hout hz
  obtain ⟨_,a,b,hab⟩ := paired_thompson_baumann_of_symmetric_model S
    (source_a5_minimal_parabolic D e hn) U hU (source_local_thompson_not_centralizes D hout)
    q hq hk d c hex
  let F := ((((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
      ((ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom)).map
        (Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom))
  let P : Subgroup H := Y.comap q ⊓ centralizer (A : Set H)
  have hR : R = F.comap q := by
    have hF : R.map q = F := by
      simpa [F, Y, α] using hab
    rw [←hF,comap_map_eq_self (hk.trans
      (source_a5_zero_centralizer_paired_action D e hn hout hz).2 ▸
        source_a5_zero_core_le_baumann D e hn hout hz)]
  have hFY : F ≤ Y := by
    rintro _ ⟨v,hv,rfl⟩
    exact (c.action.groupEquiv.symm v).property
  have hs : OriginalCentralizerImageSection D (L.subgroupOf H) := by
    exact source_a5_zero_centralizer_image_section D e hn hout hz
  have hsection : ∃ σ : P.map q →* P,
      (q.comp P.subtype).comp σ = (P.map q).subtype := by
    change ∃ σ : P.map q →* P,
      (q.comp P.subtype).comp σ = (P.map q).subtype at hs
    exact hs
  refine ⟨d,c,a,b,hR,?_⟩
  rcases haxis with h | h
  · have hPmap : P.map q = d.second.map Y.subtype := by
      simpa [P] using h.2
    left
    refine ⟨h.1, ?_⟩
    exact map_inf_centralizer_eq_of_section q Y F (d.second.map Y.subtype)
      R A P hR rfl hPmap hFY hsection
  · have hPmap : P.map q = d.first.map Y.subtype := by
      simpa [P] using h.2
    right
    refine ⟨h.1, ?_⟩
    exact map_inf_centralizer_eq_of_section q Y F (d.first.map Y.subtype)
      R A P hR rfl hPmap hFY hsection
end CFSG.Quasithin.Chapter10
