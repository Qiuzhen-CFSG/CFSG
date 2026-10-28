module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.ProjectiveGaschutz.CentralLift
public import Theory.Representation.BinaryConjugationSection.FixedSplitting
public import Theory.Representation.PSL3Two.SteinbergStructure.Projectivity
public import Theory.Representation.Quotient
public import Theory.GroupTheory.IrreducibleSectionCore

/-!
# The marked Steinberg splitting in 14.7.74

Irreducibility of the original S/V forces O₂(LT) to centralize this section.
Thus the commutator cocycle of each element of Q vanishes on ker(d.qL)=S
and descends through the original natural-module marking d.qL. Projectivity
of the concrete Steinberg action kills its first cohomology. Correcting the
original element by a lift in S gives Q=QC S and QC∩S=V, with the explicit
multiplication isomorphism in the original Q/V.

The later first Gaschütz commutator bound is not proved in this increment.
The consumer below retains that premise and the natural-extension premise;
final 14.7.74 assembly remains with LocalCollapse. Earlier inputs in Prior
are produced by the 14.7.71--73 chief-factor, Steinberg and root branches.

Source: Aschbacher--Smith, 14.7.74, printed p.1077 (PDF p.1094),
combined manuscript of 1 March 2004.
-/

public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (a : Prior d)

include a in
theorem S_le_Q : S L F ≤ Q T L := by
  rw [a.core]
  exact pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer a.sylow_normalizes)

include a in
/-- The original Steinberg chief section is centralized by O₂(LT). -/
theorem S_Q_commutator_le : ⁅S L F, Q T L⁆ ≤ V := by
  let J := L ⊔ (T : Subgroup G)
  have hLJ : L ≤ J := le_sup_left
  have hSJ : S L F ≤ J := a.steinberg.section_le.trans hLJ
  have hVJ : V ≤ J := a.steinberg.kernel_le.trans hSJ
  have hJN : J ≤ normalizer (S L F : Set G) := by
    rw [a.core]
    exact (sup_le L.le_normalizer a.sylow_normalizes).trans
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hJV : J ≤ normalizer (V : Set G) :=
    sup_le d.natural.chosen.normalizes (by simpa only [F.last] using F.invariant 3)
  let : (V.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJV
  let : ((S L F).subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJN
  let : IsIrreducible (BinaryLinearThree.S.comp d.qL) :=
    (irreducible_comp_surjective_iff d.qL d.qL_surjective BinaryLinearThree.S).mpr
      BinaryLinearThree.IrreducibleCatalogue.steinberg_irreducible
  have hirr (E : Subgroup J) (hv : V.subgroupOf J ≤ E)
      (hs : E ≤ (S L F).subgroupOf J) (hn : E.Normal) :
      E = V.subgroupOf J ∨ E = (S L F).subgroupOf J := by
    have hve : V ≤ E.map J.subtype := by
      simpa only [map_subgroupOf_eq_of_le hVJ] using map_mono (f := J.subtype) hv
    have hes : E.map J.subtype ≤ S L F := by
      simpa only [map_subgroupOf_eq_of_le hSJ] using map_mono (f := J.subtype) hs
    have hnorm : L ≤ normalizer (E.map J.subtype : Set G) := by
      apply le_normalizer_iff.mpr
      intro l hl x hx
      obtain ⟨e,he,rfl⟩ := hx
      exact ⟨⟨l,hLJ hl⟩ * e * ⟨l,hLJ hl⟩⁻¹, hn.conj_mem e he ⟨l,hLJ hl⟩, rfl⟩
    rcases a.steinberg.eq_kernel_or_section (E.map J.subtype) hve hes hnorm with hv | hs
    · left
      apply map_injective J.subtype_injective
      simpa only [map_subgroupOf_eq_of_le hVJ] using hv
    · right
      apply map_injective J.subtype_injective
      simpa only [map_subgroupOf_eq_of_le hSJ] using hs
  have hp : IsPGroup 2 ((S L F).subgroupOf J) :=
    ((isPGroup_pCoreIn 2 J).to_le (S_le_Q d a)).comap_subtype
  have hc := commutator_pCore_le_of_irreducible_section
    (V.subgroupOf J) ((S L F).subgroupOf J)
    (subgroupOf_mono J a.steinberg.kernel_le) hp hirr
  have hm := map_mono (f := J.subtype) hc
  rw [map_commutator, map_subgroupOf_eq_of_le hSJ, map_subgroupOf_eq_of_le hVJ] at hm
  exact hm

include a in
/-- Projectivity kills commutator cocycles for the same marked action as the
source natural module. This does not presume Q/V is elementary abelian. -/
theorem Q_eq_QC_sup_S : Q T L = QC T L V ⊔ S L F := by
  let := BinaryLinearThree.SteinbergStructure.subsingleton_H1
  apply a.steinberg.sup_fixedPreimage_eq d.qL d.qL_surjective (Q T L)
    (S_le_Q d a) (Q_normalizes_V (F := F))
  · rw [commutator_comm, a.commutator]
  · intro l hl x hx
    have hlS : (l : G) ∈ S L F := by
      rw [d.qL_ker, ← a.core] at hl
      exact hl
    exact commutator_le.mp (S_Q_commutator_le d a) l hlS x hx

include a in
/-- The two literal summands meet in precisely V. -/
theorem QC_inf_S_eq : QC T L V ⊓ S L F = V := by
  let : IsSimpleGroup BinaryLinearThree.Group := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsIrreducible BinaryLinearThree.S :=
    BinaryLinearThree.IrreducibleCatalogue.steinberg_irreducible
  exact a.steinberg.inf_fixedPreimage_eq d.qL d.qL_surjective (Q T L)
    (S_le_Q d a) (Q_normalizes_V (F := F)) d.natural.chosen.normalizes
    (OneCohomology.fixed_eq_bot_of_faithful_irreducible BinaryLinearThree.S
      BinaryLinearThree.steinberg_injective)
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (a : Prior d)
include a

/-- The source direct sum is the internal direct product in the literal Q/V.
The displayed isomorphism multiplies the two original quotient images. -/
theorem quotient_splitting :
    letI : (V.subgroupOf (Q T L)).Normal :=
      normal_subgroupOf_of_le_normalizer (Q_normalizes_V (F := F))
    let q := QuotientGroup.mk' (V.subgroupOf (Q T L))
    IsCompl (((QC T L V).subgroupOf (Q T L)).map q)
      (((S L F).subgroupOf (Q T L)).map q) ∧
    ∃ e : (((QC T L V).subgroupOf (Q T L)).map q) ×
        (((S L F).subgroupOf (Q T L)).map q) ≃* (Q T L ⧸ V.subgroupOf (Q T L)),
      ∀ c s, e (c,s) = c * s := by
  let : (V.subgroupOf (Q T L)).Normal :=
    normal_subgroupOf_of_le_normalizer (Q_normalizes_V (F := F))
  let q := QuotientGroup.mk' (V.subgroupOf (Q T L))
  have hgen : (QC T L V).subgroupOf (Q T L) ⊔ (S L F).subgroupOf (Q T L) = ⊤ := by
    rw [← subgroupOf_sup (show QC T L V ≤ Q T L from commutatorPreimage_le _ _ _) (S_le_Q d a),
      ← Q_eq_QC_sup_S d a, subgroupOf_self]
  have hk : q.ker = (QC T L V).subgroupOf (Q T L) ⊓ (S L F).subgroupOf (Q T L) := by
    rw [QuotientGroup.ker_mk']
    change V.subgroupOf (Q T L) = ((QC T L V) ⊓ S L F).subgroupOf (Q T L)
    rw [QC_inf_S_eq d a]
  apply image_directProduct_of_ker_eq_inf q (QuotientGroup.mk'_surjective _) _ _ hgen hk
  apply commutator_le.mpr
  intro c hc s hs
  rw [QuotientGroup.ker_mk']
  change ⁅(c : G), (s : G)⁆ ∈ V
  exact commutator_le.mp (QC_commutator_le (F := F)) c hc s (a.steinberg.section_le hs)
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (a : Prior d)
include a

/-- The proved marked splitting discharges the projective premise of the
actual collapse consumer. The Gaschütz and natural-extension steps remain
explicit and are not asserted by this conditional application. -/
theorem conclusions_of_projective_splitting
    (hKC : ⁅QC T L V, K F⁆ ≤ F.U)
    (hdisp : V < QC T L V → ⁅QC T L V, (F.Li L 1).pCoreIn 2⁆ = V) :
    normalizer (L : Set G) = L ∧
    S L F = (normalizer (L : Set G)).pCoreIn 2 ∧
    F.H = K F ⊔ (T : Subgroup G) ∧
    F.H.pCoreIn 2 = (K F).pCoreIn 2 ∧
    ChapterJ.sylowCenter T = F.Vi 1 ∧ F.H = ChapterJ.centralizerOfSylowCenter T := by
  exact conclusions_of_extension_inputs d a (Q_eq_QC_sup_S d a) hKC hdisp

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse
