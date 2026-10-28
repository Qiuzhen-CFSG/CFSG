module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.OddTwo
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.Borel
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The original nonbinary symplectic Borel and diagram marking

The actual normal star component is aligned with the original Sylow.
The proved minimal-parabolic source gives its Borel overlap and a genuine
Sylow actor moving a parabolic class. Perfectness identifies the full
nonbinary symplectic group with its literal derived subgroup, and the
same equivalence transports both the Borel and diagram conclusions.
The field-two derived group is not silently replaced by the full group.

Source: Aschbacher–Smith E.2.2(2b), printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]
private theorem preserves_map {A B:Type*} [Group A] [Group B]
    (e:A≃*B) (a:MulAut A) (P:Subgroup A)
    (h:PreservesParabolicClass a P) :
    PreservesParabolicClass (MulAut.congr e a) (P.map e.toMonoidHom) := by
  obtain ⟨g,hg⟩:=h
  refine ⟨e g,?_⟩
  have ha:(MulAut.congr e a).toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp a.toMonoidHom := by ext x; simp
  have hc:(MulAut.conj (e g)).toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp (MulAut.conj g).toMonoidHom := by ext x; simp [MulAut.conj_apply]
  rw [map_map,ha,←map_map,hg,map_map,←hc,←map_map]

theorem source_binary_symplectic_model (T:Sylow 2 H)
    (hP:ChapterB.IsMinimalParabolicOver T ⊤) (hs:¬Group.IsSolvable H)
    (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hgen:K⊔(T:Subgroup H)=⊤) {n:ℕ} (hn:1<n)
    (hm:ClassicalGroup.IsPSp (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 (2^n)) :
    DiagramModel (ChapterB.minimalParabolicMax T hP) K (T:Subgroup H) n := by
  let M:=ChapterB.minimalParabolicMax T hP
  let J:=sourceKernel M
  let q:=QuotientGroup.mk' J
  let S:=T.mapSurjective (QuotientGroup.mk'_surjective J)
  let D:=sourceImage M K
  have hi:=Structure.source_normal_simple_image T hP hs K hK hgen
  let : D.Normal:=hi.2.2.1
  have hmin:=(Structure.source_star_minimal_core_free T hP).1
  have hmax:ChapterB.minimalParabolicMax S hmin=M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'];exact le_rfl)).symm
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩:=hm
  let : Fintype F:=Fintype.ofFinite F
  let : CharP F 2:=charP_of_card_eq_prime_pow (p:=2) (f:=n)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let e0:D≃*Sp F:=e.trans EvenProjective.equiv.symm
  obtain ⟨g,_,⟨t,ht⟩,hB⟩:=Structure.SymplecticFour.source_diagram_and_borel hcard hn S hmin D e0 hi.2.2.2
  let e':=e0.trans (MulAut.conj g)
  have hq:2<Nat.card F:=by
    rw [hcard]
    exact (by norm_num : 2=2^1) ▸ Nat.pow_lt_pow_right (by decide) hn
  let d:Sp4Derived F≃*Sp F:=derivedEquivFull_of_card_gt_two hq
  let ed:D≃*Sp4Derived F:=e'.trans d.symm
  have hctop:commutator (Sp F)=⊤:=by
    let := perfect_of_card_gt_two hq
    exact Group.IsPerfect.commutator_eq_top
  have hdcoe : d.toMonoidHom = (commutator (Sp F)).subtype := by
    apply MonoidHom.ext
    intro x
    exact derivedEquivFull_of_card_gt_two_apply hq x
  have hd (P:Subgroup (Sp F)) : (P.subgroupOf (Sp4Derived F)).map d.toMonoidHom=P := by
    rw [hdcoe]
    change (P.subgroupOf (commutator (Sp F))).map (commutator (Sp F)).subtype=P
    simp only [subgroupOf_map_subtype,hctop,inf_top_eq]
  have hcomp:d.toMonoidHom.comp ed.toMonoidHom=e'.toMonoidHom := by ext x;simp [ed]
  refine Or.inr ⟨F,hF,hfin,inferInstance,by omega,hcard,ed,?_,?_⟩
  · apply map_injective (f:=d.toMonoidHom) d.injective
    rw [map_map,hcomp,hd]
    rw [source_overlap_coordinate]
    change ((M.map q).subgroupOf D).map e'.toMonoidHom=Theory.SpecificGroups.SymplecticFour.borel (F:=F)
    rw [←hB,hmax]
    exact (comap_equiv_eq_map_symm e'.symm _).symm
  · refine ⟨MulAut.conjNormal (t:H⧸J),?_,?_⟩
    · rw [sourceAutomizer_eq_map_conjNormal]
      exact mem_map_of_mem _ t.property
    · intro hp
      have ha : MulAut.congr d (MulAut.congr ed (MulAut.conjNormal (t:H⧸J))) =
          DiagramAutomorphisms.extensionAction D e'.symm t := by
        ext x
        simp [MulAut.congr_apply,ed,DiagramAutomorphisms.extensionAction]
        rfl
      have h1:=preserves_map d _ _ hp.1
      have h2:=preserves_map d _ _ hp.2
      rw [ha,hd] at h1 h2
      exact ht ⟨h1,h2⟩
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
