module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup.Frame
public import Theory.Representation.SpecialLinearThreeFrameGeometry.Transitivity

/-!
# The original point-stabilizer orbit for the complement argument

Projective two-transitivity of the actual SL₃(2) model supplies an actor fixing
V₁ᵍ and carrying V₁ to any other original point V₁ˣ. Lift this actor through
the literal star projection to L. Its point fixation puts it in Hᵍ, so the
transporter belongs to L ∩ Hᵍ as required by the symmetric centralizer bounds.
All changes of subspace are transported through the original conjugation
coordinates, retaining the right-conjugation convention.

The natural module has no nonidentity L-fixed point: irreducibility reduces
the contrary case to trivial action, contradicting the original g outside H.
These two results supply the remaining orbit and fixed-space premises of the
natural complement, with no new geometry assumption.

Source: Aschbacher--Smith, the last paragraph of 14.4.7,
printed p.1009; refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension.RankCore.GaschutzComplement
open Matrix.PSL3.PointRadicalGeneration
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem coordinate_conjugate (F : InvariantFlag T V 3) (g l : G)
    (B : ChapterG.Section02.LinearThree.Hypothesis (sourceSetup F L) (ZMod 2) 1 g l)
    (A C : Subgroup G) (hAV : A ≤ V) (hCV : C ≤ V)
    (P Q : Submodule (ZMod 2) (Fin 3 → ZMod 2))
    (hP : ∀ v : V, (v : G) ∈ A ↔ (B.coordinates v).toAdd ∈ P)
    (hQ : ∀ v : V, (v : G) ∈ C ↔ (B.coordinates v).toAdd ∈ Q)
    (t : L) (he : Q.map (Matrix.SpecialLinearGroup.FrameGeometry.natural
      (B.model (ChapterG.Section02.LinearThree.starProjection (sourceSetup F L) t))) = P) :
    conjugate A t = C := by
  let a := B.model (ChapterG.Section02.LinearThree.starProjection (sourceSetup F L) t)
  have hv : L ≤ normalizer (V : Set G) := ChapterG.Section02.LinearThree.normalizes_of_span _ B.span_eq
  have hconj : conjugate A t ≤ V := conjugate_le_of_normalizes hAV t (hv t.property)
  have hm (v : V) : (v : G) ∈ conjugate A t ↔ (v : G) ∈ C := by
    rw [conjugate,mem_map_equiv]
    simp only [MulAut.conj_symm_apply, inv_inv]
    let w : V := ⟨(t : G) * v * (t : G)⁻¹,(mem_normalizer_iff.mp (hv t.property) v).mp v.property⟩
    change (w : G) ∈ A ↔ _
    rw [hP w,hQ v]
    have hw := B.equivariant t v
    change (B.coordinates w).toAdd = a.val.mulVec (B.coordinates v).toAdd at hw
    rw [hw,← he]
    constructor
    · rintro ⟨z,hz,heq⟩
      exact (Matrix.SpecialLinearGroup.toLin' a).injective heq ▸ hz
    · intro hvQ
      exact ⟨_,hvQ,rfl⟩
  apply le_antisymm
  · intro v hvA
    exact (hm ⟨v,hconj hvA⟩).mp hvA
  · intro v hvC
    exact (hm ⟨v,hCV hvC⟩).mpr hvC

/-- The original point stabilizer in L is transitive on all the other points.
The transporter remains in L and in the literal H-conjugate. -/
theorem source_point_orbits (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∀ x ∈ L, conjugate (F.Vi 1) x = conjugate (F.Vi 1) g ∨
      ∃ t ∈ L, t ∈ conjugate F.H g ∧ conjugate (F.Vi 1) x = conjugate (F.Vi 1) t := by
  obtain ⟨l,_,_,_,⟨B⟩⟩ := source_almostSpecial d earlier hq chosen structural alternatives F hne g hg hgP hgH
  let D := sourceSetup F L
  let pg := conjugatePoint B.point (B.model (ChapterG.Section02.LinearThree.starProjection D ⟨g,hg⟩))
  have hpg : finrank (ZMod 2) pg = 1 := (conjugatePoint_finrank _ _).trans B.point_dimension
  have hAg : conjugate (F.Vi 1) g ≤ V := conjugate_le_of_normalizes (F.le_seed 1) g (chosen.normalizes hg)
  have hpgmem (v : V) : (v : G) ∈ conjugate (F.Vi 1) g ↔ (B.coordinates v).toAdd ∈ pg :=
    (B.model_conjugatePoint_mem ⟨g,hg⟩ v).symm
  have hneP : B.point ≠ pg := by
    intro he
    have hd : Disjoint B.point pg := B.model_points_disjoint
    rw [← he] at hd
    have hz : B.point = ⊥ := disjoint_self.mp hd
    have hc := B.point_dimension
    rw [hz,finrank_bot] at hc
    contradiction
  intro x hx
  by_cases heq : conjugate (F.Vi 1) x = conjugate (F.Vi 1) g
  · exact Or.inl heq
  apply Or.inr
  let px := conjugatePoint B.point (B.model (ChapterG.Section02.LinearThree.starProjection D ⟨x,hx⟩))
  have hpx : finrank (ZMod 2) px = 1 := (conjugatePoint_finrank _ _).trans B.point_dimension
  have hAx : conjugate (F.Vi 1) x ≤ V := conjugate_le_of_normalizes (F.le_seed 1) x (chosen.normalizes hx)
  have hpxmem (v : V) : (v : G) ∈ conjugate (F.Vi 1) x ↔ (B.coordinates v).toAdd ∈ px :=
    (B.model_conjugatePoint_mem ⟨x,hx⟩ v).symm
  have hneX : px ≠ pg := by
    intro he
    apply heq
    apply le_antisymm
    · intro v hv
      exact (hpgmem ⟨v,hAx hv⟩).mpr (he ▸ (hpxmem ⟨v,hAx hv⟩).mp hv)
    · intro v hv
      exact (hpxmem ⟨v,hAg hv⟩).mpr (he ▸ (hpgmem ⟨v,hAg hv⟩).mp hv)
  obtain ⟨a,haX,haG⟩ := Matrix.SpecialLinearGroup.FrameGeometry.exists_point_pair_map
    px pg B.point pg hpx hpg B.point_dimension hpg hneX hneP
  obtain ⟨t,ht⟩ := (ChapterG.Section02.LinearThree.starProjection_surjective D) (B.model.symm a)
  have hta : B.model (ChapterG.Section02.LinearThree.starProjection D t) = a := by
    rw [ht,B.model.apply_symm_apply]
  have hAt : conjugate (F.Vi 1) t = conjugate (F.Vi 1) x :=
    coordinate_conjugate F g l B (F.Vi 1) (conjugate (F.Vi 1) x) (F.le_seed 1) hAx
      B.point px B.point_mem hpxmem t (by rw [hta]; exact haX)
  have hGt : conjugate (conjugate (F.Vi 1) g) t = conjugate (F.Vi 1) g :=
    coordinate_conjugate F g l B _ _ hAg hAg pg pg hpgmem hpgmem t (by rw [hta]; exact haG)
  refine ⟨t,t.property,?_,hAt.symm⟩
  have hn := (conjugate_eq_iff (conjugate (F.Vi 1) g) t).mp hGt
  change (t : G) ∈ (normalizer (F.Vi 1 : Set G)).map (MulAut.conj g⁻¹).toMonoidHom
  rw [map_equiv_normalizer_eq]
  exact hn
/-- The original natural L-module has no nonidentity fixed point. -/
theorem source_seed_fixed_bot (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    V ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨l,_,_,_,⟨B⟩⟩ := source_almostSpecial d earlier hq chosen structural alternatives F hne g hg hgP hgH
  have hn : L ≤ normalizer (V ⊓ centralizer (L : Set G) : Set G) :=
    (le_centralizer_iff.mp (show V ⊓ centralizer (L : Set G) ≤ centralizer (L : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  rcases B.irreducible (V ⊓ centralizer (L : Set G)) inf_le_left hn with hb | he
  · exact hb
  · have he' : V ⊓ centralizer (L : Set G) = V := he
    have hc : V ≤ centralizer (L : Set G) := he'.ge.trans inf_le_right
    exact (hgH ((Subgroup.centralizer_le_normalizer (F.Vi 1 : Set G))
      ((le_centralizer_iff.mp hc).trans (centralizer_le (F.le_seed 1)) hg))).elim
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup
