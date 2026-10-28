module
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion.Generation

/-!+# Conjugate generation for the actual component extension

An element of the edge two-group outside the vertex two-core has relative
normal closure generating the vertex group with that edge group. The proof
uses the quasisimple component in the actual quotient by O₂, so it also
applies to odd central covers. Edge transitivity then supplies the identical
statement at every oriented edge of the free holomorph.

This proves MS93 (2.3)(b) from the original component extension, as used in
(3.8), printed pp.857 and 877. No natural-module model is required.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.MSCentralOrbit
open BinaryMS.MS93 BinaryMS.MS93.NormalizerTransfer BinaryMS.MS93.CriticalCriterion
variable {H : Type*} [Group H] [Finite H]

/-- MS93 (2.3)(b) for a quasisimple component and a two-group supplement. -/
theorem component_generation (K R : Subgroup H) [K.Normal]
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hp : IsPGroup 2 R) (hgen : K ⊔ R = ⊤) (hQR : pCore 2 H ≤ R) :
    CriticalCriterion.Generation R := by
  apply Generation.of_edge R (alpha R) (beta R) rfl (base_adjacent R)
  intro x hx hout
  let N := conjugatesIn (zpowers x) (Mbar R)
  have hxR : x ∈ R.map (embedM R) := by simpa only [Q_beta] using hx
  have hNM : N ≤ Mbar R := conjugatesIn_le _ _
    ((zpowers_le.mpr hxR).trans (map_le_range _ _))
  have hxN : x ∈ N := by
    apply le_iSup (fun g : Mbar R => rightConjugate (zpowers x) g) (1 : Mbar R)
    exact ⟨x,mem_zpowers x,by simp⟩
  let A : Subgroup H := N.comap (embedM R)
  let : A.Normal := by
    constructor
    intro y hy g
    show embedM R (g*y*g⁻¹) ∈ N
    simpa only [map_mul,map_inv] using
      le_normalizer_iff.mp (conjugatesIn_normalized (zpowers x) (Mbar R))
        (embedM R g) ⟨g,rfl⟩ (embedM R y) hy
  obtain ⟨y,hy,hyx⟩ := hxR
  have hyA : y ∈ A := by change embedM R y ∈ N; rwa [hyx]
  have hyQ : y ∉ pCore 2 H := by
    intro hy'
    apply hout
    rw [Q_alpha R hp hQR,←hyx]
    exact mem_map_of_mem _ hy'
  have htop := normal_sup_eq_top_of_two_escape K A R hK hp hgen hQR y hy hyA hyQ
  have hm := congrArg (Subgroup.map (embedM R)) htop
  rw [show stabilizer R (alpha R) = Mbar R from stabilizer_m_base R]
  change N ⊔ Q R (beta R) = Mbar R
  rw [Q_beta]
  change N ⊔ R.map (embedM R) = (embedM R).range
  simpa only [Subgroup.map_sup,A,map_comap_eq,
    inf_eq_right.mpr (show N ≤ (embedM R).range from hNM),
    ←MonoidHom.range_eq_map] using hm

end CFSG.Quasithin.ChapterC.MSCentralOrbit
