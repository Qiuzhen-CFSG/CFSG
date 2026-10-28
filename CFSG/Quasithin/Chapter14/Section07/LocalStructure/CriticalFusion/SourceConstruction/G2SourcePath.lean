module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.CriticalLength
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.Section

/-!
# Critical-path placement before residual recognition

The ball kernel of radius b−1 at the first H vertex contains the entire
H-span U. The geodesic tail then puts U in the reciprocal point centralizer;
the allowed H-rechoice preserves this containment. Relative normality of
the conjugate span gives normalization of Uα. If Zα lies in V, the natural
seed transitivity and central-label distance give b = 3.

These arguments adapt Source/ReciprocalPlacement and Source/CriticalLength
to the original higher-rank hypothesis. They use no alternating quotient,
module recognition, or Data record. Existence and rank selection of the
critical path, and the later critical-pair symmetry, remain source obligations.

Source: Aschbacher–Smith, F.9.13–14 and 14.7.1, 14.7.3(4), printed
pp.322–323 and 1042–1043. Used by the G₂ branch on pp.1067–1069.
-/


public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The literal reciprocal placement follows from the original critical path. -/
theorem reciprocal_placement (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (c : CriticalPath (L := L) F) : F.U ≤ conjugate F.H c.conjugator := by
  let K := GeometryGroup T L F
  let Ω := geometryFamily (L := L) F
  let B := ballKernel Ω (base Ω true) (c.b-1)
  have hV : V ≤ B.map K.subtype := by
    intro v hv
    have hvK : v ∈ K := ((le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)).trans le_sup_left)
      (h.chosen.le_sylow hv)
    refine ⟨⟨v,hvK⟩,?_,rfl⟩
    have h := (c.radius c.b).mpr le_rfl (show (⟨v,hvK⟩ : K) ∈ V.subgroupOf K from hv)
    have hn := ballKernel_succ_le Ω
      (show (graph Ω).Adj (base Ω false) (base Ω true) from
        ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base Ω false true⟩) (c.b-1)
    apply hn
    simpa only [Nat.sub_add_cancel (by have := c.three_le; omega : 1 ≤ c.b)] using h
  have hH : F.H ≤ normalizer (B.map K.subtype : Set G) := by
    intro h hh
    have hhK : h ∈ K := (le_sup_right : F.H ≤ K) hh
    have hn : (⟨h,hhK⟩ : K) ∈ normalizer (B : Set K) := by
      apply stabilizer_le_normalizer_ballKernel Ω (base Ω true) (c.b-1)
      change (⟨h,hhK⟩ : K) ∈ stabilizer Ω (base Ω true)
      simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] using
        (show (⟨h,hhK⟩ : K) ∈ Ω true from hh)
    exact le_normalizer_map K.subtype ⟨⟨h,hhK⟩,hn,rfl⟩
  have hU : F.U ≤ B.map K.subtype := conjugateSpanBy_le hV hH
  have hterm : ∀ x ∈ F.U, c.gammaConjugator*x*c.gammaConjugator⁻¹ ∈ F.H := by
    intro x hx
    obtain ⟨x',hx',rfl⟩ := hU hx
    have he := hx' (c.gammaConjugator⁻¹ • base Ω true) (by
      change (graph Ω).edist (base Ω true) (c.gammaConjugator⁻¹ • base Ω true) ≤ ((c.b-1 : ℕ):ℕ∞)
      have hd := (c.path.drop 1).edist_le
      simpa only [SimpleGraph.Walk.drop_length,c.length,c.first] using hd)
    have hf : c.gammaConjugator*x'*c.gammaConjugator⁻¹ ∈ stabilizer Ω (base Ω true) := by
      change (c.gammaConjugator*x'*c.gammaConjugator⁻¹) • base Ω true = base Ω true
      rw [mul_smul,mul_smul,he,smul_inv_smul]
    have hh : c.gammaConjugator*x'*c.gammaConjugator⁻¹ ∈ Ω true := by
      simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] using hf
    exact hh
  intro x hx
  have hx' : (c.rechoice:G)*x*(c.rechoice:G)⁻¹ ∈ F.U :=
    (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy V F.H c.rechoice.property) x).mp hx
  have ht := hterm _ hx'
  change x ∈ F.H.map (MulAut.conj c.conjugator⁻¹).toMonoidHom
  apply mem_map.mpr
  refine ⟨c.conjugator*x*c.conjugator⁻¹,?_,?_⟩
  · simpa only [CriticalPath.conjugator,mul_inv_rev,mul_assoc,Subgroup.coe_inv] using ht
  · simp [mul_assoc]
/-- The original U normalizes the reciprocal U, before any G₂ or alternating
module identification. The conjugation direction is the one in CriticalPath. -/
theorem normalizes_partner
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) :
    F.U ≤ normalizer (path.Uα : Set G) := by
  have hn : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy V F.H
  have hm := (map_mono (f := (MulAut.conj path.conjugator⁻¹).toMonoidHom) hn).trans
    (le_normalizer_map (MulAut.conj path.conjugator⁻¹).toMonoidHom)
  exact (reciprocal_placement h path).trans hm

/-- The early critical-length consequence, with the source's actual point
chosen from the flag instead of from the later 14.7.63 datum. -/
theorem critical_length_three
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hc : path.Zα ≤ V) : path.b = 3 := by
  obtain ⟨z,hz,he⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hcenter := F.H_eq_centralizer (by decide) z he
  have hzV : z ∈ V := F.le_seed 1 (he.symm ▸ mem_zpowers z)
  have hm : (path.rechoice:G)⁻¹*((path.gammaConjugator:G)⁻¹*z*(path.gammaConjugator:G))*(path.rechoice:G) ∈ V := by
    apply hc
    change _ ∈ conjugate (F.Vi 1) path.conjugator
    unfold conjugate
    refine ⟨z,he.symm ▸ mem_zpowers z,?_⟩
    simp [CriticalPath.conjugator,mul_assoc]
  have hbound := ChapterF.Section09.central_label_distance
    (L ⊔ (T:Subgroup G)) F.H V z path.gammaConjugator⁻¹
    (inclusion le_sup_right path.rechoice) hz
    (by rw [hcenter])
    (fun v hv hv1 => by
      obtain ⟨l,hl,he⟩ := h.vector_transitive hzV hv hz hv1
      exact ⟨l,mem_sup_left hl,he⟩)
    path.rechoice.property (by simpa using hm)
  change (graph (geometryFamily (L:=L) F)).dist
    (base (geometryFamily (L:=L) F) false)
    (path.gammaConjugator⁻¹ • base (geometryFamily (L:=L) F) true) ≤ 3 at hbound
  rw [← path.geodesic,path.length] at hbound
  exact le_antisymm hbound path.three_le

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
