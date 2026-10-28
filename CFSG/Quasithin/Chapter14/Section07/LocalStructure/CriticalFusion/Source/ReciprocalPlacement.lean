module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.CriticalLength

/-!
# The original span lies in the reciprocal vertex

The critical radius places V in the ball kernel of radius b−1 about the
first H vertex. That kernel is H-invariant, so it contains the literal
H-span U. The tail of the recorded path has length b−1; hence U fixes its
terminal vertex. Finally the permitted H-rechoice normalizes U and gives
containment in the original reciprocal centralizer, with the same source
conjugator. No rank-selection or reciprocal-placement premise is needed.

Source: Aschbacher–Smith F.9.13 and Notation 14.7.1.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The literal reciprocal placement follows from the original critical path. -/
theorem Data.source_reciprocal_placement (d : Data T L V F W)
    (c : CriticalPath (L := L) F) : F.U ≤ conjugate F.H c.conjugator := by
  let K := GeometryGroup T L F
  let Ω := geometryFamily (L := L) F
  let B := ballKernel Ω (base Ω true) (c.b-1)
  have hV : V ≤ B.map K.subtype := by
    intro v hv
    have hvK : v ∈ K := ((le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)).trans le_sup_left)
      (d.natural.chosen.le_sylow hv)
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
    (mem_normalizer_iff.mp (d.conjugationSection.normalized c.rechoice.property) x).mp hx
  have ht := hterm _ hx'
  change x ∈ F.H.map (MulAut.conj c.conjugator⁻¹).toMonoidHom
  apply mem_map.mpr
  refine ⟨c.conjugator*x*c.conjugator⁻¹,?_,?_⟩
  · simpa only [CriticalPath.conjugator,mul_inv_rev,mul_assoc,Subgroup.coe_inv] using ht
  · simp [mul_assoc]
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
