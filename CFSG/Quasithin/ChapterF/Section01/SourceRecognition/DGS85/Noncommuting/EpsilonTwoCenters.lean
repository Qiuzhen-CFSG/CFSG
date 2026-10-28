module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.CenterCommutators
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.RadiusOneSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.RecognitionSource

/-!
# The two epsilon-two critical center identities

The exact epsilon-two choice gives conjugate critical endpoints. Transporting
the central-center alternative to the last neighbor makes its edge seed the
same source center. Applying the natural edge calculation in both orientations
proves Z_beta = R = Z_(alpha'-1), together with both radius-one commutator
identities. All quotients and conjugation coordinates retain their markings.

The reduced F1.11 application first invokes the proved reciprocal bounds and
corrected recognition theorem on the actual two center sections. It then
constructs their natural-coordinate data and proves the first-edge identities;
natural coordinates are not a premise of that application. Earlier local model,
faithful section, residual-fixed-space and adjacent-core obstruction inputs
remain explicit. The long-distance exclusion is a separate remaining argument.

Source: DGS, *Groups and Graphs* (1985), (7.4)(c--d), p.128.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
universe u
variable {G : Type u} [Group G]

/-- Both critical path ends have the same literal center and radius-one commutator. -/
theorem graph_epsilonTwo_critical_centers
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph (family P)).Adj x y →
      LocalRankOneData (stabilizer (family P) x)
        (stabilizer (family P) x ⊓ stabilizer (family P) y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer (family P) x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph (family P)).Adj x y → ¬ stabilizer (family P) y ≤ normalizer
      ((Q (family P) x ⊓ Q (family P) y : Subgroup G) : Set G))
    {v w u t : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u) (hwt : (graph (family P)).Adj w t)
    (hdu : (graph (family P)).dist u w + 1 = b (family P))
    (hdt : (graph (family P)).dist v t + 1 = b (family P))
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat₀ : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v))
    (hnat₁ : HasNaturalCenter (L w) (Z (family P) w) (Q (family P) w)) :
    ⁅Z (family P) v,Z (family P) w⁆ = Z (family P) u ∧
      ⁅Z (family P) v,Z (family P) w⁆ = Z (family P) t ∧
      ⁅V (family P) u 1,Q (family P) u⁆ = Z (family P) u ∧
      ⁅V (family P) t 1,Q (family P) t⁆ = Z (family P) t := by
  have hf := graph_epsilonTwo_forward_identities h hB hS hc hvu hdu hne
    (d v u hvu) (d u v hvu.symm)
    (by rw [hstar]; exact hodd v) (by rw [hstar]; exact hodd u)
    (by rw [hstar]; exact hdich u) hepsilon (by rw [hstar]; exact hnat₀) (hob v u hvu)
  obtain ⟨g,hg⟩ := (graph_epsilonTwo_even_of_localData h hB L hcov d hstar hodd hdich
    hc hne hvu hepsilon).1
  have htype : v.type = w.type := (same_orbit_iff (family P) v w).mp ⟨g,hg⟩
  have hut : u.type = t.type := by
    have hu := hvu.1
    have ht := hwt.1
    cases hv : v.type <;> cases hw : w.type <;> cases hu' : u.type <;> cases ht' : t.type <;> simp_all
  have hcentral : Z (family P) u = Stellmacher.omegaOneCenterAmbient (L u) := by
    apply (hdich u).resolve_left
    intro hs
    exact graph_seed_ne_of_centralizerSylow h hB hvu.symm (d u v hvu.symm)
      (by rw [hstar]; exact hodd u) (by rw [hstar]; exact hs)
      (by simpa only [inf_comm] using hepsilon)
  have hcentralt := (graph_center_equality_of_type h L hcov hut).mp hcentral
  have hepsilont : Z (family P) t = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) w ⊓ stabilizer (family P) t).pCoreIn 2) := by
    by_contra hn
    apply graph_noncentral_of_edgeSeed_ne h hB hwt.symm (d t w hwt.symm)
      (by rw [hstar]; exact hodd t) (by simpa only [inf_comm] using hn)
    rw [hstar]
    exact hcentralt
  have hr := graph_epsilonTwo_forward_identities h hB hS (graph_criticalPair_reverse h hS hc hne)
    hwt (by simpa only [SimpleGraph.dist_comm] using hdt) (by rwa [commutator_comm])
    (d w t hwt) (d t w hwt.symm)
    (by rw [hstar]; exact hodd w) (by rw [hstar]; exact hodd t)
    (by rw [hstar]; exact hdich t) hepsilont (by rw [hstar]; exact hnat₁) (hob w t hwt)
  exact ⟨hf.1,(commutator_comm _ _).trans hr.1,hf.2,hr.2⟩

/-- Recognition on the same two sections produces the literal center coordinates. -/
theorem EqualFieldNaturalSections.hasNaturalCenters
    {L₀ L₁ Z₀ Z₁ Q₀ Q₁ : Subgroup G}
    [(Q₀.subgroupOf L₀).Normal] [(Q₁.subgroupOf L₁).Normal]
    {W₀ W₁ : Type*}
    [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
    {σ₀ : Representation (ZMod 2) (L₀ ⧸ Q₀.subgroupOf L₀) W₀}
    {σ₁ : Representation (ZMod 2) (L₁ ⧸ Q₁.subgroupOf L₁) W₁}
    (hn : EqualFieldNaturalSections σ₀ σ₁)
    (d₀ : BinaryConjugationSection L₀ Z₀ (Stellmacher.omegaOneCenterAmbient L₀)
      (σ₀.comp (QuotientGroup.mk' (Q₀.subgroupOf L₀))))
    (d₁ : BinaryConjugationSection L₁ Z₁ (Stellmacher.omegaOneCenterAmbient L₁)
      (σ₁.comp (QuotientGroup.mk' (Q₁.subgroupOf L₁)))) :
    HasNaturalCenter L₀ Z₀ Q₀ ∧ HasNaturalCenter L₁ Z₁ Q₁ := by
  obtain ⟨F₀,i₀,f₀,c₀,F₁,i₁,f₁,c₁,e₀,e₁,E₀,E₁,he₀,he₁,_⟩ := hn
  let : Algebra (ZMod 2) F₀ := ZMod.algebra F₀ 2
  let : Algebra (ZMod 2) F₁ := ZMod.algebra F₁ 2
  exact ⟨hasNaturalCenter_of_marked _ _ _ σ₀ d₀ e₀ E₀ he₀,
    hasNaturalCenter_of_marked _ _ _ σ₁ d₁ e₁ E₁ he₁⟩

namespace Reduction
open DGS85.Reduction Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => reducedFamily L₀ S₀

/-- Actual reduced F1.11 application: both corrected bounds and recognition are
applied before the epsilon-two center identities. No natural coordinates are assumed. -/
theorem reduced_epsilonTwo_forward_from_recognition (h : HypothesisF11 L₀ S₀)
    {v w u : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (E₁ : Subgroup (G₀ L₀ S₀))
    (c₀ : LocalRankOneData (stabilizer F v) (stabilizer F v ⊓ stabilizer F u))
    (c₁ : LocalRankOneData (stabilizer F w) E₁)
    (ho₀ : ¬ 2 ∣ c₀.Pstar.relIndex (stabilizer F v))
    (ho₁ : ¬ 2 ∣ c₁.Pstar.relIndex (stabilizer F w))
    [((Q F v).subgroupOf c₀.Pstar).Normal]
    [((Q F w).subgroupOf c₁.Pstar).Normal]
    {W₀ W₁ : Type*}
    [AddCommGroup W₀] [Module (ZMod 2) W₀]
    [AddCommGroup W₁] [Module (ZMod 2) W₁]
    (σ₀ : Representation (ZMod 2) (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar) W₀)
    (σ₁ : Representation (ZMod 2) (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar) W₁)
    (d₀ : BinaryConjugationSection c₀.Pstar (Z F v) (Stellmacher.omegaOneCenterAmbient c₀.Pstar)
      (σ₀.comp (QuotientGroup.mk' ((Q F v).subgroupOf c₀.Pstar))))
    (d₁ : BinaryConjugationSection c₁.Pstar (Z F w) (Stellmacher.omegaOneCenterAmbient c₁.Pstar)
      (σ₁.comp (QuotientGroup.mk' ((Q F w).subgroupOf c₁.Pstar))))
    (M₀ : BinaryRankOneModel (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar))
    (M₁ : BinaryRankOneModel (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar))
    (hf₀ : Function.Injective σ₀) (hf₁ : Function.Injective σ₁)
    (hr₀ : fixedSpace σ₀ (pResidual 2 (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar)) = ⊥)
    (hr₁ : fixedSpace σ₁ (pResidual 2 (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar)) = ⊥)
    (he : (graph F).Adj v u) (hd : (graph F).dist u w + 1 = b F)
    (cβ : LocalRankOneData (stabilizer F u) (stabilizer F u ⊓ stabilizer F v))
    (hoβ : ¬ 2 ∣ cβ.Pstar.relIndex (stabilizer F u))
    (hdich : Stellmacher.IsSylowSubgroupIn (Q F u)
      (cβ.Pstar ⊓ centralizer (Z F u : Set (G₀ L₀ S₀))) ∨
      Z F u = Stellmacher.omegaOneCenterAmbient cβ.Pstar)
    (hepsilon : Z F u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer F v ⊓ stabilizer F u).pCoreIn 2))
    (hob : ¬ stabilizer F u ≤ normalizer ((Q F v ⊓ Q F u : Subgroup (G₀ L₀ S₀)) : Set (G₀ L₀ S₀))) :
    ⁅Z F v,Z F w⁆ = Z F u ∧ ⁅V F u 1,Q F u⁆ = Z F u := by
  have hr := reduced_sections_recognized h hc hne (stabilizer F v ⊓ stabilizer F u) E₁
    c₀ c₁ ho₀ ho₁ σ₀ σ₁ d₀ d₁ M₀ M₁ hf₀ hf₁ hr₀ hr₁
  have hn := hr.1.hasNaturalCenters d₀ d₁
  exact graph_epsilonTwo_forward_identities (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_kernel_sylow h) hc he hd hne c₀ cβ ho₀ hoβ hdich hepsilon hn.1 hob

end Reduction

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
