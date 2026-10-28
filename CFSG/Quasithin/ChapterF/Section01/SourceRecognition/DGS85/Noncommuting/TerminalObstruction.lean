module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalActor

/-!
# The terminal module obstruction in the long-distance branch

The path argument excludes a linear quotient at the last odd vertex.
The final radius/core index argument forces a linear quotient there for
any faithfully marked Chapter 5 model on V_t/Z_t with vanishing O²-fixed
space. All path vertices, the escaping radius-one actor, quadraticity,
fixed-space generation and the strict index comparison are constructed.

The conclusion identifies the exact remaining earlier-source obligation:
construct that faithful radius section and prove its residual fixed-space
condition. This theorem does not assert the unconditional b=2 bound.
Source: DGS, *Groups and Graphs* (1985), (7.5), printed pp.129--131.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

theorem graph_epsilonTwo_terminal_obstruction
    (h : LocallyRankOneTriple P B)
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
    {v w u : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u)
    (hdu : (graph (family P)).dist u w + 1 = b (family P))
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat₀ : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v))
    (hnat₁ : HasNaturalCenter (L w) (Z (family P) w) (Q (family P) w))
    (hsyl : Stellmacher.IsSylowSubgroupIn
      (Z (family P) v ⊔ Q (family P) w) (stabilizer (family P) w))
    (hbranch : ∀ i, ∃ k, ((family P (!i)).subgroupOf (family P i)).index - 1 = 2^k) :
    b (family P) = 2 ∨ ∃ t y : Vertex (family P),
      ∃ hty : (graph (family P)).Adj t y,
      ∃ hN : ((Q (family P) t).subgroupOf (d t y hty).Pstar).Normal,
        let := hN
        ∀ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
        ∀ σ : Representation (ZMod 2)
          ((d t y hty).Pstar ⧸ (Q (family P) t).subgroupOf (d t y hty).Pstar) W,
        ∀ _ : BinaryConjugationSection (d t y hty).Pstar (V (family P) t 1) (Z (family P) t)
          (σ.comp (QuotientGroup.mk' ((Q (family P) t).subgroupOf (d t y hty).Pstar))),
        ∀ _ : BinaryRankOneModel
          ((d t y hty).Pstar ⧸ (Q (family P) t).subgroupOf (d t y hty).Pstar),
          ¬ (Function.Injective σ ∧ fixedSpace σ (pResidual 2
            ((d t y hty).Pstar ⧸ (Q (family P) t).subgroupOf (d t y hty).Pstar)) = ⊥) := by
  rcases graph_epsilonTwo_last_odd_not_linear h hB hS L hcov d hstar hodd hdich hob
    hc hne hvu hdu hepsilon hnat₀ hnat₁ hsyl hbranch with hb | ⟨hb,t,y,hwt,hty,hdt,hdy,hcore,hesc,hnot⟩
  · exact Or.inl hb
  right
  obtain ⟨u',a,x,hvu',hva,hu'a,hyx,hdu',hdx,ha⟩ :=
    graph_terminal_actor_configuration h hS hc hb hwt hty hdy hesc
  have heps := graph_epsilonTwo_at_neighbor h hvu hvu' hepsilon
  have hcoreEq : (Q (family P) t).subgroupOf (d t y hty).Pstar = pCore 2 (d t y hty).Pstar := by
    rw [show Q (family P) t = (d t y hty).Pstar.pCoreIn 2 from (d t y hty).same_core.symm]
    exact comap_map_eq_self_of_injective (d t y hty).Pstar.subtype_injective _
  have hN : ((Q (family P) t).subgroupOf (d t y hty).Pstar).Normal := by
    rw [hcoreEq]
    infer_instance
  refine ⟨t,y,hty,hN,?_⟩
  let := hN
  dsimp only
  intro W _ _ σ s M hf
  obtain ⟨k,_,_,_,e,_⟩ := graph_epsilonTwo_terminal_section_natural h hB hS L hcov d hstar
    hodd hdich hob hc hne hvu' hwt hva hu'a hdu' hdt heps hnat₀ hnat₁ hsyl
    (by omega) hty hyx hdx hcore σ s ha M hf.1 hf.2
  have he : Nonempty (((d t y hty).Pstar ⧸ pCore 2 (d t y hty).Pstar) ≃* SL(2,k)) := by
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hcoreEq.symm).trans e⟩
  rw [hstar] at he
  exact (hnot k inferInstance inferInstance inferInstance).1 he

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
