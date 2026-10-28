module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalSmallExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalSmallModels

/-!
# The epsilon-two critical distance is two

The earlier geometry gives b=2 or b≥6. In the latter branch, the last
nontransitive path produces the literal terminal V_t/Z_t section, with
fixed generation, faithful Sylow action and a nontrivial quadratic actor
whose fixed-space index is at most its order. The last-odd argument
excludes linear quotients. The model bounds exclude Suzuki and larger
unitary quotients, and the field-two unitary argument closes the remaining
cases. Thus no long epsilon-two branch survives.

The hypotheses are the earlier local source conclusions and the two
natural centers from (7.1); no terminal representation premise remains.
`TerminalBoundSource` applies this to the original reduced F1.11 graph.
Source: DGS, *Groups and Graphs* (1985), (7.5), pp.129--131.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- DGS (7.5), conditional only on the stated earlier local and endpoint inputs. -/
theorem graph_epsilonTwo_distance_two
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
    (hbranch : ∀ i, ∃ k, ((family P (!i)).subgroupOf (family P i)).index - 1 = 2^k)
    : b (family P) = 2 := by
  rcases graph_epsilonTwo_distance_gap h hB hS L hcov d hstar hodd hdich hob
    hc hne hvu hdu hepsilon hnat₀ hnat₁ with hb | hb
  · exact hb
  obtain ⟨t,y,hty,W,hadd,hmodule,σ,_,_,hfin,hgen,hfaith,hactor,hsmall⟩ :=
    graph_epsilonTwo_terminal_small_unitary h hB hS L hcov d hstar hodd hdich hob
      hc hne hvu hdu hepsilon hnat₀ hnat₁ hsyl hbranch (by omega)
  let := hadd
  let := hmodule
  let := hfin
  let := finite_endpoints h
  let c := d t y hty
  let : Finite c.Pstar := Finite.of_injective (inclusion c.Pstar_le) (inclusion_injective _)
  let := graph_local_core_normal t c
  obtain ⟨a,_,_,hAT,hAc,hq,hbound⟩ := hactor
  exact (small_unitary_fixed_generated_index_obstruction hsmall σ _ _
    hAT hAc hq hgen hfaith hbound).elim

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
