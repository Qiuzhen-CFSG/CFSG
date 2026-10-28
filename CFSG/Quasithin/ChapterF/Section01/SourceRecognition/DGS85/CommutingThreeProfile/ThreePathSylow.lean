module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SourceParameter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RadiusThree
public import Theory.GroupAction.SylowNormalizerOrbit
import all Theory.GroupAction.SylowNormalizerOrbit

/-!
# The actual Sylow image of a short three-path

Every two-subgroup fixing a nonbacktracking three-path lies in both interior
vertex cores. Their intersection is normal in the full path fixer and is
therefore its unique Sylow two-subgroup. If the earlier source parameter
s is greater than three, the path fixer is transitive on forward neighbors.
Two-power branching and the odd Sylow index transfer this transitivity to
the intersection itself. Comparing its action with the incoming core then
identifies their images modulo the endpoint core.

The graph need not be a tree. All local model and earlier source inputs are
explicit; no three-path image or endpoint orbit is assumed. The unitary
selection consumer uses this to bound its actual centralizer image. The
implementation import deliberately reuses the same-package coprime-index
orbit proof without changing that module's public boundary.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(3.4)(c), (12.4)(b), and the Sylow-placement step of (12.5), printed p.182.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open CommutingNontrivial Theory.GroupAction.CubicTree
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The full three-path fixer has the literal interior-core intersection as its Sylow. -/
theorem three_path_core_sylow
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    (models : ∀ v, IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    {a : Vertex (family P)} (p : BasedWalk (graph (family P)) 3 a)
    (hp : p.Nonbacktracking) (T : Sylow 2 (pathStabilizer (family P) p)) :
    (T : Subgroup (pathStabilizer (family P) p)).map (pathStabilizer (family P) p).subtype =
      Q (family P) p.1.val ⊓ Q (family P) p.2.1.val := by
  let F := family P
  rcases p with ⟨⟨v,hav⟩,⟨⟨w,hvw⟩,⟨⟨z,hwz⟩,u⟩⟩⟩
  let H := pathStabilizer F (n := 3) (v := a) (⟨⟨v,hav⟩,⟨⟨w,hvw⟩,⟨⟨z,hwz⟩,u⟩⟩⟩ : BasedWalk (graph F) 3 a)
  let I := Q F v ⊓ Q F w
  let D := (T : Subgroup H).map H.subtype
  have hfix (x) (hx : x ∈ [a,v,w,z]) : D ≤ stabilizer F x :=
    fun t ht => (map_subtype_le _ ht) x hx
  have hDI : D ≤ I := by
    apply le_inf
    · exact source_two_neighbor_pGroup_le_core h hB d hav.symm hvw hp.1.symm
        (models v) D (T.isPGroup'.map _) (hfix v (by simp))
        (hfix a (by simp)) (hfix w (by simp))
    · exact source_two_neighbor_pGroup_le_core h hB d hvw.symm hwz hp.2.1.symm
        (models w) D (T.isPGroup'.map _) (hfix w (by simp))
        (hfix v (by simp)) (hfix z (by simp))
  have hIH : I ≤ H := by
    intro g hg x hx
    change x ∈ [a,v,w,z] at hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with hx | hx | hx | hx <;> subst x
    · exact (source_Z_Q_U h v).2 hg.1 a ((mem_ball_one F v a).mpr (.inl hav.symm))
    · exact Q_le_stabilizer F v hg.1
    · exact Q_le_stabilizer F w hg.2
    · exact (source_Z_Q_U h w).2 hg.2 z ((mem_ball_one F w z).mpr (.inl hwz))
  have hn : H ≤ normalizer (I : Set G) := by
    apply (le_inf _ _).trans inf_normalizer_le_normalizer_inf
    · exact (show H ≤ stabilizer F v from fun g hg => hg v (by change v ∈ [a,v,w,z]; simp)).trans
        (stabilizer_normalizes_Q F v)
    · exact (show H ≤ stabilizer F w from fun g hg => hg w (by change w ∈ [a,v,w,z]; simp)).trans
        (stabilizer_normalizes_Q F w)
  exact le_antisymm hDI ((le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 (stabilizer F v)).to_inf_left hIH hn).trans (pCoreIn_le_sylow _ T))

/-- For a three-path shorter than s, its interior cores are transitive on forward neighbors. -/
theorem three_path_core_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    (models : ∀ v, IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hs : 3 < sourceS (P := P))
    {a : Vertex (family P)} (p : BasedWalk (graph (family P)) 3 a)
    (hp : p.Nonbacktracking) :
    ∀ z w, Theory.GroupAction.CubicTree.Forward p z → Theory.GroupAction.CubicTree.Forward p w →
      ∃ g ∈ Q (family P) p.1.val ⊓ Q (family P) p.2.1.val, g • z = w := by
  classical
  let F := family P
  let H := pathStabilizer F p
  let Y := {z : (graph F).neighborSet p.endpoint // (z : Vertex F) ≠ p.penultimate}
  let : ∀ i, Finite (F i) := finite_endpoints h
  let : Finite H := Finite.of_injective (inclusion (pathStabilizer_le F p)) (inclusion_injective _)
  let : Finite ((graph F).neighborSet p.endpoint) := (graph_locally_finite h p.endpoint).2
  have hfix (g : H) : (g : G) • p.endpoint = p.endpoint ∧
      (g : G) • p.penultimate = p.penultimate := by
    rcases p with ⟨⟨v,hv⟩,⟨⟨w,hw⟩,⟨⟨z,hz⟩,u⟩⟩⟩
    exact ⟨g.property z (by change z ∈ [a,v,w,z]; simp),
      g.property w (by change w ∈ [a,v,w,z]; simp)⟩
  let : MulAction H Y := {
    smul := fun g z => ⟨⟨(g : G) • (z.val : Vertex F), by
      have hh := (Subgroup.CosetGeometry.translationGraphIso F (g : G)).map_adj_iff.mpr z.val.property
      change (graph F).Adj ((g : G) • p.endpoint) ((g : G) • (z.val : Vertex F)) at hh
      rwa [(hfix g).1] at hh⟩, fun he => z.property
        ((MulAction.injective (g : G)) (he.trans (hfix g).2.symm))⟩
    one_smul := fun z => Subtype.ext (Subtype.ext (_root_.one_smul G _))
    mul_smul := fun g k z => Subtype.ext (Subtype.ext (mul_smul (g : G) (k : G) _)) }
  have hr := (sourceS_short_regular h hS p hs hp).2
  let : MulAction.IsPretransitive H Y := ⟨by
    intro z w
    obtain ⟨g,hg,he⟩ := hr z.val w.val ⟨z.val.property,z.property⟩ ⟨w.val.property,w.property⟩
    exact ⟨⟨g,hg⟩,Subtype.ext (Subtype.ext he)⟩⟩
  have hc : Nat.card Y = Nat.card ((graph F).neighborSet p.endpoint) - 1 := by
    let : Fintype ((graph F).neighborSet p.endpoint) := Fintype.ofFinite _
    have he : Nat.card {z : (graph F).neighborSet p.endpoint // (z : Vertex F) = p.penultimate} = 1 := by
      let : Unique {z : (graph F).neighborSet p.endpoint // (z : Vertex F) = p.penultimate} :=
        ⟨⟨⟨⟨p.penultimate,p.adj_penultimate_endpoint.symm⟩,rfl⟩⟩,
          fun z => Subtype.ext (Subtype.ext z.property)⟩
      exact Nat.card_unique
    rw [←he]
    simp only [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_compl _
  have hpow : ∃ n, Nat.card Y = 2^n := by
    rw [hc,card_neighbors_of_indices F
      (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_rankOne_branching h p.endpoint.type
  let T : Sylow 2 H := Classical.choice inferInstance
  have hcop : Nat.Coprime (Nat.card Y) (T : Subgroup H).index := by
    obtain ⟨n,hn⟩ := hpow
    rw [hn]
    exact (Nat.prime_two.coprime_pow_of_not_dvd T.not_dvd_index).symm
  let : MulAction.IsPretransitive T Y := Theory.GroupAction.coprime_transitive (T : Subgroup H) hcop
  intro z w hz hw
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq T (show Y from ⟨⟨z,hz.1⟩,hz.2⟩)
    (show Y from ⟨⟨w,hw.1⟩,hw.2⟩)
  refine ⟨g.val.val,?_,congrArg (fun z : Y => (z.val : Vertex F)) hg⟩
  rw [←three_path_core_sylow h hB d models p hp T]
  exact mem_map_of_mem H.subtype g.property


/-- The interior-core intersection has the full incoming-core image at the
terminal vertex of every three-path shorter than the source parameter. -/
theorem three_path_core_supplement
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    (models : ∀ v, IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hs : 3 < sourceS (P := P))
    {a : Vertex (family P)} (p : BasedWalk (graph (family P)) 3 a)
    (hp : p.Nonbacktracking) :
    (Q (family P) p.1.val ⊓ Q (family P) p.2.1.val) ⊔ Q (family P) p.endpoint =
      Q (family P) p.2.1.val ⊔ Q (family P) p.endpoint := by
  classical
  let F := family P
  let : ∀ i, Finite (F i) := finite_endpoints h
  have htrans := three_path_core_transitive h hB hS d models hs p hp
  rcases p with ⟨⟨v,hav⟩,⟨⟨w,hvw⟩,⟨⟨y,hwy⟩,u⟩⟩⟩
  change (Q F v ⊓ Q F w) ⊔ Q F y = Q F w ⊔ Q F y
  have hval : 1 < ((graph F).neighborSet y).ncard := by
    change 1 < Nat.card ((graph F).neighborSet y)
    rw [card_neighbors_of_indices F
      (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact lt_of_lt_of_le (by decide) (source_valence_ge_three h hS y.type)
  obtain ⟨z,hz,hzn⟩ := Set.exists_ne_of_one_lt_ncard hval w
  have hQwy : Q F w ≤ stabilizer F y :=
    (source_Z_Q_U h w).2.trans ((ballKernel_one_le_edge F hwy).trans inf_le_right)
  apply le_antisymm (sup_le_sup inf_le_right le_rfl)
  apply sup_le _ le_sup_right
  intro t ht
  have hty : t • y = y := hQwy ht
  have htw : t • w = w := Q_le_stabilizer F w ht
  have htz : (graph F).Adj y (t • z) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F t).map_adj_iff.mpr hz
    change (graph F).Adj (t • y) (t • z) at hh
    rwa [hty] at hh
  have htn : t • z ≠ w := fun he => hzn ((MulAction.injective t) (he.trans htw.symm))
  obtain ⟨g,hg,he⟩ := htrans z (t • z) ⟨hz,hzn⟩ ⟨htz,htn⟩
  let c := t⁻¹*g
  have hcw : c ∈ Q F w := (Q F w).mul_mem ((Q F w).inv_mem ht) hg.2
  have hcz : c • z = z := by simp only [c,mul_smul,he,inv_smul_smul]
  have hA : zpowers c ≤ Q F w := zpowers_le.mpr hcw
  have hcy : c ∈ Q F y := by
    apply source_two_neighbor_pGroup_le_core h hB d hwy.symm hz hzn.symm (models y)
      (zpowers c) ((isPGroup_pCoreIn 2 (stabilizer F w)).to_le hA)
      (hA.trans hQwy) (hA.trans (Q_le_stabilizer F w)) (zpowers_le.mpr hcz)
    exact mem_zpowers c
  have htEq : t = g*c⁻¹ := by dsimp [c]; group
  rw [htEq]
  exact ((Q F v ⊓ Q F w) ⊔ Q F y).mul_mem (mem_sup_left hg)
    (mem_sup_right ((Q F y).inv_mem hcy))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
