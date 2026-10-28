module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LinearCenterEscape
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SourceCoreSelection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.RankOnePaths

/-!
# Constructing the escaping Chapter 11 four-walk

At a commuting critical edge, choose a neighboring alpha vertex and a
turn at alpha. Four-walk transitivity supplies the literal path supplement
used to select the linear alpha quotient. The nonquadratic seed theorem
then chooses an escaping orientation. Its five vertices form the actual
nonbacktracking walk g·c, g·beta, alpha, beta, c.

Thus no separate transporter, escape, or path-membership input is needed.
The rank-one catalogue and four-walk transitivity remain explicit here;
OriginalLinearSource discharges both from the original linear endpoint
markings and the earlier source 6.8 theorem.
Source: DGS, Groups and Graphs (1985), (11.4)--(11.6), pp.171--174.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem neighbor_other (h : LocallyRankOneTriple P B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (a b : Vertex (family P)) :
    ∃ c, (graph (family P)).Adj b c ∧ a ≠ c := by
  let := finite_endpoints h
  have hv := card_neighbors_of_indices (family P)
    (fun i => ((family P (!i)).subgroupOf (family P i)).index) (fun _ => rfl) b
  have hc : 1 < ((graph (family P)).neighborSet b).ncard := by
    rw [←Nat.card_coe_set_eq,hv]
    have := source_valence_ge_three h hS b.type
    omega
  obtain ⟨c,hc,hca⟩ := Set.exists_ne_of_one_lt_ncard hc a
  exact ⟨c,hc,Ne.symm hca⟩

private theorem turn_walk {a b c : Vertex (family P)}
    (hab : (graph (family P)).Adj a b) (hbc : (graph (family P)).Adj b c)
    (hac : a ≠ c) (g : G) (hga : g ∈ stabilizer (family P) a)
    (hgb : g • b ≠ b) :
    ∃ p : BasedWalk (graph (family P)) 4 (g • c),
      p.Nonbacktracking ∧ p.vertices = [g • c,g • b,a,b,c] := by
  have hb'a : (graph (family P)).Adj (g • b) a := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab.symm
    change (graph (family P)).Adj (g • b) (g • a) at hh
    rwa [show g • a = a from hga] at hh
  have hc'b' : (graph (family P)).Adj (g • c) (g • b) :=
    (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hbc.symm
  refine ⟨⟨⟨g • b,hc'b'⟩,⟨⟨a,hb'a⟩,⟨⟨b,hab⟩,⟨⟨c,hbc⟩,PUnit.unit⟩⟩⟩⟩,?_,rfl⟩
  change a ≠ g • c ∧ b ≠ g • b ∧ c ≠ a ∧ True
  exact ⟨fun he => hac ((MulAction.injective g) ((show g • a = a from hga).trans he)),
    Ne.symm hgb,Ne.symm hac,trivial⟩

/-- Four-walk transitivity constructs all the escaping-path inputs for
(11.6), including the alpha selection and the actual center transporter. -/
theorem source_exists_escaping_four_walk
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ht : ∀ v, RootPathTransitive (graph (family P)) G v 4) :
    ∃ c, (graph (family P)).Adj b c ∧ a ≠ c ∧
      ∃ g ∈ stabilizer (family P) a, g • b ≠ b ∧
        ¬ Z (family P) b ≤ Q (family P) (g • b) ∧
        ∃ p : BasedWalk (graph (family P)) 4 (g • c),
          p.Nonbacktracking ∧ p.vertices = [g • c,g • b,a,b,c] := by
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨c,hbc,hac⟩ := neighbor_other h hS a b
  obtain ⟨b',hab',hbb'⟩ := neighbor_other h hS b a
  obtain ⟨g,hga,hgb⟩ := locally_transitive (family P) hab hab'
  have hgb' : g • b ≠ b := by rw [hgb]; exact Ne.symm hbb'
  obtain ⟨p,hp,hpv⟩ := turn_walk hab hbc hac g hga hgb'
  obtain ⟨_,n,hn,hi⟩ := source_core_product_and_alpha_on_path h hB d hc hb hcomm
    hbc hac Ma Mb (ht (g • c)) p hp
    (by rw [hpv]; simp) (by rw [hpv]; simp) (by rw [hpv]; simp)
  obtain ⟨k,_,_,hk,⟨ea⟩⟩ := hi
  let : Fintype k := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  obtain ⟨t,hta,htb,hesc⟩ := source_linear_rankOne_center_escape h hB d hc hb hcomm
    hbc hac Ma Mb (ea.trans ep.symm) g hga hgb'
  exact ⟨c,hbc,hac,t,hta,htb,hesc,turn_walk hab hbc hac t hta htb⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
