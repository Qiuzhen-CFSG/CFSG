module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RadiusThree

/-!
# The actual radius-three configuration and its core Sylow

The original 6.5 obstruction makes the neighboring core escape the preceding
vertex core. Applying the normalizer and two-neighbor arguments constructs
Q_(alpha'-1) as a Sylow of X = <V_beta^(3), Q_(alpha'-1)>. If the radius-three
span escapes Q_(alpha'-2), Sylow conjugacy inside this same X puts
Q_(alpha'-1) intersect Q_(alpha'-2) in Q_(alpha'-3).

The reduced F1.11 application retains the original centers, cores, full
Borel, local actors and arbitrary ordered critical pair. This proves the
stated intermediate configuration in DGS 8.4(1), printed p.137; transport
to the moving neighbor and the rest of 8.4--8.7 still require proof.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The radius-three configuration used in the remaining part of 8.4(1).
The original 6.5 intersection obstruction supplies the escaping neighboring
core; all Sylow membership and core transport inside X are proved. -/
theorem source_radius_three_configuration (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 3 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (hne : ⁅V (family P) beta 1 ⊓ Q (family P) a', V (family P) a' 1⁆ ≠ ⊥) :
    let F := family P
    let W := V F beta 3
    let H := ⁅V F beta 1 ⊓ Q F a', V F a' 1⁆
    5 ≤ b F ∧ W ≤ Q F beta ∧ IsPGroup 2 W ∧ W ≤ centralizer (H : Set G) ∧
      ∃ x₁ x₂ x₃ : Vertex F,
        (graph F).Adj a' x₁ ∧ (graph F).Adj x₁ x₂ ∧ (graph F).Adj x₂ x₃ ∧
        (graph F).dist beta x₁ + 1 = (graph F).dist beta a' ∧
        (graph F).dist beta x₂ + 1 = (graph F).dist beta x₁ ∧
        (graph F).dist beta x₃ + 1 = (graph F).dist beta x₂ ∧
        W ≤ d.localGroup x₂ ∧ W ≤ Q F x₃ ∧ W ⊓ d.localGroup x₁ ≤ Q F x₁ ∧
        (W ≤ Q F x₂ → W ≤ Q F x₁) ∧
        (let X := W ⊔ Q F x₁
         X ≤ d.localGroup x₂ ∧ X ≤ centralizer (H : Set G) ∧
           (∃ S : Sylow 2 X, (S : Subgroup X).map X.subtype = Q F x₁) ∧
           (¬ W ≤ Q F x₂ → Q F x₁ ⊓ Q F x₂ ≤ Q F x₃)) := by
  dsimp only
  let := finite_endpoints h
  let F := family P
  let W := V F beta 3
  let H := ⁅V F beta 1 ⊓ Q F a', V F a' 1⁆
  obtain ⟨hb5, hWQ, hp, hWH, x₁, x₂, x₃, h₁, h₂, h₃, hd₁, hd₂, hd₃,
      hWL, hWQ₃, hinter, hinside⟩ := source_radius_three_path_control h hB d models hc hab hd hb hcomm hne
  let X := W ⊔ Q F x₁
  obtain ⟨hn, hHZ, _⟩ := source_critical_commutator_structure h hB d hc hab hd (by omega) hcomm models
  have hHV : H ≤ V F a' 1 := le_normalizer_iff_commutator_le_right.mp
    ((inf_le_right.trans (Q_le_stabilizer F a')).trans (stabilizer_normalizes_V F a' 1))
  have hHQ : H ≤ Q F a' := hHV.trans
    (V_le_Q_of_dist_add_lt_b F h.generate (fun v => (source_Z_Q_U h v).1)
      a' a' 1 (by simp only [SimpleGraph.dist_self, zero_add]; change 1 < b (family P); omega)
      (d.kernel_sylow a'))
  have hHL : H ≤ d.localGroup a' := hHQ.trans
    (pGroup_le_localGroup F d a' _ (isPGroup_pCoreIn 2 _) (Q_le_stabilizer F a'))
  have hnorm := (normal_subgroupOf_iff_le_normalizer hHL).mp hn
  have hQ₁P₂ : Q F x₁ ≤ stabilizer F x₂ :=
    (source_Z_Q_U h x₁).2.trans ((ballKernel_one_le_edge F h₂).trans inf_le_right)
  have hXL : X ≤ d.localGroup x₂ := sup_le hWL
    (pGroup_le_localGroup F d x₂ _ (isPGroup_pCoreIn 2 _) hQ₁P₂)
  have hXH : X ≤ centralizer (H : Set G) := sup_le hWH
    ((le_centralizer_iff.mp (Z_centralizes_Q F x₁ (source_Z_Q_U h x₁).1)).trans
      (centralizer_le (hHZ ⟨x₁,h₁⟩)))
  have hescape : ¬ Q F x₁ ≤ Q F x₂ := by
    intro he
    apply hob x₁ x₂ h₂
    rw [inf_eq_right.mpr he]
    exact stabilizer_normalizes_Q F x₁
  have hxne : x₂ ≠ a' := by
    intro he
    rw [he] at hd₂
    omega
  obtain ⟨S,hS⟩ := source_core_sylow_of_normalizing_subgroup h hB d h₂.symm h₁.symm hxne
    (models x₂) (models x₁) X H hXL le_sup_right hescape
    (le_inf ((hHZ ⟨x₁,h₁⟩).trans (Z_le_stabilizer F x₁)) (hHQ.trans (Q_le_stabilizer F a')))
    hne hnorm (hXH.trans (Subgroup.centralizer_le_normalizer _))
  exact ⟨hb5, hWQ, hp, hWH, x₁, x₂, x₃, h₁, h₂, h₃, hd₁, hd₂, hd₃,
    hWL, hWQ₃, hinter, hinside, hXL, hXH, ⟨S,hS⟩,
    fun he => source_core_intersection_le_third_core h hB d h₂.symm h₃ (models x₂)
      X W hXL S hS hp le_sup_left hWQ₃ he⟩

/-- Literal reduced-F1.11 application of the radius-three configuration.
This supplies the actual geodesic, full local actors and core-Sylow marking
for the remaining 8.4 proof at every ordered commuting critical pair. -/
theorem reduced_radius_three_configuration
    {J : Fin 2 → Subgroup G} {S₀ : Subgroup G} (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 3 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a, Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥) :
    let F := Reduction.reducedFamily J S₀
    let W := V F beta 3
    let H := ⁅V F beta 1 ⊓ Q F a', V F a' 1⁆
    5 ≤ b F ∧ W ≤ Q F beta ∧ IsPGroup 2 W ∧ W ≤ centralizer (H : Set (Reduction.G₀ J S₀)) ∧
      ∃ x₁ x₂ x₃ : Vertex F,
        (graph F).Adj a' x₁ ∧ (graph F).Adj x₁ x₂ ∧ (graph F).Adj x₂ x₃ ∧
        (graph F).dist beta x₁ + 1 = (graph F).dist beta a' ∧
        (graph F).dist beta x₂ + 1 = (graph F).dist beta x₁ ∧
        (graph F).dist beta x₃ + 1 = (graph F).dist beta x₂ ∧
        W ≤ graphLocalGroup F x₂ ∧ W ≤ Q F x₃ ∧ W ⊓ graphLocalGroup F x₁ ≤ Q F x₁ ∧
        (W ≤ Q F x₂ → W ≤ Q F x₁) ∧
        (let X := W ⊔ Q F x₁
         X ≤ graphLocalGroup F x₂ ∧ X ≤ centralizer (H : Set (Reduction.G₀ J S₀)) ∧
           (∃ S : Sylow 2 X, (S : Subgroup X).map X.subtype = Q F x₁) ∧
           (¬ W ≤ Q F x₂ → Q F x₁ ⊓ Q F x₂ ≤ Q F x₃)) :=
  source_radius_three_configuration (Reduction.reduced_triple h) (Reduction.reduced_borel_core_sylow h)
    (Reduction.reducedEarlierLocalTheorems h hob) hob models hc hab hd hb hcomm hne

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
