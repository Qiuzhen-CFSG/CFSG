module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SmallBetaSeedSquare
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedCoreApplication

/-!
# General commuting-one seed bounds, core product and alpha selection

The complete beta catalogue now satisfies the prime-two seed-square
inequality. Linear beta uses its elementary edge quotient; positive Suzuki
parameters use the quadratic module bound; both nonbinary unitary carriers
use exclusion of the elementary pair; the four small models use their
literal order-four pair section. Alpha is not preselected in this argument.

The proved index comparison consequently gives S=Q_alpha Q_beta. Together
with the independent pair-core span this selects the actual linear alpha
quotient of field order greater than two. The opposite seed is nonquadratic
and the pair is nonabelian. The original-completion applications preserve
both local quotient markings, the seed indices and the full edge radical.
The literal (11.6) neighbor-separation consumer has both core premises
discharged, including its original-inclusion vanishing statement.

Earlier local data, the rank-one catalogue and actual path transitivity
remain explicit source inputs. The nonlinear (11.8) profile, Suzuki
exclusion, general-field path stabilizers and final marked assembly remain
separate obligations of this theorem family.
Source: DGS85, Groups and Graphs (1985), (11.3)(e--h), (11.4)--(11.6),
printed pp.169--174; corrected (5.12), pp.113--115.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

open SimpleGraph SimpleGraph.PathTransitivePolygon
/-- Source (11.3)(g) at prime two for the complete beta catalogue. Alpha
is arbitrary; the two seed indices are those of the original critical pair. -/
theorem source_seed_square_on_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
    ((Q (family P) b).relIndex (Z (family P) a))^2 ≤
      (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b) := by
  cases Mb with
  | linear n hn mark =>
    have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := .linear n hn mark
    obtain ⟨k,_,_,hk,⟨eb⟩⟩ := mark
    let : Fintype k := Fintype.ofFinite k
    let : CharP k 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hk)
    let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
      MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
        ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
    exact source_linear_beta_seed_square_on_path h hB d hc hb hcomm hbc hac Ma Mb
      (eb.trans ep.symm) ht p hp ha hb' hc'
  | dihedral eb =>
    exact source_small_beta_model_seed_square h hB d hc hb hcomm hbc hac Ma (.dihedral eb) (Or.inl eb)
  | suzuki m eb =>
    by_cases hm : m = 0
    · subst m
      exact source_small_beta_model_seed_square h hB d hc hb hcomm hbc hac Ma (.suzuki 0 eb)
        (Or.inr (Or.inl eb))
    · exact source_suzuki_seed_square h hB d hc hb hbc hac Ma (by omega) eb.some
  | projective_unitary n hn hi =>
    by_cases hn1 : n = 1
    · have hs : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 2 := by
        simpa only [hn1,pow_one] using hi
      exact source_small_beta_model_seed_square h hB d hc hb hcomm hbc hac Ma
        (.projective_unitary n hn hi) (Or.inr (Or.inr (Or.inr hs)))
    · exact source_unitary_seed_square h hB d hc hb hcomm hbc hac Ma (by omega) (Or.inl hi)
  | special_unitary n hn hi =>
    by_cases hn1 : n = 1
    · have hs : IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 2 := by
        simpa only [hn1,pow_one] using hi
      exact source_small_beta_model_seed_square h hB d hc hb hcomm hbc hac Ma
        (.special_unitary n hn hi) (Or.inr (Or.inr (Or.inl hs)))
    · exact source_unitary_seed_square h hB d hc hb hcomm hbc hac Ma (by omega) (Or.inr hi)

/-- The general source core product and alpha selection. The seed bound
and pair-core span are discharged for every original catalogue alternative. -/
theorem source_core_product_and_alpha_on_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      Q (family P) a ⊔ Q (family P) b ∧
      ∃ n, 1 < n ∧ ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2^n) := by
  have hbound := source_seed_square_on_path h hB d hc hb hcomm hbc hac Ma Mb ht p hp ha hb' hc'
  exact ⟨source_core_product_of_seed_square_bound_on_path h hB d hc hb hbc hac Ma Mb hbound ht p hp ha hb' hc',
    source_alpha_linear_of_seed_square_bound_on_path h hB d hc hb hcomm hbc hac Ma Mb hbound ht p hp ha hb' hc'⟩

/-- Both nonquadratic seed action and nonabelianness of the actual pair,
without any assumed alpha marking or core identity. -/
theorem source_seed_nonquadratic_and_pair_nonabelian_on_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
    ⁅⁅Z (family P) a,Z (family P) c ⊓ Q (family P) b⁆,
      Z (family P) c ⊓ Q (family P) b⁆ ≠ ⊥ ∧
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    ⁅V,V⁆ ≠ ⊥ := by
  have hh := source_core_product_and_alpha_on_path h hB d hc hb hcomm hbc hac Ma Mb ht p hp ha hb' hc'
  have hcore := source_rankOne_pair_core_span_on_path h hB d hc hb hbc hac Ma Mb ht p hp ha hb' hc'
  have hsupp : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      (Z (family P) c ⊓ Q (family P) b) ⊔ Q (family P) a := by
    rw [sup_comm]
    exact alpha_supplement_of_pair_generation _ _ _ _ _ hh.1 hcore
      ((source_Z_Q_U h a).1.trans (map_subtype_le _))
  refine ⟨source_seed_nonquadratic_of_supplement h hB d hc hb hcomm hbc hac Mb hsupp,?_⟩
  exact source_pair_nonabelian_of_seed_index_le h hB d hc hb hcomm hbc hac Ma Mb
    ((Nat.le_self_pow (by decide) _).trans
      (source_seed_square_on_path h hB d hc hb hcomm hbc hac Ma Mb ht p hp ha hb' hc'))

section Original
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

/-- The full source seed inequality on the original subgroup images. -/
theorem original_reduced_seed_square_on_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
    (((Q F₀ b).map (G₀).subtype).relIndex ((Z F₀ a).map (G₀).subtype))^2 ≤
      ((Q F₀ a).map (G₀).subtype).relIndex
        ((Z F₀ c).map (G₀).subtype ⊓ (Q F₀ b).map (G₀).subtype) := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  rw [←map_inf _ _ _ (G₀).subtype_injective,
    relIndex_map_map_of_injective _ _ (G₀).subtype_injective,
    relIndex_map_map_of_injective _ _ (G₀).subtype_injective]
  exact source_seed_square_on_path (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hcomm hbc hac (Ma.of_equiv eqa)
      (Mb.of_equiv eqb) ht p hp ha hb' hc'

/-- General (11.4)--(11.5) in the original completion, with both quotient
markings and the full edge radical retained. -/
theorem original_reduced_core_product_and_alpha_on_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
    (((stabilizer F₀ a).map (G₀).subtype) ⊓
      ((stabilizer F₀ b).map (G₀).subtype)).pCoreIn 2 =
      (Q F₀ a).map (G₀).subtype ⊔ (Q F₀ b).map (G₀).subtype ∧
    ∃ n, 1 < n ∧ ClassicalGroup.IsPSL
      ((d.localGroup a).map (G₀).subtype ⧸ pCore 2 ((d.localGroup a).map (G₀).subtype)) 2 (2^n) := by
  exact original_reduced_core_product_and_alpha_of_seed_square_bound_on_path
    h d hc hb hcomm hbc hac Ma Mb
    (original_reduced_seed_square_on_path h d hc hb hcomm hbc hac Ma Mb ht p hp ha hb' hc')
    ht p hp ha hb' hc'

/-- The actual (11.6) neighbor-separation consumer, with both core identities
and alpha selection discharged. Its vanishing is retained under the original
completion inclusion. -/
theorem reduced_rankOne_neighbor_separation_on_path (h : HypothesisF11 L₀ S₀)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices)
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b) :
    (∀ v, (graph F₀).Adj a v →
      ∃ w ∈ (Z F₀ c ⊓ Q F₀ b) ⊔ (Z F₀ (g • c) ⊓ Q F₀ (g • b)), w • b = v) ∧
      neighborCoreIntersection F₀ b ⊓ Q F₀ (g • c) = ⊥ ∧
      (neighborCoreIntersection F₀ b).map (G₀).subtype ⊓ (Q F₀ (g • c)).map (G₀).subtype = ⊥ := by
  have hproduct := (source_core_product_and_alpha_on_path (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hcomm hbc hac Ma Mb ht p hp ha hb' hc').1
  have hcore := source_rankOne_pair_core_span_on_path (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac Ma Mb ht p hp ha hb' hc'
  exact reduced_rankOne_neighbor_separation h d hc hb hbc hac Ma Mb hproduct hcore g hga hgb

end Original
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
