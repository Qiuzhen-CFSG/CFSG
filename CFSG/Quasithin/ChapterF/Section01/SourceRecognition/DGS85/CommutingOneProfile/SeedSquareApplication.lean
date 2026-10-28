module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CoreProductOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairLinearMultiplicity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairSuzukiBounds

/-!
# Source applications of the Chapter 11 seed bounds

For linear beta, its elementary Sylow quotient first supplies the core
product; the already proved pair-core span then selects alpha. This proves
the seed-square inequality without an assumed alpha marking. For every
nondegenerate Suzuki beta quotient the new square bound directly supplies
(11.4) and alpha selection, through the full catalogue order comparison.

For both nonbinary unitary beta carriers, the same comparison either gives
those conclusions or leaves an elementary pair with equal source seed
indices. The latter is the precise remaining (11.3)(e) obstacle, not a
completed unitary source theorem. All original-completion applications
retain the reduction inclusion, endpoint quotient markings and edge radical.
The small beta cases, general unitary exclusion of the elementary pair,
nonlinear profiles and final marked assembly remain with this owner.

Source: DGS85, Groups and Graphs (1985), (11.3)(e,g,h),
(11.4)--(11.5), printed pp.169--172.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]
local instance : Algebra (ZMod 2) k := ZMod.algebra k 2
open BenderSuzuki.MatrixGroups

open SimpleGraph SimpleGraph.PathTransitivePolygon
/-- The seed-square inequality for every linear beta field, with alpha
selected from the actual core identities rather than assumed linear. -/
theorem source_linear_beta_seed_square_on_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
    ((Q (family P) b).relIndex (Z (family P) a))^2 ≤
      (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b) := by
  have hab := source_critical_one_adjacent hc hb
  have hsupp := source_linear_center_supplement h hB d hab Mb eb
    (fun he => hc.2 (he.trans (source_Z_Q_U h b).2))
  rw [inf_comm] at hsupp
  have hprod : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      Q (family P) a ⊔ Q (family P) b := by
    apply le_antisymm
    · rw [hsupp]
      exact sup_le (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans le_sup_left) le_sup_right
    · exact sup_le (Noncommuting.graph_Q_le_edgeCore h hab)
        (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm)
  obtain ⟨n,hn,mark⟩ := source_alpha_linear_of_core_identities h hB d hc hb hcomm hbc hac Ma Mb
    hprod (source_rankOne_pair_core_span_on_path h hB d hc hb hbc hac Ma Mb ht p hp ha hb' hc')
  obtain ⟨ka,_,_,hcard,⟨ea⟩⟩ := mark
  let : Fintype ka := Fintype.ofFinite ka
  let : CharP ka 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let ep : SL(2,ka) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) ka :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi ka)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  obtain ⟨f,hf,hk,R,hR⟩ := source_linear_pair_actor h hB d hc hb hbc hac Mb eb
  rcases source_pair_linear_seed_square_or_elementary h hB d hc hb hbc hac Ma Mb f hf hk R hR with hbound | helem
  · exact hbound
  · let := helem.2
    exact False.elim (source_linear_rankOne_pair_nonabelian h hB d hc hb hcomm hbc hac Ma Mb (ea.trans ep.symm)
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff_isMulCommutative.mpr
        (inferInstance : IsMulCommutative (pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b))))))
/-- The nondegenerate Suzuki beta branch now supplies both source (11.4)
and the actual alpha selection, with no numerical premise. -/
theorem source_suzuki_core_product_and_alpha_on_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {m : ℕ} (hm : 0 < m)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SuzukiMatrixGroup m)
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
      (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
        Q (family P) a ⊔ Q (family P) b ∧
      ∃ n, 1 < n ∧ ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2^n) := by
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := .suzuki m ⟨eb⟩
  have hbound := source_suzuki_seed_square h hB d hc hb hbc hac Ma hm eb
  exact ⟨source_core_product_of_seed_square_bound_on_path h hB d hc hb hbc hac Ma Mb hbound ht p hp ha hb' hc',
    source_alpha_linear_of_seed_square_bound_on_path h hB d hc hb hcomm hbc hac Ma Mb hbound ht p hp ha hb' hc'⟩

/-- The unitary branch is reduced to the exact earlier (11.3)(e) obstacle:
an elementary pair with equal alpha and beta seed indices. -/
theorem source_unitary_core_product_and_alpha_or_elementary_pair_on_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {n : ℕ} (hn : 2 ≤ n)
    (hi : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
    ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
        Q (family P) a ⊔ Q (family P) b ∧
      ∃ n, 1 < n ∧ ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2^n)) ∨
      (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b) =
        (Q (family P) b).relIndex (Z (family P) a) ∧
      IsElementaryAbelian 2 (pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)) := by
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) :=
    hi.elim (.projective_unitary n (by omega)) (.special_unitary n (by omega))
  rcases source_unitary_seed_square_or_elementary h hB d hc hb hbc hac Ma hn hi with hbound | hsmall
  · exact Or.inl ⟨source_core_product_of_seed_square_bound_on_path h hB d hc hb hbc hac Ma Mb hbound ht p hp ha hb' hc',
      source_alpha_linear_of_seed_square_bound_on_path h hB d hc hb hcomm hbc hac Ma Mb hbound ht p hp ha hb' hc'⟩
  · exact Or.inr hsmall


section Original
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

/-- The Suzuki beta branch in the original completion, with the full edge
radical and alpha quotient marking transported through its inclusion. -/
theorem original_reduced_suzuki_core_product_and_alpha_on_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    {m : ℕ} (hm : 0 < m)
    (eb : ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)) ≃* SuzukiMatrixGroup m)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
    (((stabilizer F₀ a).map (G₀).subtype) ⊓
      ((stabilizer F₀ b).map (G₀).subtype)).pCoreIn 2 =
      (Q F₀ a).map (G₀).subtype ⊔ (Q F₀ b).map (G₀).subtype ∧
    ∃ n, 1 < n ∧ ClassicalGroup.IsPSL
      ((d.localGroup a).map (G₀).subtype ⧸ pCore 2 ((d.localGroup a).map (G₀).subtype)) 2 (2^n) := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb₀ := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb₀ (pCore_map_iso 2 eb₀)
  obtain ⟨hproduct,n,hn,hmark⟩ := source_suzuki_core_product_and_alpha_on_path
    (Reduction.reduced_triple h) (Reduction.reduced_borel_core_sylow h) d hc hb hcomm hbc hac
      (Ma.of_equiv eqa) hm (eqb.trans eb) ht p hp ha hb' hc'
  refine ⟨?_,n,hn,hmark.of_mulEquiv eqa.symm⟩
  have hh := congrArg (Subgroup.map (G₀).subtype) hproduct
  rw [map_pCoreIn_of_injective 2 _ _ (G₀).subtype_injective,
    map_inf _ _ _ (G₀).subtype_injective,Subgroup.map_sup] at hh
  exact hh

/-- Both original unitary quotient markings are retained. The second
alternative is the literal elementary pair still requiring exclusion. -/
theorem original_reduced_unitary_core_product_and_alpha_or_elementary_pair_on_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    {n : ℕ} (hn : 2 ≤ n)
    (hi : ClassicalGroup.IsPSU ((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 (2^n) ∨
      IsSU ((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 (2^n))
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
    ((((stabilizer F₀ a).map (G₀).subtype) ⊓
      ((stabilizer F₀ b).map (G₀).subtype)).pCoreIn 2 =
      (Q F₀ a).map (G₀).subtype ⊔ (Q F₀ b).map (G₀).subtype ∧
    ∃ n, 1 < n ∧ ClassicalGroup.IsPSL
      ((d.localGroup a).map (G₀).subtype ⧸ pCore 2 ((d.localGroup a).map (G₀).subtype)) 2 (2^n)) ∨
      ((Q F₀ a).map (G₀).subtype).relIndex
        ((Z F₀ c).map (G₀).subtype ⊓ (Q F₀ b).map (G₀).subtype) =
        ((Q F₀ b).map (G₀).subtype).relIndex ((Z F₀ a).map (G₀).subtype) ∧
      IsElementaryAbelian 2 ((pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b)).map (G₀).subtype) := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb₀ := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb₀ (pCore_map_iso 2 eb₀)
  have hi₀ : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) := by
    rcases hi with hi | hi
    · exact Or.inl (hi.of_mulEquiv eqb)
    · obtain ⟨E,hE,hfin,J,hcard,hconj,⟨e⟩⟩ := hi
      exact Or.inr ⟨E,hE,hfin,J,hcard,hconj,⟨eqb.trans e⟩⟩
  rcases source_unitary_core_product_and_alpha_or_elementary_pair_on_path
    (Reduction.reduced_triple h) (Reduction.reduced_borel_core_sylow h) d hc hb hcomm hbc hac
      (Ma.of_equiv eqa) hn hi₀ ht p hp ha hb' hc' with ⟨hproduct,n',hn',hmark⟩ | ⟨he,helem⟩
  · apply Or.inl
    refine ⟨?_,n',hn',hmark.of_mulEquiv eqa.symm⟩
    have hh := congrArg (Subgroup.map (G₀).subtype) hproduct
    rw [map_pCoreIn_of_injective 2 _ _ (G₀).subtype_injective,
      map_inf _ _ _ (G₀).subtype_injective,Subgroup.map_sup] at hh
    exact hh
  · apply Or.inr
    refine ⟨?_,?_⟩
    · rw [←map_inf _ _ _ (G₀).subtype_injective,
        relIndex_map_map_of_injective _ _ (G₀).subtype_injective,
        relIndex_map_map_of_injective _ _ (G₀).subtype_injective]
      exact he
    · let : IsElementaryAbelian 2 (pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b)) := helem
      exact IsElementaryAbelian.map (G₀).subtype

/-- The linear-beta seed bound on the original subgroup images. -/
theorem original_reduced_linear_beta_seed_square_on_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    (eb : ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)) ≃* SL(2,k))
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
    (((Q F₀ b).map (G₀).subtype).relIndex ((Z F₀ a).map (G₀).subtype))^2 ≤
      ((Q F₀ a).map (G₀).subtype).relIndex
        ((Z F₀ c).map (G₀).subtype ⊓ (Q F₀ b).map (G₀).subtype) := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb₀ := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb₀ (pCore_map_iso 2 eb₀)
  rw [←map_inf _ _ _ (G₀).subtype_injective,
    relIndex_map_map_of_injective _ _ (G₀).subtype_injective,
    relIndex_map_map_of_injective _ _ (G₀).subtype_injective]
  exact source_linear_beta_seed_square_on_path (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hcomm hbc hac (Ma.of_equiv eqa)
      (Mb.of_equiv eqb) (eqb.trans eb) ht p hp ha hb' hc'
end Original


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
