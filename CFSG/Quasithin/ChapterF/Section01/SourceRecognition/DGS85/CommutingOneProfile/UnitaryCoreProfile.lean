module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedBetaCoreSpecial
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedFieldParameters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedUnitaryCoreOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedSecondKernels
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedUnitaryCoreOrdersAllFields
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedAlphaNatural

/-!
# The assembled unitary core and natural alpha profile

This module collects the literal (11.8)(c)--(f) data already proved on an
escaping source path.  The output keeps both unitary markings, the actual
field degree, all strict order inequalities, the special-group layers, and
the elementary central quotient.  The full-Borel theorem is an application
of the same profile after identifying the reduced edge core with `O₂` of the
common Borel. The exact-order extension now gives the full core orders
for every positive fixed-field degree. Nonbinary fields use the faithful
Frattini degree bound; the binary case uses three-center normal-closure
transitivity and extraspecial order parity. The natural-section extension
proves Φ(Q_alpha)=Z_alpha and constructs coordinates on the literal quotient,
intertwining original conjugation with the selected SL₂ matrices. The
full-Borel natural profile selects both the beta marking and the alpha field
from the source inputs. Path lengths and odd path stabilizers remain for
the subsequent source argument. The kernel extension also proves
that the full alpha second kernel and beta third kernel vanish, while the
beta second-kernel radical is Z_beta. This applies at every positive degree,
including the binary field.
The field-parameter extension is re-exported here: its full-Borel theorem
identifies the alpha field as the square of the same beta fixed field and
provides the exact alpha-center, seed and pair orders for both unitary markings.
Source: DGS85, Groups and Graphs (1985), (11.8)(c)--(f), printed pp.175--176.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

/-- The complete unitary beta-core profile on the original escaping path. -/
theorem original_reduced_unitary_beta_profile_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b)
    (hesc : ¬ (Z F₀ b).map (G₀).subtype ≤ (Q F₀ (g • b)).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : (((Q F₀ b).map (G₀).subtype).subgroupOf
        (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype)).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 ((((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype) ⧸
        ((Q F₀ b).map (G₀).subtype).subgroupOf
          (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype))) :
    let qα := ((Q F₀ a).map (G₀).subtype).relIndex
      ((Z F₀ c).map (G₀).subtype ⊓ (Q F₀ b).map (G₀).subtype)
    ∃ n, 0 < n ∧
      (ClassicalGroup.IsPSU ((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 (2^n) ∨
       IsSU ((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 (2^n)) ∧
      Nat.card ((Z F₀ b).map (G₀).subtype) = 2^n ∧
      qα^2 * 2^n < Nat.card ((Q F₀ b).map (G₀).subtype) ∧
      qα^2 < ((Z F₀ b).map (G₀).subtype).relIndex ((Q F₀ b).map (G₀).subtype) ∧
      centerIn ((Q F₀ b).map (G₀).subtype) = (Z F₀ b).map (G₀).subtype ∧
      ⁅(Q F₀ b).map (G₀).subtype,(Q F₀ b).map (G₀).subtype⁆ =
        (Z F₀ b).map (G₀).subtype ∧
      (frattini ((Q F₀ b).map (G₀).subtype)).map
        ((Q F₀ b).map (G₀).subtype).subtype = (Z F₀ b).map (G₀).subtype ∧
      centerIn (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype) =
        (Z F₀ b).map (G₀).subtype ∧
      (∀ x ∈ (Q F₀ b).map (G₀).subtype, x^4 = 1) ∧
      ⁅⁅(Q F₀ b).map (G₀).subtype,(Q F₀ b).map (G₀).subtype⁆,
        (Q F₀ b).map (G₀).subtype⁆ = ⊥ ∧
      ⁅(Q F₀ b).map (G₀).subtype,(Q F₀ b).map (G₀).subtype⁆ ≠ ⊥ ∧
      ∃ hN : (((Z F₀ b).map (G₀).subtype).subgroupOf
          ((Q F₀ b).map (G₀).subtype)).Normal,
        letI := hN
        IsElementaryAbelian 2 ((Q F₀ b).map (G₀).subtype ⧸
          ((Z F₀ b).map (G₀).subtype).subgroupOf ((Q F₀ b).map (G₀).subtype)) := by
  obtain ⟨n,hn,mark,hcard,hlower,hindex,hcent,hder,hphi,hedge⟩ :=
    original_reduced_unitary_beta_core_special_on_escaping_path h d hc hb hcomm hbc hac
      Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne
  obtain ⟨_,_,hcl,hpow,hnon,hN,helem⟩ :=
    original_reduced_beta_core_layers_on_escaping_path h d hc hb hcomm hbc hac
      Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  refine ⟨n,hn,mark,hcard,hlower,hindex,hcent,hder,hphi,hedge,hpow,hcl,hnon,?_⟩
  exact ⟨hN,helem⟩

/-- The same profile at the literal full original Borel. -/
theorem original_borel_unitary_beta_profile_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {c : Vertex F₀} (hc : IsCriticalPair F₀ (base F₀ false) (base F₀ true))
    (hb : DGS85.b F₀ = 1)
    (hcomm : ⁅Z F₀ (base F₀ false),Z F₀ (base F₀ true)⁆ = ⊥)
    (hbc : (graph F₀).Adj (base F₀ true) c) (hac : (base F₀ false) ≠ c)
    (Ma : IsRankOneModel ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)))
    (g : G₀) (hga : g ∈ stabilizer F₀ (base F₀ false))
    (hgb : g • (base F₀ true) ≠ (base F₀ true))
    (hesc : ¬ (Z F₀ (base F₀ true)).map (G₀).subtype ≤
      (Q F₀ (g • (base F₀ true))).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : (base F₀ false) ∈ p.vertices) (hbp : (base F₀ true) ∈ p.vertices)
    (hcp : c ∈ p.vertices) (hgbp : g • (base F₀ true) ∈ p.vertices)
    (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
        (twoCore (commonBorel L₀ S₀))).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
        ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
          (twoCore (commonBorel L₀ S₀)))) :
    ∃ n, 0 < n ∧
      (ClassicalGroup.IsPSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^n) ∨
       IsSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^n)) ∧
      Nat.card ((Z F₀ (base F₀ true)).map (G₀).subtype) = 2^n ∧
      ((Q F₀ (base F₀ false)).map (G₀).subtype).relIndex
        ((Z F₀ c).map (G₀).subtype ⊓ (Q F₀ (base F₀ true)).map (G₀).subtype)^2 * 2^n <
        Nat.card ((Q F₀ (base F₀ true)).map (G₀).subtype) ∧
      ((Q F₀ (base F₀ false)).map (G₀).subtype).relIndex
        ((Z F₀ c).map (G₀).subtype ⊓ (Q F₀ (base F₀ true)).map (G₀).subtype)^2 <
        ((Z F₀ (base F₀ true)).map (G₀).subtype).relIndex
          ((Q F₀ (base F₀ true)).map (G₀).subtype) ∧
      centerIn ((Q F₀ (base F₀ true)).map (G₀).subtype) =
        (Z F₀ (base F₀ true)).map (G₀).subtype ∧
      ⁅(Q F₀ (base F₀ true)).map (G₀).subtype,
        (Q F₀ (base F₀ true)).map (G₀).subtype⁆ =
        (Z F₀ (base F₀ true)).map (G₀).subtype ∧
      (frattini ((Q F₀ (base F₀ true)).map (G₀).subtype)).map
        ((Q F₀ (base F₀ true)).map (G₀).subtype).subtype =
          (Z F₀ (base F₀ true)).map (G₀).subtype ∧
      centerIn (twoCore (commonBorel L₀ S₀)) =
        (Z F₀ (base F₀ true)).map (G₀).subtype ∧
      (∀ x ∈ (Q F₀ (base F₀ true)).map (G₀).subtype, x^4 = 1) ∧
      ⁅⁅(Q F₀ (base F₀ true)).map (G₀).subtype,
        (Q F₀ (base F₀ true)).map (G₀).subtype⁆,
        (Q F₀ (base F₀ true)).map (G₀).subtype⁆ = ⊥ ∧
      ⁅(Q F₀ (base F₀ true)).map (G₀).subtype,
        (Q F₀ (base F₀ true)).map (G₀).subtype⁆ ≠ ⊥ ∧
      ∃ hN : (((Z F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
          ((Q F₀ (base F₀ true)).map (G₀).subtype)).Normal,
        letI := hN
        IsElementaryAbelian 2 ((Q F₀ (base F₀ true)).map (G₀).subtype ⧸
          ((Z F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
            ((Q F₀ (base F₀ true)).map (G₀).subtype)) := by
  obtain ⟨n,hn,mark,hcard,hlower,hindex,hcent,hder,hphi,hedge⟩ :=
    original_borel_unitary_core_special_on_escaping_path h d hc hb hcomm hbc hac
      Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne
  obtain ⟨_,_,hcl,hpow,hnon,hN,helem⟩ :=
    original_reduced_beta_core_layers_on_escaping_path h d hc hb hcomm hbc hac
      Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  refine ⟨n,hn,mark,hcard,hlower,hindex,hcent,hder,hphi,hedge,hpow,hcl,hnon,?_⟩
  exact ⟨hN,helem⟩

/-- Apply the exact order theorem to the nonelementary full-Borel branch.
The selected binary field is retained as the separate outstanding source case. -/
theorem original_borel_unitary_core_orders_or_binary_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {c : Vertex F₀} (hc : IsCriticalPair F₀ (base F₀ false) (base F₀ true))
    (hb : DGS85.b F₀ = 1)
    (hcomm : ⁅Z F₀ (base F₀ false),Z F₀ (base F₀ true)⁆ = ⊥)
    (hbc : (graph F₀).Adj (base F₀ true) c) (hac : (base F₀ false) ≠ c)
    (Ma : IsRankOneModel ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)))
    (g : G₀) (hga : g ∈ stabilizer F₀ (base F₀ false))
    (hgb : g • (base F₀ true) ≠ (base F₀ true))
    (hesc : ¬ (Z F₀ (base F₀ true)).map (G₀).subtype ≤
      (Q F₀ (g • (base F₀ true))).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : (base F₀ false) ∈ p.vertices) (hbp : (base F₀ true) ∈ p.vertices)
    (hcp : c ∈ p.vertices) (hgbp : g • (base F₀ true) ∈ p.vertices)
    (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
        (twoCore (commonBorel L₀ S₀))).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
        ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
          (twoCore (commonBorel L₀ S₀)))) :
    ∃ m, 0 < m ∧
      (ClassicalGroup.IsPSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^m) ∨
       IsSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^m)) ∧
      (m = 1 ∨
        Nat.card ((Q F₀ (base F₀ true)).map (G₀).subtype) = 2^(7*m) ∧
        Nat.card (twoCore (commonBorel L₀ S₀)) = 2^(10*m) ∧
        Nat.card ((Q F₀ (base F₀ false)).map (G₀).subtype) = 2^(8*m) ∧
        ((Z F₀ (base F₀ false)).map (G₀).subtype).relIndex
          ((Q F₀ (base F₀ false)).map (G₀).subtype) = 2^(4*m)) := by
  obtain ⟨m,hm,mark,_⟩ := original_borel_unitary_beta_profile_on_escaping_path h d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne
  refine ⟨m,hm,mark,?_⟩
  by_cases hbinary : m = 1
  · exact Or.inl hbinary
  · exact Or.inr (original_borel_unitary_core_orders_on_escaping_path h d hc hb hcomm
      hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp m (by omega) mark)

/-- The exact source core orders at every positive unitary field degree,
with both original coverings and the full Borel retained. -/
theorem original_borel_unitary_exact_orders_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {c : Vertex F₀} (hc : IsCriticalPair F₀ (base F₀ false) (base F₀ true))
    (hb : DGS85.b F₀ = 1)
    (hcomm : ⁅Z F₀ (base F₀ false),Z F₀ (base F₀ true)⁆ = ⊥)
    (hbc : (graph F₀).Adj (base F₀ true) c) (hac : (base F₀ false) ≠ c)
    (Ma : IsRankOneModel ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)))
    (g : G₀) (hga : g ∈ stabilizer F₀ (base F₀ false))
    (hgb : g • (base F₀ true) ≠ (base F₀ true))
    (hesc : ¬ (Z F₀ (base F₀ true)).map (G₀).subtype ≤
      (Q F₀ (g • (base F₀ true))).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : (base F₀ false) ∈ p.vertices) (hbp : (base F₀ true) ∈ p.vertices)
    (hcp : c ∈ p.vertices) (hgbp : g • (base F₀ true) ∈ p.vertices)
    (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
        (twoCore (commonBorel L₀ S₀))).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
        ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
          (twoCore (commonBorel L₀ S₀)))) :
    ∃ m, 0 < m ∧
      (ClassicalGroup.IsPSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^m) ∨
       IsSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^m)) ∧
      Nat.card ((Q F₀ (base F₀ true)).map (G₀).subtype) = 2^(7*m) ∧
        Nat.card (twoCore (commonBorel L₀ S₀)) = 2^(10*m) ∧
        Nat.card ((Q F₀ (base F₀ false)).map (G₀).subtype) = 2^(8*m) ∧
        ((Z F₀ (base F₀ false)).map (G₀).subtype).relIndex
          ((Q F₀ (base F₀ false)).map (G₀).subtype) = 2^(4*m) := by
  obtain ⟨m,hm,mark,_⟩ := original_borel_unitary_beta_profile_on_escaping_path h d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne
  refine ⟨m,hm,mark,?_⟩
  exact original_borel_unitary_core_orders_all_fields_on_escaping_path h d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne m hm mark

/-- In the literal nonelementary full-Borel branch, both unitary covers
have the proved full-kernel depths and beta second-kernel radical order.
No lower bound of two on the field degree is imposed. -/
theorem original_borel_unitary_second_kernel_profile_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {c : Vertex F₀} (hc : IsCriticalPair F₀ (base F₀ false) (base F₀ true))
    (hb : DGS85.b F₀ = 1)
    (hcomm : ⁅Z F₀ (base F₀ false),Z F₀ (base F₀ true)⁆ = ⊥)
    (hbc : (graph F₀).Adj (base F₀ true) c) (hac : (base F₀ false) ≠ c)
    (Ma : IsRankOneModel ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)))
    (g : G₀) (hga : g ∈ stabilizer F₀ (base F₀ false))
    (hgb : g • (base F₀ true) ≠ (base F₀ true))
    (hesc : ¬ (Z F₀ (base F₀ true)).map (G₀).subtype ≤
      (Q F₀ (g • (base F₀ true))).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : (base F₀ false) ∈ p.vertices) (hbp : (base F₀ true) ∈ p.vertices)
    (hcp : c ∈ p.vertices) (hgbp : g • (base F₀ true) ∈ p.vertices)
    (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
        (twoCore (commonBorel L₀ S₀))).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
        ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
          (twoCore (commonBorel L₀ S₀)))) :
    ∃ n, 0 < n ∧
      (ClassicalGroup.IsPSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^n) ∨
       IsSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^n)) ∧
      (ballKernel F₀ (base F₀ false) 2).map (G₀).subtype = ⊥ ∧
      (ballKernel F₀ (base F₀ true) 3).map (G₀).subtype = ⊥ ∧
      ((ballKernel F₀ (base F₀ true) 2).map (G₀).subtype).pCoreIn 2 =
        (Z F₀ (base F₀ true)).map (G₀).subtype ∧
      Nat.card (((ballKernel F₀ (base F₀ true) 2).map (G₀).subtype).pCoreIn 2) = 2^n ∧
      (ballKernel F₀ (base F₀ true) 2).map (G₀).subtype ≠ ⊥ := by
  obtain ⟨n,hn,mark,hcard,_⟩ := original_borel_unitary_beta_profile_on_escaping_path h d
    hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne
  obtain ⟨hα,hβ,hR,hRne⟩ := original_reduced_second_kernels_on_escaping_path h d
    hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  exact ⟨n,hn,mark,hα,hβ,hR,hR.symm ▸ hcard,hRne⟩

/-- The nonelementary full-Borel branch constructs the original natural alpha
quotient over the selected field, including the binary unitary case. -/
theorem original_borel_unitary_natural_profile_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {c : Vertex F₀} (hc : IsCriticalPair F₀ (base F₀ false) (base F₀ true))
    (hb : DGS85.b F₀ = 1)
    (hcomm : ⁅Z F₀ (base F₀ false),Z F₀ (base F₀ true)⁆ = ⊥)
    (hbc : (graph F₀).Adj (base F₀ true) c) (hac : (base F₀ false) ≠ c)
    (Ma : IsRankOneModel ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)))
    (g : G₀) (hga : g ∈ stabilizer F₀ (base F₀ false))
    (hgb : g • (base F₀ true) ≠ (base F₀ true))
    (hesc : ¬ (Z F₀ (base F₀ true)).map (G₀).subtype ≤
      (Q F₀ (g • (base F₀ true))).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : (base F₀ false) ∈ p.vertices) (hbp : (base F₀ true) ∈ p.vertices)
    (hcp : c ∈ p.vertices) (hgbp : g • (base F₀ true) ∈ p.vertices)
    (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
        (twoCore (commonBorel L₀ S₀))).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
        ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
          (twoCore (commonBorel L₀ S₀)))) :
    ∃ m, 0 < m ∧
      (ClassicalGroup.IsPSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^m) ∨
       IsSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^m)) ∧
    let R := (Q F₀ (base F₀ false)).map (G₀).subtype
    let A := (Z F₀ (base F₀ false)).map (G₀).subtype
    let L := (d.localGroup (base F₀ false)).map (G₀).subtype
    (frattini R).map R.subtype = A ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
        Nat.card k = 2^(2*m) ∧
        ∃ ea : (L ⧸ pCore 2 L) ≃* SL(2,k),
          ∃ f : R →* Multiplicative (Fin 2 → k), Function.Surjective f ∧
            f.ker = A.subgroupOf R ∧
            ∀ (l : L) (x y : R), (y : G) = (l : G) * (x : G) * (l : G)⁻¹ →
              (f y).toAdd = Matrix.mulVec (ea (QuotientGroup.mk' (pCore 2 L) l)).val (f x).toAdd := by
  obtain ⟨m,hm,mark,_⟩ := original_borel_unitary_beta_profile_on_escaping_path h d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne
  exact ⟨m,hm,mark,original_borel_unitary_alpha_natural_on_escaping_path h d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne m hm mark⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
