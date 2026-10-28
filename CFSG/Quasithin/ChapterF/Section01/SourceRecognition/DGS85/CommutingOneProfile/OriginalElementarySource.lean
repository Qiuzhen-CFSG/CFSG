module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryInitial
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LinearBetaSource

/-!
# The elementary Chapter 11 branch on the full original Borel

The literal quotient O₂(B)/Q_beta is transported through the original
inclusion to the reduced edge. Its elementary property selects a linear
or dihedral beta quotient. The path-free dihedral exclusion removes the
second alternative without an alpha marking. The genuine linear beta
action then selects alpha and gives the square-field relation, both core
orders, the full-Borel order, corrected beta span, center and r=4, s=5.
The resulting universal-tree path inputs feed the actual Chapter 14 roots.

Both local quotient catalogues remain explicit. No branch choice, linear
marking, escape, path-transitivity or earlier-local record is assumed.
This does not by itself identify the marked amalgam.
Source: DGS, Groups and Graphs (1985), (11.7), pp.174--175; (14.1), p.210.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open Reduction NoncommutingProfile
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

private theorem elementary_of_mapped_quotient {H : Type*} [Group H]
    (R N : Subgroup H) (hNR : N ≤ R) (f : H →* G) (hf : Function.Injective f)
    [(N.subgroupOf R).Normal]
    (helem : ∃ hn : ((N.map f).subgroupOf (R.map f)).Normal, letI := hn
      IsElementaryAbelian 2 (R.map f ⧸ (N.map f).subgroupOf (R.map f))) :
    IsElementaryAbelian 2 (R ⧸ N.subgroupOf R) := by
  obtain ⟨hn,helem⟩ := helem
  let := hn
  let := helem
  let e := R.equivMapOfInjective f hf
  have hmap : (N.subgroupOf R).map e.toMonoidHom = (N.map f).subgroupOf (R.map f) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact mem_map_of_mem f hy
    · intro hx
      obtain ⟨y,hy,heq⟩ := hx
      exact ⟨⟨y,hNR hy⟩,hy,Subtype.ext heq⟩
  let eq := QuotientGroup.congr _ _ e hmap
  exact IsElementaryAbelian.of_surjective eq.symm.toMonoidHom eq.symm.surjective

/-- Elementary beta selection on the literal original quotient, with the
alpha linear marking and the dihedral candidate both discharged. -/
theorem original_reduced_elementary_linear_beta
    (h : HypothesisF11 L₀ S₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (Ma : IsRankOneModel ((graphLocalGroup F₀ a).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((graphLocalGroup F₀ b).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ b).map (G₀).subtype)))
    (helem : ∃ hN : (((Q F₀ b).map (G₀).subtype).subgroupOf
        (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype)).Normal,
      letI := hN
      IsElementaryAbelian 2 ((((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype) ⧸
        ((Q F₀ b).map (G₀).subtype).subgroupOf
          (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype))) :
    ∃ m, 0 < m ∧ ClassicalGroup.IsPSL ((graphLocalGroup F₀ b).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ b).map (G₀).subtype)) 2 (2^m) := by
  let d := reducedFullEarlierLocalTheorems h
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  let R := (stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2
  let hN : ((Q F₀ b).subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer
    (((pCoreIn_le 2 _).trans inf_le_right).trans (stabilizer_normalizes_Q _ _))
  have hQR : Q F₀ b ≤ R := by
    have hh := Noncommuting.graph_Q_le_edgeCore (reduced_triple h)
      (source_critical_one_adjacent hc hb).symm
    change Q F₀ b ≤ (stabilizer F₀ b ⊓ stabilizer F₀ a).pCoreIn 2 at hh
    rwa [inf_comm (stabilizer F₀ b) (stabilizer F₀ a)] at hh
  have he := elementary_of_mapped_quotient R (Q F₀ b) hQR
    (G₀).subtype (G₀).subtype_injective helem
  obtain ⟨m,hm,mark⟩ := reduced_elementary_beta_selection h d hc hb hcomm
    (Ma.of_equiv eqa) (Mb.of_equiv eqb) ⟨hN,he⟩
  exact ⟨m,hm,mark.of_mulEquiv eqb.symm⟩

variable (h : HypothesisF11 L₀ S₀)
    (hc : IsCriticalPair (Reduction.reducedFamily L₀ S₀)
      (base (Reduction.reducedFamily L₀ S₀) false) (base (Reduction.reducedFamily L₀ S₀) true))
    (hb : DGS85.b (Reduction.reducedFamily L₀ S₀) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false),
      Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)⁆ = ⊥)
    (Ma : IsRankOneModel ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
      (base (Reduction.reducedFamily L₀ S₀) false)).map (Reduction.G₀ L₀ S₀).subtype ⧸
      pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
        (base (Reduction.reducedFamily L₀ S₀) false)).map (Reduction.G₀ L₀ S₀).subtype)))
    (Mb : IsRankOneModel ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
      (base (Reduction.reducedFamily L₀ S₀) true)).map (Reduction.G₀ L₀ S₀).subtype ⧸
      pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
        (base (Reduction.reducedFamily L₀ S₀) true)).map (Reduction.G₀ L₀ S₀).subtype)))
    (helem : ∃ hN : (((Q (Reduction.reducedFamily L₀ S₀)
        (base (Reduction.reducedFamily L₀ S₀) true)).map (Reduction.G₀ L₀ S₀).subtype).subgroupOf
        (twoCore (commonBorel L₀ S₀))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
        ((Q (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map
          (Reduction.G₀ L₀ S₀).subtype).subgroupOf (twoCore (commonBorel L₀ S₀))))

include h hc hb hcomm Ma Mb helem

/-- The literal elementary quotient of the full original Borel two-core
selects the actual linear beta marking and its positive field degree. -/
theorem original_borel_elementary_linear_beta :
    ∃ m, 0 < m ∧ ClassicalGroup.IsPSL
      ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype)) 2 (2^m) := by
  let R := (stabilizer F₀ (base F₀ false) ⊓ stabilizer F₀ (base F₀ true)).pCoreIn 2
  have htr := reduced_triple h
  have hBG : B₀ L₀ S₀ ≤ G₀ :=
    (show B₀ L₀ S₀ ≤ P₀ L₀ S₀ 0 from le_sup_right).trans le_sup_left
  have hRG : twoCore (commonBorel L₀ S₀) ≤ G₀ :=
    (show twoCore (commonBorel L₀ S₀) ≤ B₀ L₀ S₀ from le_sup_right).trans hBG
  have hmap : R.map (G₀).subtype = twoCore (commonBorel L₀ S₀) := by
    dsimp only [R]
    rw [show stabilizer F₀ (base F₀ false) = F₀ false from Subgroup.CosetGeometry.stabilizer_base _ _,
      show stabilizer F₀ (base F₀ true) = F₀ true from Subgroup.CosetGeometry.stabilizer_base _ _,
      show F₀ false ⊓ F₀ true = (B₀ L₀ S₀).subgroupOf G₀ from htr.intersection,
      pCoreIn_subgroupOf 2 _ _ hBG,B₀_core h]
    exact map_subgroupOf_eq_of_le hRG
  apply original_reduced_elementary_linear_beta h hc hb hcomm Ma Mb
  change ∃ hN : (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf (R.map (G₀).subtype)).Normal,
    letI := hN
    IsElementaryAbelian 2 (R.map (G₀).subtype ⧸
      ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf (R.map (G₀).subtype))
  rw [hmap]
  exact helem

/-- The field, numerical and path clauses of (11.7) from its literal
full-Borel branch. Both linear markings are outputs, at the same degree. -/
theorem original_borel_elementary_orders_and_paths :
    ∃ m, 0 < m ∧
      ClassicalGroup.IsPSL ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype)) 2 (2^m) ∧
      ClassicalGroup.IsPSL ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype)) 2 (2^(2*m)) ∧
      (Q F₀ (base F₀ false)).map (G₀).subtype = (Z F₀ (base F₀ false)).map (G₀).subtype ∧
      Nat.card ((Z F₀ (base F₀ true)).map (G₀).subtype) = 2^m ∧
      Nat.card ((Q F₀ (base F₀ false)).map (G₀).subtype) = (2^(2*m))^2 ∧
      Nat.card ((Q F₀ (base F₀ true)).map (G₀).subtype) = (2^(2*m))^2 * 2^m ∧
      Nat.card (twoCore (commonBorel L₀ S₀)) = (2^(2*m))^2 * (2^m)^2 ∧
      HasSourcePathParameters (P := fun i => (P₀ L₀ S₀ i).subgroupOf G₀) 4 5 ∧
      (∀ x : Vertex F₀, RootPathTransitive (graph F₀) G₀ x 5) ∧
      ∀ {x y : Vertex F₀} (q : (graph F₀).Walk x y), IsSourcePath q → 5 ≤ q.length →
        Odd (Nat.card ((pathFixer (X := G₀) q).map (G₀).subtype)) := by
  obtain ⟨m,hm,mark⟩ := original_borel_elementary_linear_beta h hc hb hcomm Ma Mb helem
  obtain ⟨ha,hQa,hZb,hca,hcb,hS⟩ := original_linear_beta_core_profile h hc hb hcomm Ma hm mark
  exact ⟨m,hm,mark,ha,hQa,hZb,hca,hcb,hS,
    original_linear_beta_source_path_profile h hc hb hcomm Ma hm mark⟩

/-- The corrected Chapter 11 beta seed span is the whole beta core, and
its center is the actual beta center, on the original subgroup images. -/
theorem original_borel_elementary_span_and_center :
    betaSpan ((stabilizer F₀ (base F₀ true)).map (G₀).subtype)
      ((Z F₀ (base F₀ false)).map (G₀).subtype) = (Q F₀ (base F₀ true)).map (G₀).subtype ∧
      centerIn ((Q F₀ (base F₀ true)).map (G₀).subtype) = (Z F₀ (base F₀ true)).map (G₀).subtype := by
  obtain ⟨m,hm,mark⟩ := original_borel_elementary_linear_beta h hc hb hcomm Ma Mb helem
  exact original_linear_beta_span_and_center h hc hb hcomm Ma hm mark

/-- The actual Chapter 14 tree-path inputs follow from the elementary
full-Borel branch, with both linear markings and the paths constructed. -/
theorem original_elementary_tree_path_profile :
    BasedPathTransitive (X := (reducedAmalgam L₀ S₀).Universal)
      (sourceGraph (reducedAmalgam L₀ S₀)) 5 ∧
      ∀ {x y} (q : (sourceGraph (reducedAmalgam L₀ S₀)).Walk x y),
        q.IsPath → q.length = 5 →
          Odd (Nat.card (pathFixer (X := (reducedAmalgam L₀ S₀).Universal) q)) := by
  obtain ⟨m,hm,mark⟩ := original_borel_elementary_linear_beta h hc hb hcomm Ma Mb helem
  exact original_linear_beta_tree_path_profile h hc hb hcomm Ma hm mark

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
