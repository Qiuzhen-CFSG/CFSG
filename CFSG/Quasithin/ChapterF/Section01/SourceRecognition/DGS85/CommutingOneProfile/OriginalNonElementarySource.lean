module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SourceSuzukiExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalUnitarySource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedElementaryProfile

/-!
# The nonelementary Chapter 11 branch on the full original Borel

The actual quotient O₂(B)/Q_beta maps isomorphically to a local Sylow.
Its nonelementarity leaves Suzuki or one of the two unitary covers. The
path-free Suzuki exclusion removes every Suzuki parameter, so the unitary
marking and its positive fixed-field degree are constructed from the branch
hypothesis. The existing marked calculation then proves the field ratio,
exact core orders, full kernel depths, special beta core and equivariant
natural alpha quotient, with r=4, s=5 and odd long-path fixers.

The final application supplies the Chapter 14 path inputs on the literal
universal cover of the full-Borel amalgam. The earlier-local record and all
path and escape premises are discharged. The actual local quotient catalogue
is retained at both endpoints; no marked amalgam recognition is asserted.
All quotients, subgroup images, and actions use the original inclusion.
Source: DGS, Groups and Graphs (1985), (11.8), pp.175--177,
and its universal-cover application (14.1), p.210.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open Reduction NoncommutingProfile
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

private theorem nonElementary_of_mapped_quotient {H : Type*} [Group H]
    (R N : Subgroup H) (hNR : N ≤ R) (f : H →* G) (hf : Function.Injective f)
    [(N.subgroupOf R).Normal]
    (hne : ∃ hn : ((N.map f).subgroupOf (R.map f)).Normal, letI := hn
      ¬ IsElementaryAbelian 2 (R.map f ⧸ (N.map f).subgroupOf (R.map f))) :
    ¬ IsElementaryAbelian 2 (R ⧸ N.subgroupOf R) := by
  intro he
  obtain ⟨hn,hne⟩ := hne
  let := hn
  let := he
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
  exact hne (IsElementaryAbelian.of_surjective eq.toMonoidHom eq.surjective)

/-- The nonelementary branch selects a genuine unitary marking on the
original beta quotient; no path or alpha-marking premise is required. -/
theorem original_reduced_nonElementary_unitary_beta
    (h : HypothesisF11 L₀ S₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (Ma : IsRankOneModel ((graphLocalGroup F₀ a).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((graphLocalGroup F₀ b).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ b).map (G₀).subtype)))
    (hne : ∃ hN : (((Q F₀ b).map (G₀).subtype).subgroupOf
        (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype)).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 ((((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype) ⧸
        ((Q F₀ b).map (G₀).subtype).subgroupOf
          (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype))) :
    ∃ m, 0 < m ∧
      (ClassicalGroup.IsPSU ((graphLocalGroup F₀ b).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ b).map (G₀).subtype)) 3 (2^m) ∨
       IsSU ((graphLocalGroup F₀ b).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ b).map (G₀).subtype)) 3 (2^m)) := by
  let d := reducedFullEarlierLocalTheorems h
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
  have hn := nonElementary_of_mapped_quotient R (Q F₀ b) hQR
    (G₀).subtype (G₀).subtype_injective hne
  rcases reduced_nonElementary_beta_selection h d (source_critical_one_adjacent hc hb)
    (Mb.of_equiv eqb) ⟨hN,hn⟩ with ⟨m,⟨es⟩⟩ | ⟨m,hm,mark⟩
  · exact (original_reduced_suzuki_beta_exclusion h hc hb hcomm Ma m
      (eqb.symm.trans es)).elim
  · refine ⟨m,hm,?_⟩
    rcases mark with hm | ⟨E,hE,hfin,J,hcard,hconj,⟨e⟩⟩
    · exact Or.inl (hm.of_mulEquiv eqb.symm)
    · exact Or.inr ⟨E,hE,hfin,J,hcard,hconj,⟨eqb.symm.trans e⟩⟩

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
    (hne : ∃ hN : (((Q (Reduction.reducedFamily L₀ S₀)
        (base (Reduction.reducedFamily L₀ S₀) true)).map (Reduction.G₀ L₀ S₀).subtype).subgroupOf
        (twoCore (commonBorel L₀ S₀))).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
        ((Q (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map
          (Reduction.G₀ L₀ S₀).subtype).subgroupOf (twoCore (commonBorel L₀ S₀))))

include h hc hb hcomm Ma Mb hne

/-- The literal quotient of the full original Borel two-core selects PSU₃
or SU₃, with every positive field degree retained. -/
theorem original_borel_nonElementary_unitary_beta :
    ∃ m, 0 < m ∧
      (ClassicalGroup.IsPSU ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype)) 3 (2^m) ∨
       IsSU ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype)) 3 (2^m)) := by
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
  apply original_reduced_nonElementary_unitary_beta h hc hb hcomm Ma Mb
  change ∃ hN : (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf (R.map (G₀).subtype)).Normal,
    letI := hN
    ¬ IsElementaryAbelian 2 (R.map (G₀).subtype ⧸
      ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf (R.map (G₀).subtype))
  rw [hmap]
  exact hne

/-- Source (11.8) field, order and path clauses from its actual nonelementary
full-Borel branch. The selected unitary marking is an output. -/
theorem original_borel_nonElementary_orders_and_paths :
    ∃ m, 0 < m ∧
      (ClassicalGroup.IsPSU ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype)) 3 (2^m) ∨
       IsSU ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype)) 3 (2^m)) ∧
      ClassicalGroup.IsPSL ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype)) 2 (2^(2*m)) ∧
      Nat.card ((Q F₀ (base F₀ true)).map (G₀).subtype) = 2^(7*m) ∧
      Nat.card (twoCore (commonBorel L₀ S₀)) = 2^(10*m) ∧
      Nat.card ((Q F₀ (base F₀ false)).map (G₀).subtype) = 2^(8*m) ∧
      ((Z F₀ (base F₀ false)).map (G₀).subtype).relIndex
        ((Q F₀ (base F₀ false)).map (G₀).subtype) = 2^(4*m) ∧
      HasSourcePathParameters (P := fun i => (P₀ L₀ S₀ i).subgroupOf G₀) 4 5 ∧
      (∀ x : Vertex F₀, RootPathTransitive (graph F₀) G₀ x 5) ∧
      ∀ {x y : Vertex F₀} (q : (graph F₀).Walk x y), IsSourcePath q → 5 ≤ q.length →
        Odd (Nat.card ((pathFixer (X := G₀) q).map (G₀).subtype)) := by
  obtain ⟨m,hm,mark⟩ := original_borel_nonElementary_unitary_beta h hc hb hcomm Ma Mb hne
  obtain ⟨hQb,hS,hQa,hindex⟩ := original_borel_unitary_core_orders_from_marking h hc hb hcomm Ma hm mark
  exact ⟨m,hm,mark,(original_unitary_field_and_valences h hc hb hcomm Ma hm mark).1,
    hQb,hS,hQa,hindex,original_borel_unitary_source_path_profile_from_marking h hc hb hcomm Ma hm mark⟩

/-- The selected nonelementary row supplies the full kernel depths, special
beta core, and equivariant natural alpha quotient on the original subgroup
images. No unitary marking or path action is assumed. -/
theorem original_borel_nonElementary_structural_profile :
    ∃ m, 0 < m ∧
      (ClassicalGroup.IsPSU ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype)) 3 (2^m) ∨
       IsSU ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype)) 3 (2^m)) ∧
      ((ballKernel F₀ (base F₀ false) 2).map (G₀).subtype = ⊥ ∧
      (ballKernel F₀ (base F₀ true) 3).map (G₀).subtype = ⊥ ∧
      ((ballKernel F₀ (base F₀ true) 2).map (G₀).subtype).pCoreIn 2 =
        (Z F₀ (base F₀ true)).map (G₀).subtype ∧
      Nat.card (((ballKernel F₀ (base F₀ true) 2).map (G₀).subtype).pCoreIn 2) = 2^m ∧
      (ballKernel F₀ (base F₀ true) 2).map (G₀).subtype ≠ ⊥) ∧
      (let R := (Q F₀ (base F₀ true)).map (G₀).subtype
        let C := (Z F₀ (base F₀ true)).map (G₀).subtype
        Nat.card R = 2^(7*m) ∧ Nat.card C = 2^m ∧
          centerIn R = C ∧ ⁅R,R⁆ = C ∧ (frattini R).map R.subtype = C ∧
          centerIn (twoCore (commonBorel L₀ S₀)) = C ∧
          (∀ x ∈ R, x^4 = 1) ∧ ⁅⁅R,R⁆,R⁆ = ⊥ ∧ ⁅R,R⁆ ≠ ⊥ ∧
          ∃ hN : (C.subgroupOf R).Normal, letI := hN
            IsElementaryAbelian 2 (R ⧸ C.subgroupOf R)) ∧
      (let R := (Q F₀ (base F₀ false)).map (G₀).subtype
        let C := (Z F₀ (base F₀ false)).map (G₀).subtype
        let L := (graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype
        (frattini R).map R.subtype = C ∧
          ∃ hN : (C.subgroupOf R).Normal, letI := hN
            ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
              Nat.card k = 2^(2*m) ∧
              ∃ ea : (L ⧸ pCore 2 L) ≃* SL(2,k),
                ∃ e : (R ⧸ C.subgroupOf R) ≃* Multiplicative (Fin 2 → k),
                  ∀ (l : L) (x y : R), (y : G) = (l : G) * (x : G) * (l : G)⁻¹ →
                    (e (QuotientGroup.mk' (C.subgroupOf R) y)).toAdd =
                      Matrix.mulVec (ea (QuotientGroup.mk' (pCore 2 L) l)).val
                        (e (QuotientGroup.mk' (C.subgroupOf R) x)).toAdd) := by
  obtain ⟨m,hm,mark⟩ := original_borel_nonElementary_unitary_beta h hc hb hcomm Ma Mb hne
  exact ⟨m,hm,mark,
    original_borel_unitary_second_kernel_profile_from_marking h hc hb hcomm Ma hm mark,
    original_borel_unitary_beta_layers_from_marking h hc hb hcomm Ma hm mark,
    original_borel_unitary_alpha_natural_quotient_from_marking h hc hb hcomm Ma hm mark⟩

/-- The actual Chapter 14 universal-tree path inputs follow from the
nonelementary full-Borel branch with its unitary marking constructed. -/
theorem original_nonElementary_tree_path_profile :
    BasedPathTransitive (X := (reducedAmalgam L₀ S₀).Universal)
      (sourceGraph (reducedAmalgam L₀ S₀)) 5 ∧
      ∀ {x y} (q : (sourceGraph (reducedAmalgam L₀ S₀)).Walk x y),
        q.IsPath → q.length = 5 →
          Odd (Nat.card (pathFixer (X := (reducedAmalgam L₀ S₀).Universal) q)) := by
  obtain ⟨m,hm,mark⟩ := original_borel_nonElementary_unitary_beta h hc hb hcomm Ma Mb hne
  exact original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
