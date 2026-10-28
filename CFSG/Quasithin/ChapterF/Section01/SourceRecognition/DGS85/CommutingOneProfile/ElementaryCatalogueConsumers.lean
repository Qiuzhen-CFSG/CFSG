module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryMarkedProfile

/-!
# Elementary source consumers with the beta catalogue discharged

Transport the elementary quotient of the literal reduced parabolic core
to the original graph-core image in O₂(B). The exceptional order-144
obstruction then supplies the beta catalogue. Applying the existing
Chapter 11 construction gives the complete U₄ profile, both universal-tree
path premises and the marked reduced comparison with only alpha's catalogue
retained. Nonsolvability of the original alpha parabolic supplies that last
catalogue in the final specialization; beta need not be nonsolvable.

The unrestricted alpha exclusion remains open. The marked quotient, split
data and rotation order in the comparison remain Chapter 14 inputs.
Source: DGS, Groups and Graphs (1985), (11.7), pp.174--175,
(14.1), p.210, and Theorem D, p.224; Aschbacher--Smith F.1.1 and F.1.12.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open Reduction Theory.GroupTheory FongSeitzBinary
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "G₀" => Reduction.G₀ L S

open Theory.GroupTheory.RankTwoAmalgam OriginalExtension SuzukiContainment NoncommutingProfile
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
local notation "R" => reducedSylow L S
local notation:max "M" b:arg => (Subgroup.map (Subgroup.subtype G₀) (graphLocalGroup F (base F b)))

variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S) = 1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),Z (reducedFamily L S) (base (reducedFamily L S) true)⁆ = ⊥)
    (Ma : IsRankOneModel ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) false)).map (Reduction.G₀ L S).subtype ⧸
      pCore 2 ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) false)).map (Reduction.G₀ L S).subtype)))
    (helem : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := reducedSylow L S) 1
      IsElementaryAbelian 2 (reducedSylow L S ⧸
        ((parabolic L (reducedSylow L S) 1).pCoreIn 2).subgroupOf (reducedSylow L S)))

include h hc hb hcomm Ma helem

omit hc hb hcomm Ma in
/-- The elementary quotient of the reduced parabolic core supplies the actual
beta rank-one catalogue through the full original Borel. -/
theorem original_parabolic_elementary_beta_model :
    IsRankOneModel (M true ⧸ pCore 2 (M true)) := by
  have he : ∃ hN : (((Q F (base F true)).map (G₀).subtype).subgroupOf R).Normal,
      letI := hN
      IsElementaryAbelian 2 (R ⧸ ((Q F (base F true)).map (G₀).subtype).subgroupOf R) := by
    have hq : (Q F (base F true)).map (G₀).subtype = (parabolic L R 1).pCoreIn 2 :=
      (reduced_base_Q_map h true).trans (reduced_parabolic_core h 1).symm
    rw [hq]
    exact ⟨FongSeitzBinary.QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := R) 1,helem⟩
  exact original_borel_elementary_beta_model (G := G) (L := L) (S := S) h he

/-- The complete U₄ profile needs only the alpha catalogue in the elementary
branch. The actual edge quotient supplies the beta catalogue. -/
theorem original_borel_elementary_marked_profile_of_alpha_model :
    ∃ m : ℕ, 0 < m ∧
      ∃ (kₐ : Type) (_ : Field kₐ) (_ : Finite kₐ) (_ : CharP kₐ 2)
        (kᵦ : Type) (_ : Field kᵦ) (_ : Finite kᵦ) (_ : CharP kᵦ 2),
        Nat.card kₐ = 2^(2*m) ∧ Nat.card kᵦ = 2^m ∧
          Nonempty (Assembly.UnitaryFourSource.Profile L R kₐ kᵦ false) := by
  exact original_borel_elementary_marked_profile h hc hb hcomm Ma
    (original_parabolic_elementary_beta_model h helem) helem

/-- Both Chapter 14 path premises, with the beta catalogue discharged on the
literal full-Borel quotient. -/
theorem original_elementary_tree_path_profile_of_alpha_model :
    BasedPathTransitive
        (X := (reducedAmalgam L S).Universal)
        (sourceGraph (reducedAmalgam L S)) 5 ∧
      ∀ {x y} (q : (sourceGraph
          (reducedAmalgam L S)).Walk x y),
        q.IsPath → q.length = 5 →
          Odd (Nat.card (pathFixer
            (X := (reducedAmalgam L S).Universal) q)) := by
  have he : ∃ hN : (((Q F (base F true)).map (G₀).subtype).subgroupOf R).Normal,
      letI := hN
      IsElementaryAbelian 2 (R ⧸ ((Q F (base F true)).map (G₀).subtype).subgroupOf R) := by
    have hq : (Q F (base F true)).map (G₀).subtype = (parabolic L R 1).pCoreIn 2 :=
      (reduced_base_Q_map h true).trans (reduced_parabolic_core h 1).symm
    rw [hq]
    exact ⟨QuadrangleStructure.original_core_normal_in_sylow 1,helem⟩
  exact original_elementary_tree_path_profile h hc hb hcomm Ma
    (original_parabolic_elementary_beta_model h helem) he

/-- The constructed elementary profile feeds the marked U₄ comparison;
only alpha still needs a catalogue input. -/
theorem original_elementary_reduced_comparison_of_alpha_model
    {X : Type*} [Group X] {endpoints : Fin 2 → Subgroup X}
    (quot : MarkedQuotient endpoints)
    (e : Iso (reducedAmalgam L S) quot.standardAmalgam)
    (split : SplitData quot.tits) (hrot : rotationOrder quot = 4) :
    ∃ (m : ℕ) (hm : 0 < m), Nonempty (Iso (reducedAmalgam L S)
      (UnitaryFourNative.amalgam m hm false)) := by
  obtain ⟨m,hm,kₐ,hFa,hfina,hcha,kᵦ,hFb,hfinb,hchb,_,hkb,⟨profile⟩⟩ :=
    original_borel_elementary_marked_profile_of_alpha_model h hc hb hcomm Ma helem
  let : NeZero m := ⟨by omega⟩
  exact ⟨m,hm,⟨Assembly.UnitaryFourSource.reducedComparison h quot e split hrot false profile m hkb⟩⟩


omit Ma in
/-- Nonsolvability is needed only at alpha: the elementary beta quotient
discharges its own catalogue, including the exceptional enlargement. -/
theorem original_elementary_reduced_comparison_of_nonsolvable_alpha
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    {X : Type*} [Group X] {endpoints : Fin 2 → Subgroup X}
    (quot : MarkedQuotient endpoints)
    (e : Iso (reducedAmalgam L S) quot.standardAmalgam)
    (split : SplitData quot.tits) (hrot : rotationOrder quot = 4) :
    ∃ (m : ℕ) (hm : 0 < m), Nonempty (Iso (reducedAmalgam L S)
      (UnitaryFourNative.amalgam m hm false)) := by
  have Ma : IsRankOneModel (M false ⧸ pCore 2 (M false)) := by
    rw [reduced_graphLocalGroup_image h false]
    change IsRankOneModel (enlargedEndpoint L S 0 ⧸ pCore 2 (enlargedEndpoint L S 0))
    rcases reduced_enlargement_rankOne_or_small_unitary h 0 with hm | hp | hs
    · exact hm
    · exact (hns (parabolic_solvable_of_projective_unitary_two h 0 hp)).elim
    · exact (hns (parabolic_solvable_of_special_unitary_two h 0 hs)).elim
  exact original_elementary_reduced_comparison_of_alpha_model (L := L) (S := S)
    h hc hb hcomm Ma helem quot e split hrot

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
