module
public import CFSG.Quasithin.Chapter14.Section09.ShortRoute.MixedSize
import all CFSG.Quasithin.Chapter14.Section09.ShortRoute.MixedSize
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourMarkedSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReversedElementarySource
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MixedZeroCore.DGSProfiles

/-!
# Original Hall--Janko recognition in the mixed noncommuting branch

For a literal F.1.1 pair with A₅ and S₃ quotient markings, the existing
critical-pair argument forces noncommuting distance two and the cubic/quintic
orientation. The Borel-core reduction preserves the entire reduced graph.
Apply the strict (10.10) exclusion on that reduction, where the full quintic
quotient is A₅, to obtain D_alpha = Z_alpha without a profile assumption.

The checked field-four comparison then supplies one compatible reduced J₂
amalgam isomorphism. Its native Borel correction makes both endpoint maps
commute with the same middle map. Restore the original pair, including its
possible outer involution, to obtain J₂ or Aut(J₂) with the whole original
Borel. The final theorem applies these maps to the literal H, BT and AT of
the Chapter 10 cubic-factor consumer.

The internal import reuses the field markings and Borel-swap proof from the
companion size module; no private identifier occurs in a public statement.
The other source profile branches and the general classification assembly
remain separate. No isomorphism of the original ambient group is asserted.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(10.9)--(10.10), pp.162--165, and (15.3), pp.229--231;
Aschbacher--Smith F.1.12(I), printed pp.262--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.ShortRoute
open Reduction NoncommutingProfile NoncommutingProfile.Reduction
open OriginalExtension SuzukiContainment
variable {G : Type*} [Group G] [Finite G] {K U S : Subgroup G}
local notation "F" => reducedFamily ![U,K] S
local notation "α" => base F false
local notation "β" => base F true

/-- Construct the compatible Hall--Janko marking in the normalized mixed
noncommuting branch, including the whole middle group and both squares. -/
theorem mixed_base_reduced_j2_iso
    (h : HypothesisF11 ![U,K] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (hn : commonBorel ![U,K] S ≤ normalizer (S : Set G))
    {u t : Vertex F} (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β) :
    Nonempty (Iso (reducedAmalgam ![U,K] S).reverse
      GreenBook.HallJanko.j2Model.toMarking.amalgam) := by
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ :=
    reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have halg : alg = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2
  have hnot := reduced_graph_core_obstruction h α β hab
  have hD := mixed_base_intersection_eq_center h eK eU hn hc hne hb hβu ht htne
  exact original_bTwo_field_four_reduced_iso h hb c hactor hcentral ht htne hcomm hnot
    (field_markings eK eU true) hD (LinearEquiv.refl _ _)
    (by exact GaloisField.card 2 2 (by decide))

/-- The actual noncommuting mixed branch constructs the reduced J2 amalgam
in the original A5-first orientation. No exceptional selection is assumed. -/
theorem mixed_noncommuting_reduced_j2_iso
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {a a' : Vertex (reducedFamily ![K,U] S)}
    (hc : IsCriticalPair (reducedFamily ![K,U] S) a a')
    (hne : ⁅Z (reducedFamily ![K,U] S) a,Z (reducedFamily ![K,U] S) a'⁆ ≠ ⊥) :
    Nonempty (Iso (reducedAmalgam ![K,U] S)
      GreenBook.HallJanko.j2Model.toMarking.amalgam) := by
  let R := twoCore (commonBorel ![K,U] S)
  have hR : HypothesisF11 ![K,U] R := h.restrict_to_borel_core
  have hcore : reducedSylow ![K,U] R = R := reduced_borel_core h
  have hP (i : Fin 2) : P₀ ![K,U] R i = P₀ ![K,U] S i := by
    rw [P₀_eq_source hR i,P₀_eq_source h i,hcore]
    rfl
  have hG : G₀ ![K,U] R = G₀ ![K,U] S := by
    rw [G₀,hP 0,hP 1]
    rfl
  have hex : ∃ v w : Vertex (reducedFamily ![K,U] R),
      IsCriticalPair (reducedFamily ![K,U] R) v w ∧
      ⁅Z (reducedFamily ![K,U] R) v,Z (reducedFamily ![K,U] R) w⁆ ≠ ⊥ := by
    unfold reducedFamily
    rw [hG]
    have hf : (fun i : Fin 2 => (P₀ ![K,U] R i).subgroupOf (G₀ ![K,U] S)) =
        (fun i : Fin 2 => (P₀ ![K,U] S i).subgroupOf (G₀ ![K,U] S)) :=
      funext fun i => congrArg (fun A : Subgroup G => A.subgroupOf (G₀ ![K,U] S)) (hP i)
    rw [hf]
    exact ⟨a,a',hc,hne⟩
  obtain ⟨v,w,hcv,hnv⟩ := hex
  have hb := reduced_intrinsic_noncommuting_bound hR hcv hnv
  rcases hb with hb | hb
  · exact (MixedDGS.noncommuting_distance_one_false hR eK eU hcv hnv hb).elim
  obtain ⟨u,hcu,hnu,hβu⟩ := mixed_reversed_noncommuting_base hR eK eU hcv hnv hb
  let F₁ := reducedFamily ![U,K] R
  have hval : 3 ≤ Nat.card ((graph F₁).neighborSet (base F₁ false)) := by
    rw [card_neighbors_of_indices F₁ (fun i => ((F₁ (!i)).subgroupOf (F₁ i)).index) (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple hR.swap) (reduced_vertex_sylow hR.swap) false
  obtain ⟨t,ht,htne⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph F₁).neighborSet (base F₁ false))
    (by rw [←Nat.card_coe_set_eq]; omega) (base F₁ true)
  have hn : commonBorel ![U,K] R ≤ normalizer (R : Set G) := by
    rw [commonBorel_swap]
    exact (reduced_commonBorel_le h).trans
      ((commonBorel ![K,U] S).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hJ := mixed_base_reduced_j2_iso hR.swap eK eU hn hcu hnu
    ((pair_b_swap K U R).trans hb) hβu ht htne
  change Nonempty (Iso (reducedAmalgam ![U,K] R).reverse
    GreenBook.HallJanko.j2Model.toMarking.amalgam) at hJ
  have hRS : reducedSylow ![U,K] S = R := by
    change twoCore (commonBorel ![U,K] S) = R
    rw [commonBorel_swap]
  have hRR : reducedSylow ![U,K] R = R := by
    change twoCore (commonBorel ![U,K] R) = R
    rw [commonBorel_swap]
    exact hcore
  have hJ' : Nonempty (Iso (reducedAmalgam ![U,K] S).reverse
      GreenBook.HallJanko.j2Model.toMarking.amalgam) := by
    exact Eq.mp (congrArg (fun T : Subgroup G =>
      Nonempty (Iso (originalAmalgam ![U,K] T).reverse
        GreenBook.HallJanko.j2Model.toMarking.amalgam)) (hRR.trans hRS.symm)) hJ
  obtain ⟨e⟩ := hJ'
  exact ⟨(CommutingOneProfile.ReversedElementary.reducedAmalgamSwap K U S).reverse.trans e⟩

/-- Restore the full original Borel and both endpoint maps, including the
possible outer involution, for the actual noncommuting mixed source pair. -/
theorem mixed_noncommuting_original_j2_or_autJ2_iso
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {a a' : Vertex (reducedFamily ![K,U] S)}
    (hc : IsCriticalPair (reducedFamily ![K,U] S) a a')
    (hne : ⁅Z (reducedFamily ![K,U] S) a,Z (reducedFamily ![K,U] S) a'⁆ ≠ ⊥) :
    Nonempty (Iso (originalAmalgam ![K,U] S)
      GreenBook.HallJanko.j2Model.toMarking.amalgam) ∨
    Nonempty (Iso (originalAmalgam ![K,U] S)
      GreenBook.HallJanko.autJ2Model.toMarking.amalgam) := by
  obtain ⟨e⟩ := mixed_noncommuting_reduced_j2_iso h eK eU hc hne
  by_cases hs : S = reducedSylow ![K,U] S
  · exact Or.inl ⟨(NativeRestoration.originalIsoReduced hs).trans e⟩
  · obtain ⟨E,_,_,_⟩ := JankoTwo.SplitComparison.original_autJ2_iso h 0 1 e hs
    exact Or.inr ⟨E⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.ShortRoute

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Subgroup Theory.GroupTheory RankTwoAmalgam Chapter3.Section02 MixedZeroCore
open ChapterF.Source ChapterF.Source.DGS85 ChapterF.Source.DGS85.OriginalExtension
open ChapterF.GreenBook Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- The noncommuting source branch constructs both endpoint maps on H and
AT and the whole BT map, with both commuting inclusion squares. -/
theorem mixed_cubic_factor_j2_or_autJ2_of_noncommuting
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥)
    {a a' : Vertex (Reduction.reducedFamily ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) a a')
    (hne : ⁅Z (Reduction.reducedFamily ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) a,
      Z (Reduction.reducedFamily ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) a'⁆ ≠ ⊥) :
    ∃ hBH : B ⊔ (T : Subgroup G) ≤ H,
      Nonempty (Iso
        (ofSubgroups H (B ⊔ (T : Subgroup G)) (A ⊔ (T : Subgroup G)) hBH (sup_le_sup_right hBA _))
        HallJanko.j2Model.toMarking.amalgam) ∨
      Nonempty (Iso
        (ofSubgroups H (B ⊔ (T : Subgroup G)) (A ⊔ (T : Subgroup G)) hBH (sup_le_sup_right hBA _))
        HallJanko.autJ2Model.toMarking.amalgam) := by
  obtain ⟨hf,_,_,_,hb,hp,hAT⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  have hmodel := ShortRoute.mixed_noncommuting_original_j2_or_autJ2_iso hf eK hU.2.2.2.2.some hc hne
  have hBH : B ⊔ (T : Subgroup G) ≤ H := by
    have hh := commonBorel_le_parabolic (L := ![(pResidual 2 H).map H.subtype,U])
      (S := (T : Subgroup G)) 0
    simpa only [hb,hp] using hh
  let f : Iso (originalAmalgam ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G))
      (ofSubgroups H (B ⊔ (T : Subgroup G)) (A ⊔ (T : Subgroup G)) hBH (sup_le_sup_right hBA _)) := {
    left := MulEquiv.subgroupCongr hp
    middle := MulEquiv.subgroupCongr hb
    right := MulEquiv.subgroupCongr hAT
    left_commutes := fun _ => Subtype.ext rfl
    right_commutes := fun _ => Subtype.ext rfl }
  refine ⟨hBH,?_⟩
  rcases hmodel with he | he
  · obtain ⟨e⟩ := he
    exact Or.inl ⟨f.symm.trans e⟩
  · obtain ⟨e⟩ := he
    exact Or.inr ⟨f.symm.trans e⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
