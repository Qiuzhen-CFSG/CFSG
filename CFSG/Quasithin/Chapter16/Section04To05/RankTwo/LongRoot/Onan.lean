module
public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.Action
public import Theory.Representation.GoldschmidtONan.Consequences
public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.Irreducible
public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.CoverObstruction
/-!
# Applying all four Goldschmidt--O'Nan alternatives

An actual subgroup of the elementary abelian `V` is converted to its binary
subspace. Conjugation and linear image agree, and orbit-stabilizer identifies
the fixed-space orbit cardinality with the relative index of its actual
ambient normalizer. The image of the parabolic has fixed space `C_V(P)`.

The source mover excludes the singleton alternative. The swapped alternative
puts `T_C` in `X`; after the cover table rules out the diagram case, its index
two contradicts the ambient Sylow index. The larger two-power alternative
contradicts `|T : N_T(X)| ≤ 2`. The order-21 alternative forces `V ≤ X` by
the proved eight-element action lemma and is excluded by the intrinsic cover
bounds and the Frattini argument.

`no_onan_action_of_cover_bounds` is this deduction, conditional on construction
of the displayed geometry and cover bounds. It is not a proof that an arbitrary
root involution constructs those premises. The exact four-case conclusion of
GLS96 C.14.2 is retained as the permitted earlier source input.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
Lemma 16.5.13, printed pp.1201--1202; GLS96 C.14.1--14.2,
`refs/KGroup/GLS2/ChapterC.tex`.
-/

@[expose] public section
open Subgroup
open Representation Representation.BinaryOffender Representation.GoldschmidtONan
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
variable {G : Type*} [Group G]
/-- The actual subgroup intersection with `V`, viewed as a binary subspace. -/
noncomputable def linearSpace (V C : Subgroup G) [IsElementaryAbelian 2 V] :
    Submodule (ZMod 2) (Additive V) :=
  AddSubgroup.toZModSubmodule 2 ((C.subgroupOf V).toAddSubgroup)

/-- The image of the actual parabolic (or other normalizing subgroup). -/
def inducedActor (V X P : Subgroup G) : Subgroup (action V X).range :=
  (P.subgroupOf (actingGroup V X)).map (action V X).rangeRestrict

/-- Its fixed space is the actual centralizer intersection. -/
theorem fixedSpace_inducedActor {V X P : Subgroup G} [IsElementaryAbelian 2 V]
    (hP : P ≤ actingGroup V X) :
    fixedSpace (representation V X) (inducedActor V X P) =
      linearSpace V (V ⊓ centralizer (P : Set G)) := by
  ext v
  constructor
  · intro hv
    refine ⟨v.toMul.property, ?_⟩
    intro p hp
    have he := hv ⟨(action V X).rangeRestrict ⟨p, hP hp⟩,
      ⟨⟨p, hP hp⟩, hp, rfl⟩⟩
    have he' := congrArg (fun w : Additive V => (w.toMul : G)) he
    exact mul_inv_eq_iff_eq_mul.mp he'
  · intro hv
    rintro ⟨a, ⟨m, hm, rfl⟩⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hv.2 m hm)

/-- Subgroups contained in `V` are determined by their binary subspaces. -/
theorem linearSpace_injective {V C D : Subgroup G} [IsElementaryAbelian 2 V]
    (hC : C ≤ V) (hD : D ≤ V)
    (he : linearSpace V C = linearSpace V D) : C = D := by
  ext c
  constructor
  · intro hc
    have hm : Additive.ofMul (⟨c, hC hc⟩ : V) ∈ linearSpace V D := he ▸ hc
    exact hm
  · intro hd
    have hm : Additive.ofMul (⟨c, hD hd⟩ : V) ∈ linearSpace V C := he.symm ▸ hd
    exact hm

/-- Linear image is ambient conjugation for the actual induced representation. -/
theorem linearSpace_map {V X C : Subgroup G} [IsElementaryAbelian 2 V]
    (hC : C ≤ V) (m : actingGroup V X) :
    (linearSpace V C).map (representation V X ((action V X).rangeRestrict m)) =
      linearSpace V (C.conjBy m) := by
  ext v
  constructor
  · rintro ⟨w, hw, he⟩
    exact ⟨(w.toMul : G), hw, congrArg (fun w : Additive V => (w.toMul : G)) he⟩
  · rintro ⟨w, hw, he⟩
    refine ⟨Additive.ofMul (⟨w, hC hw⟩ : V), hw, ?_⟩
    exact congrArg Additive.ofMul (Subtype.ext he)

/-- Every translate by the acting group stays inside `V`. -/
theorem conjugate_le_space {V X C : Subgroup G}
    (hC : C ≤ V) (m : actingGroup V X) : C.conjBy m ≤ V := by
  exact (map_mono hC).trans_eq (mem_normalizer_iff_map_conj_eq.mp m.property.1)

/-- Equality of image subspaces detects equality of the actual conjugate subgroups. -/
theorem linearSpace_map_eq_iff {V X C D : Subgroup G} [IsElementaryAbelian 2 V]
    (hC : C ≤ V) (hD : D ≤ V) (m : actingGroup V X) :
    (linearSpace V C).map (representation V X ((action V X).rangeRestrict m)) =
      linearSpace V D ↔ C.conjBy m = D := by
  rw [linearSpace_map hC]
  exact ⟨linearSpace_injective (conjugate_le_space hC m) hD, (fun h => congrArg (fun D => linearSpace V D) h)⟩

/-- The fixed-space orbit has the index of the actual ambient subgroup normalizer. -/
theorem fixedOrbit_card_eq_relIndex [Finite G]
    {V X C : Subgroup G} [IsElementaryAbelian 2 V]
    {S : Subgroup (action V X).range}
    (hC : C ≤ V) (hfixed : fixedSpace (representation V X) S = linearSpace V C) :
    Nat.card (fixedOrbit (representation V X) S) =
      (normalizer (C : Set G)).relIndex (actingGroup V X) := by
  let ρ := representation V X
  let A := (action V X).range
  let π := (action V X).rangeRestrict
  let F := fixedSpace ρ S
  let : MulAction A (Submodule (ZMod 2) (Additive V)) := {
    smul a W := W.map (ρ a)
    one_smul W := by
      change W.map (ρ 1) = W
      rw [map_one]; exact Submodule.map_id W
    mul_smul a b W := by
      change W.map (ρ (a * b)) = (W.map (ρ b)).map (ρ a)
      rw [← Submodule.map_comp, map_mul]; rfl }
  have horbit : MulAction.orbit A F = fixedOrbit ρ S := by
    ext W
    rw [MulAction.mem_orbit_iff]
    rfl
  have hstab : MulAction.stabilizer A F = subspaceStabilizer ρ F := by
    ext a
    exact (mem_subspaceStabilizer_iff_map F a).symm
  have hcomap : (subspaceStabilizer ρ F).comap π =
      (normalizer (C : Set G)).subgroupOf (actingGroup V X) := by
    ext m
    rw [mem_comap, mem_subspaceStabilizer_iff_map]
    rw [show F = linearSpace V C from hfixed]
    rw [linearSpace_map_eq_iff hC hC]
    exact mem_normalizer_iff_map_conj_eq.symm
  have hi := MulAction.index_stabilizer A F
  rw [hstab, horbit] at hi
  rw [Nat.card_coe_set_eq]
  rw [← hi, ← (subspaceStabilizer ρ F).index_comap_of_surjective
    (action V X).rangeRestrict_surjective, hcomap]
  rfl


private theorem binary_card {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E] :
    Nat.card E = 2 ^ Module.finrank (ZMod 2) E := by
  let := Fintype.ofFinite E
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-- The three intrinsic facts still required of the covered residual.
This is an output contract for that model calculation, not its proof. -/
def CoveredImageBounds (V X : Subgroup G) : Prop :=
  V = coreFrattini X ∧
  Nat.Coprime 7 (Nat.card (topAction (residualAction V X)).range) ∧
  Nat.Coprime 7 (Nat.card ((topAction (residualAction V X)).ker.map
    (sectionAction (residualAction V X))))

/-- Exclude all four alternatives on the actual normalizer action, once the
root construction and intrinsic cover calculation supply the displayed inputs. -/
theorem no_onan_action_of_cover_bounds [Finite G]
    {T : Sylow 2 G} {L X Z : Subgroup G} [IsElementaryAbelian 2 (space T X)]
    (S : Subgroup (action (space T X) X).range)
    (hinput : Input (representation (space T X) X) S)
    (halt : Alternatives (representation (space T X) X) S)
    (hfixed : fixedSpace (representation (space T X) X) S =
      linearSpace (space T X) (commutingSylow T L))
    (hmoved : Representation.RegularCyclicNormalClosure.displacementSpan
      (representation (space T X) X) S ⊤ = linearSpace (space T X) Z)
    (hXL : X ≤ L) (hZ : Z ≠ ⊥) (hZV : Z ≤ space T X) (hZX : Z ≤ X)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hbound : ((T : Subgroup G) ⊓ normalizer (X : Set G)).relIndex T ≤ 2)
    (g : G) (hg : g ∈ actingGroup (space T X) X)
    (hmove : g ∉ normalizer (commutingSylow T L : Set G))
    (hcoverT : commutingSylow T L ≤ X → (T : Subgroup G) ≤ normalizer (X : Set G))
    (hcover : space T X ≤ X → CoveredImageBounds (space T X) X) : False := by
  let V := space (T : Subgroup G) X
  let C := commutingSylow T L
  let ρ := representation V X
  let π := (action V X).rangeRestrict
  have hCV : C ≤ V := le_inf inf_le_left (inf_le_right.trans (centralizer_le hXL))
  have horbit := fixedOrbit_card_eq_relIndex hCV hfixed
  rcases halt with hs | hs | hs | he
  · have hfix := hs.2 (π ⟨g, hg⟩)
    rw [hfixed] at hfix
    exact hmove (mem_normalizer_iff_map_conj_eq.mpr
      ((linearSpace_map_eq_iff hCV hCV ⟨g, hg⟩).mp hfix))
  · obtain ⟨horb, t, _, ht, _⟩ := hs
    obtain ⟨m, hm⟩ := (action V X).rangeRestrict_surjective t
    have hswap : C.conjBy m = Z := by
      rw [← hm, hfixed, hmoved] at ht
      exact (linearSpace_map_eq_iff hCV hZV m).mp ht
    have hcard : Nat.card (fixedOrbit ρ S) = 2 := by
      rw [horb, Nat.card_coe_set_eq, Set.ncard_pair hinput.fixed_ne_moved]
    have hindex : (normalizer (C : Set G)).relIndex (actingGroup V X) = 2 :=
      horbit.symm.trans hcard
    exact no_swapped_index hTL rfl m.property (hswap ▸ hZX) hcoverT hindex
  · have hcard := hs.1
    rw [binary_card (E := Representation.RegularCyclicNormalClosure.displacementSpan
      (representation V X) S ⊤)] at hcard
    rw [horbit] at hcard
    exact no_large_two_power_index T hinput.moved_dimension_gt_one inf_le_left
      (sylowNormalizer_le_actingGroup T X)
      (inf_le_left.trans (sylow_normalizes_commutingSylow hTL)) hbound hcard
  · have hV : Nat.card V = 8 := by
      have hc := binary_card (E := Additive V)
      rw [he.2.1] at hc
      exact hc
    have hVX := space_le_residual_of_order_twentyOne hV he.2.2.1 hZ hZV hZX
    obtain ⟨hΦ, hq, hm⟩ := hcover hVX
    exact no_order_twentyOne_image_of_frattini hΦ hq hm he.2.2.1
end CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
