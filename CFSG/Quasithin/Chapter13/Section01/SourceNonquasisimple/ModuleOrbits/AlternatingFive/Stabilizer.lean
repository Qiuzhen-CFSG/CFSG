module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive.Source
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.Representation.SL2FourNaturalExtensions.SylowElements

/-!
# The selected component-centralizer Sylow in the A₅ cover branch

Central natural fixed lifting gives a full component Sylow in each point
stabilizer. Relative normality of C_L(u) in C_M(u) restricts the locally
selected Sylow C_T(u), and the image theorem makes its component image Sylow
in that stabilizer. Since the stabilizer already contains a full component
Sylow, the selected image is itself Sylow in SL₂(4), hence a four-group.

This proves the component-stabilizer assertion in the reducible A₅ paragraph
of Aschbacher--Smith 13.1.12, printed p.872. It does not require the outer
orbit calculation or assert that the four-group's odd Frattini lift splits.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
open Chapter1 Chapter1.Section02 Chapter12.Section02
open Representation.SL2FourNatural

private theorem sylow_promote {H : Type*} [Group H] [Finite H]
    {Q J : Subgroup H} (hQ : IsSylowIn 2 Q J)
    (hS : ∃ S : Sylow 2 H, (S : Subgroup H) ≤ J) :
    ∃ R : Sylow 2 H, (R : Subgroup H) = Q := by
  obtain ⟨S,hSJ⟩ := hS
  obtain ⟨P,rfl⟩ := hQ
  have hcard : Nat.card ((P : Subgroup J).map J.subtype) = Nat.card S := by
    rw [card_map_of_injective J.subtype_injective]
    exact (Nat.card_congr (P.equiv (S.subtype hSJ)).toEquiv).trans
      (Nat.card_congr (subgroupOfEquivOfLe hSJ).toEquiv)
  obtain ⟨R,hR⟩ := (P.isPGroup'.map J.subtype).exists_le_sylow
  refine ⟨R,?_⟩
  apply (eq_of_le_of_card_ge hR _).symm
  rw [hcard]
  exact (Nat.card_congr (R.equiv S).toEquiv).le

/-- The full marked component Sylow has order four and exponent two. -/
theorem component_sylow_four (S : Sylow 2 SL) :
    Nat.card S = 4 ∧ ∀ s : S, s ^ 2 = 1 := by
  constructor
  · calc
      Nat.card S = Nat.card (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2) :=
        Nat.card_congr (S.equiv (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2)).toEquiv
      _ = Nat.card F := Matrix.SpecialLinearGroup.card_upperUnipotent F
      _ = 4 := by rw [Nat.card_eq_fintype_card,card_field]
  · intro s
    apply Subtype.ext
    exact (SL2FourNaturalExtensions.sylow_element_natural S s.property).1

namespace Marking
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  {T : Sylow 2 G} {L : Subgroup G} (d : Marking T L W)

/-- Local Sylow selection puts a full SL₂(4) Sylow in the image of the
literal intersection C_T(u)∩L. Normality is relative to C_{N_G(L)}(u). -/
theorem selected_component_sylow
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L) (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    ∃ S : Sylow 2 SL, (S : Subgroup SL) =
      (((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G)).subgroupOf L).map d.component := by
  let C := centralizer ({(u : G)} : Set G)
  let M := normalizer (L : Set G) ⊓ C
  let K := L ⊓ C
  have hKM : K ≤ M := inf_le_inf_right C L.le_normalizer
  let : (K.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer
    ((inf_le_inf_left (normalizer (L : Set G)) C.le_normalizer).trans
      inf_normalizer_le_normalizer_inf)
  have hs : IsSylowIn 2 (((T : Subgroup G) ⊓ C) ⊓ K) K :=
    IndexTwo.isSylowIn_inf_of_subnormal hlocal hKM
      (inferInstance : (K.subgroupOf M).Normal).isSubnormal
  have hsL : IsSylowIn 2 (((T : Subgroup G) ⊓ C).subgroupOf L) (C.subgroupOf L) := by
    apply (IsSylowIn.map_iff L.subtype L.subtype_injective).mp
    simpa only [subgroupOf_map_subtype, K, inf_assoc, inf_left_comm, inf_comm, inf_idem] using hs
  have hsImage := IndexTwo.isSylowIn_map hsL d.component
  exact sylow_promote hsImage (d.centralizer_contains_component_sylow hmoved u)

/-- In the actual source setup, the selected component image is a four-group
and is Sylow in the marked SL₂(4); no orbit premise is needed. -/
theorem source_selected_four_group
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    ∃ S : Sylow 2 SL, (S : Subgroup SL) =
      (((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G)).subgroupOf L).map d.component ∧
      Nat.card S = 4 ∧ ∀ s : S, s ^ 2 = 1 := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hm := (normalizerMoved_commutator_and_card hL.1.1
    (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).2.1).1
  obtain ⟨S,hS⟩ := d.selected_component_sylow hm u hlocal
  exact ⟨S,hS,component_sylow_four S⟩

end Marking
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
