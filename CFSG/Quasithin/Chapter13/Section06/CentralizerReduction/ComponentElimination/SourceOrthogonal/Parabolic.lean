module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.AutomorphismActions

/-!
# The actual normalized minimal parabolic in the plus quotient

Put P = Lᵥ(Tᵥ ∩ K), retaining both factors as subgroups of G. The
13.6.14 invariance of K and 13.6.20 containment of Lᵥ show that K⁺ is
normal in the plus actor and that Tᵥ⁺ normalizes P⁺. These assertions
are transported through the literal plus quotient map.

For a marked binary linear model of K⁺, an actor outside K⁺ induces
an outer automorphism preserving this particular parabolic. The intrinsic
flag calculation forces SL₄(2) and the middle node. The model marking,
minimal-parabolic identification, self-centralizer and outside actor are
still explicit: this does not claim to establish them from 13.6.16.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.23(2–3), printed p.933. A minimal parabolic omits one flag cut;
it is not required to be maximal among proper subgroups.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal
open ComponentSelection
open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
variable {G : Type*} [Group G]

/-- The source P = Lᵥ(Tᵥ ∩ K), before any quotient. -/
def sourceParabolic (K L T : Subgroup G) (v : G) : Subgroup G :=
  Lv L v ⊔ (Tv T v ⊓ K)

/-- The parabolic lies in the selected component once 13.6.20 is known. -/
theorem sourceParabolic_le (K L T : Subgroup G) (v : G)
    (hLK : Lv L v ≤ K) : sourceParabolic K L T v ≤ K :=
  sup_le hLK inf_le_right

/-- Tᵥ normalizes both actual factors of P. -/
theorem normalizes_sourceParabolic (K L T : Subgroup G) (v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hK : Tv T v ≤ normalizer (K : Set G)) :
    Tv T v ≤ normalizer (sourceParabolic K L T v : Set G) := by
  intro t ht
  rw [mem_normalizer_iff_map_conj_eq, sourceParabolic, Subgroup.map_sup,
    Subgroup.map_inf _ _ _ (MulAut.conj t).injective,
    mem_normalizer_iff_map_conj_eq.mp (hL ht),
    mem_normalizer_iff_map_conj_eq.mp ((Tv T v).le_normalizer ht),
    mem_normalizer_iff_map_conj_eq.mp (hK ht)]

/-- Relative normalization passes through the literal plus quotient map. -/
theorem normalizes_plusImage (K L T A B : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hB : B ≤ plusActor K L T v) (hAB : A ≤ normalizer (B : Set G)) :
    plusImage K L T z v hL hz A ≤
      normalizer (plusImage K L T z v hL hz B : Set _) := by
  apply le_trans (map_mono (f := plusMk K L T z v hL hz) ?_)
    ((B.subgroupOf (plusActor K L T v)).le_normalizer_map _)
  rw [← subgroupOf_normalizer_eq hB]
  exact comap_mono hAB

/-- K⁺ is normal in the actual plus actor; no ambient normality is assumed. -/
theorem plusComponent_normal (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G)) :
    (plusImage K L T z v hL hz K).Normal := by
  have hminus : Kminus K T v = K := Kminus_eq_of_invariant K T v hK
  have hactor : plusActor K L T v ≤ normalizer (K : Set G) := by
    unfold plusActor
    rw [hminus, sup_eq_left.mpr hLK]
    exact sup_le K.le_normalizer hK
  let : (K.subgroupOf (plusActor K L T v)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (K_le_plusActor K L T v)).mpr hactor
  exact (inferInstance : (K.subgroupOf (plusActor K L T v)).Normal).map
    (plusMk K L T z v hL hz) (plusMk_surjective K L T z v hL hz)

/-- The marked source parabolic, preserved by an actual outer actor, forces
SL₄(2) and omitted node 1 (zero-based indexing). The automorphism is obtained
by conjugation on K⁺, not supplied as an unrelated diagram action. -/
theorem rankFour_of_outer_sourceParabolic (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G))
    {m : ℕ} (hm : m = 3 ∨ m = 4)
    (e : plusImage K L T z v hL hz K ≃* SL(m + 1, ZMod 2))
    (b : Basis m) (i : Fin m)
    (hP : ((plusImage K L T z v hL hz (sourceParabolic K L T v)).subgroupOf
      (plusImage K L T z v hL hz K)).map
      (e.trans (slEquivLinear (m + 1))).toMonoidHom = minimalParabolic b i)
    (hc : centralizer (plusImage K L T z v hL hz K : Set (Gplus K L T z v hL hz)) = ⊥)
    (hout : ¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K) :
    m = 3 ∧ i.val = 1 := by
  let C := plusImage K L T z v hL hz K
  let P := plusImage K L T z v hL hz (sourceParabolic K L T v)
  let S := plusImage K L T z v hL hz (Tv T v)
  let : C.Normal := plusComponent_normal K L T z v hL hz hLK hK
  have hPC : P ≤ C := map_mono (comap_mono (sourceParabolic_le K L T v hLK))
  have hSP : S ≤ normalizer (P : Set _) :=
    normalizes_plusImage K L T _ _ z v hL hz
      ((sourceParabolic_le K L T v hLK).trans (K_le_plusActor K L T v))
      (normalizes_sourceParabolic K L T v hL hK)
  obtain ⟨s, hs, hsC⟩ : ∃ s, s ∈ S ∧ s ∉ C := by
    by_contra h
    apply hout
    intro s hs
    by_contra hsC
    exact h ⟨s, hs, hsC⟩
  let E := e.trans (slEquivLinear (m + 1))
  let a := componentAction C E s
  have ha : a ∉ MulAut.innerSubgroup _ := fun ha =>
    hsC ((componentAction_mem_inner C E hc s).mp ha)
  have hfix := componentAction_map_subgroup C E P hPC s (hSP hs)
  change ((P.subgroupOf C).map E.toMonoidHom).map a.toMonoidHom = _ at hfix
  change (P.subgroupOf C).map E.toMonoidHom = minimalParabolic b i at hP
  rw [hP] at hfix
  have hh := outer_preserves_minimalParabolic_middle (by omega : 2 ≤ m)
    (by omega : m ≤ 4) b i a ha hfix
  exact ⟨hh.1, by omega⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal
