module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.ActionAlternative
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.CentralizerControl

/-!
# The actual involution alternative and its Sylow geometry at the original G,T

The chosen involution in Wᵍ−U stabilizes the elementary seed V. Its action
on U/Z(U) is nontrivial because O₂(H)∩L=U. The elementary-eight action
calculation therefore gives c₂ or literal interchange of the quaternion
factors, with no action-type or marked-cubic hypothesis.

This extension specializes the existing source argument to the actual
`HigherRankHypothesis` and to `Structural1222At` and `Theorem12213At`.
The universal interfaces remain unchanged. Earlier Chapter 12 inputs keep
their original producers; final recognition still requires I.4.5.
Source: Aschbacher–Smith, 14.4.3–5, printed pp.1006–1008.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual selected outside involution is c₂ or interchanges the two
quaternion factors. No action type or marked-cubic premise is assumed. -/
theorem source_involution_action_dichotomy (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U) :
    q.IsC2 (F.uAction s) ∨
      (q.left.map F.U.subtype).map (MulAut.conj (s : G)).toMonoidHom =
        q.right.map F.U.subtype := by
  let := setup.chosen.elementary
  let H := setup
  have hTL := (source_involution_sylow d setup structural
    alternatives F hne hZ hcard g s hgP hgH hsX
    (congrArg Subtype.val hs) hout).1
  have hsTL : (s : G) ∈ (T : Subgroup G) ⊓ L := hTL ▸ mem_sup_right (mem_zpowers (s : G))
  have hVU : V ≤ F.U := le_conjugateSpanBy V F.H
  let E := V.subgroupOf F.U
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hVU
  have hE : Nat.card E = 8 := (Nat.card_congr (subgroupOfEquivOfLe hVU).toEquiv).trans
    (by simpa [F.last] using F.card 3 (by decide))
  have hact : (F.uAction s) ^ 2 = 1 := by rw [← map_pow, hs, map_one]
  have hstab : ∀ v ∈ E, F.uAction s v ∈ E := by
    intro v hv
    change (s : G) * (v : G) * (s : G)⁻¹ ∈ V
    exact (mem_normalizer_iff.mp (H.sylow_normalizes_seed_at structural hsTL.1) v).mp hv
  have hnon : quotientAut (center F.U) (F.uAction s) ≠ 1 := by
    intro he
    have hk : s ∈ F.uhatAction.ker := he
    rw [source_uhat_kernel d setup structural alternatives F hZ] at hk
    apply hout
    rw [← source_twoCore_inf_block d setup structural
      alternatives F hne hZ hcard]
    exact ⟨hsTL.2, mem_map_of_mem F.H.subtype hk⟩
  rcases q.elementary_eight_involution_dichotomy E hE (F.uAction s) hact hstab hnon with h | h
  · exact Or.inl h
  · right
    rw [map_map]
    have he : (MulAut.conj (s : G)).toMonoidHom.comp F.U.subtype =
        F.U.subtype.comp (F.uAction s).toMonoidHom := rfl
    rw [he, ← map_map, h]

/-- The source c₂ alternative has the rank-three Sylow intersection required
by the ambient elementary-extension transfer argument. -/
theorem source_sylow_rank_of_c2 (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hc2 : q.IsC2 (F.uAction s)) :
    primeRank 2 ((T : Subgroup G) ⊓ L : Subgroup G) = 3 := by
  let := setup.chosen.elementary
  let P := (T : Subgroup G) ⊓ L
  have hTL := (source_involution_sylow d setup structural
    alternatives F hne hZ hcard g s hgP hgH hsX
    (congrArg Subtype.val hs) hout).1
  have hUP : F.U ≤ P := by change F.U ≤ (T : Subgroup G) ⊓ L; rw [hTL]; exact le_sup_left
  have hsP : (s : G) ∈ P := by
    change (s : G) ∈ (T : Subgroup G) ⊓ L
    rw [hTL]
    exact mem_sup_right (mem_zpowers (s : G))
  let U₀ := F.U.subgroupOf P
  let e : F.U ≃* U₀ := (subgroupOfEquivOfLe hUP).symm
  let q₀ := q.map e
  have hU₀ : Nat.card U₀ = 32 := (Nat.card_congr e.toEquiv).symm.trans hcard
  have hi : U₀.index = 2 := by
    have hh := U₀.card_mul_index
    rw [hU₀, (source_sylow_index d setup structural
      alternatives F hne hZ hcard).1] at hh
    omega
  let : U₀.Normal := U₀.normal_of_index_eq_two hi
  let a : P := ⟨s,hsP⟩
  have ho : q₀.BothOuter (MulAut.conjNormal a) :=
    (QuaternionCentralProductData.IsC2.bothOuter q hc2).map q e _ (fun _ => rfl)
  let E := V.subgroupOf F.U
  have hVU : V ≤ F.U := le_conjugateSpanBy V F.H
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hVU
  have hE : Nat.card E = 8 := (Nat.card_congr (subgroupOfEquivOfLe hVU).toEquiv).trans
    (by simpa [F.last] using F.card 3 (by decide))
  let E₀ := E.map e.toMonoidHom
  have hE₀ : IsElementaryAbelian 2 E₀ := IsElementaryAbelian.map e.toMonoidHom
  have hEc : Nat.card E₀ = 8 := by rw [card_map_of_injective e.injective, hE]
  exact (quaternion_index_two_rank U₀ q₀ hi a hout ho E₀ hE₀ hEc).2

/-- In the remaining c₂ branch the ambient Sylow has order 128 and its
intersection with L has index two, the literal index used by Thompson transfer. -/
theorem source_sylow_index_two_of_c2_and_card_thirty_six (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hc2 : q.IsC2 (F.uAction s)) (h36 : Nat.card (HStar F.H) = 36) :
    Nat.card T = 128 ∧ (L.subgroupOf (T : Subgroup G)).index = 2 := by
  have hcore := source_twoCore_eq_of_c2 d setup structural alternatives F hne hZ hcard
    g hgP hgH q s hsX hs hout hc2
  have hc : Nat.card (pCore 2 F.H) = 32 := by
    rw [← card_map_of_injective F.H.subtype_injective]
    change Nat.card (F.H.pCoreIn 2) = 32
    rwa [← hcore]
  have hH : Nat.card F.H = 1152 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 F.H), hc, h36]
  let S : Sylow 2 F.H := T.subtype (F.invariant 1)
  have hS : Nat.card S = 128 := by
    rw [S.card_eq_multiplicity, hH]
    decide +kernel
  have hT : Nat.card T = 128 := by
    change Nat.card ((T : Subgroup G).subgroupOf F.H) = 128 at hS
    rwa [Nat.card_congr (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ F.H from
      F.invariant 1)).toEquiv] at hS
  refine ⟨hT,?_⟩
  have hLT : Nat.card (L.subgroupOf (T : Subgroup G)) = 64 := by
    rw [← inf_subgroupOf_right L (T : Subgroup G),
      Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm]
    exact (source_sylow_index d setup structural
      alternatives F hne hZ hcard).1
  have hh := (L.subgroupOf (T : Subgroup G)).card_mul_index
  rw [hLT,hT] at hh
  omega

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
