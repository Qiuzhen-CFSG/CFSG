module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.CentralizerControl
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.ElementaryInvolution
public import Theory.GroupTheory.QuaternionCentralProductTransport.OuterAction

/-!
# The actual involution alternative and its Sylow geometry

The chosen involution in Wᵍ−U stabilizes the elementary seed V. Its action
on U/Z(U) is nontrivial because O₂(H)∩L=U. The elementary-eight action
calculation therefore gives c₂ or literal interchange of the quaternion
factors, with no action-type or marked-cubic hypothesis.

The c₂ case has rank-three Sylow intersection. If the quotient order is 36,
T has order 128 and T∩L has index two. The order-eighteen branch already
constructs SourceLocalData and its I.4.5 configuration. The final consumer
retains explicit witnesses in the other two cases, including the original
Wᵍ, Sylow product and generated elementary sixteen.

Excluding the swapping branch and the order-36 c₂ branch remains with
qt-d-14414-g2-source. Universal recognition remains qt-i45-g2-recognition,
and the earlier source inputs retain their original producers. This reduction
does not assert the unconditional source theorem.

Source: Aschbacher–Smith, 14.4.4–5, printed pp.1007–1008.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual selected outside involution is c₂ or interchanges the two
quaternion factors. No action type or marked-cubic premise is assumed. -/
theorem source_involution_action_dichotomy (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U) :
    q.IsC2 (F.uAction s) ∨
      (q.left.map F.U.subtype).map (MulAut.conj (s : G)).toMonoidHom =
        q.right.map F.U.subtype := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  have hTL := (source_involution_sylow d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard g s hgP hgH hsX
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
    exact (mem_normalizer_iff.mp (H.sylow_normalizes_seed previous.structural hsTL.1) v).mp hv
  have hnon : quotientAut (center F.U) (F.uAction s) ≠ 1 := by
    intro he
    have hk : s ∈ F.uhatAction.ker := he
    rw [source_uhat_kernel d earlier hq chosen previous F hZ] at hk
    apply hout
    rw [← source_twoCore_inf_block d earlier hq chosen previous.structural
      previous.alternatives F hne hZ hcard]
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
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hc2 : q.IsC2 (F.uAction s)) :
    primeRank 2 ((T : Subgroup G) ⊓ L : Subgroup G) = 3 := by
  let := chosen.elementary
  let P := (T : Subgroup G) ⊓ L
  have hTL := (source_involution_sylow d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard g s hgP hgH hsX
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
    rw [hU₀, (source_sylow_index d earlier hq chosen previous.structural
      previous.alternatives F hne hZ hcard).1] at hh
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
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hc2 : q.IsC2 (F.uAction s)) (h36 : Nat.card (HStar F.H) = 36) :
    Nat.card T = 128 ∧ (L.subgroupOf (T : Subgroup G)).index = 2 := by
  have hcore := source_twoCore_eq_of_c2 d earlier hq chosen previous F hne hZ hcard
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
    exact (source_sylow_index d earlier hq chosen previous.structural
      previous.alternatives F hne hZ hcard).1
  have hh := (L.subgroupOf (T : Subgroup G)).card_mul_index
  rw [hLT,hT] at hh
  omega

/-- The original local data are constructed except in two explicit source
branches: a c₂ action with quotient order 36, or a literal swapping sixteen. -/
theorem source_localData_or_remaining_branches (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U) :
    Nonempty (SourceLocalData L F) ∨
      (q.IsC2 (F.uAction s) ∧ F.U = F.H.pCoreIn 2 ∧
        centralizer (L : Set G) = ⊥ ∧ Nat.card (HStar F.H) = 36) ∨
      ((q.left.map F.U.subtype).map (MulAut.conj (s : G)).toMonoidHom =
        q.right.map F.U.subtype ∧
        ⁅F.U, zpowers (s : G)⁆ = F.U ⊓ centralizer ({(s : G)} : Set G) ∧
        IsElementaryAbelian 2 (zpowers (s : G) ⊔ ⁅F.U, zpowers (s : G)⁆ : Subgroup G) ∧
        Nat.card (zpowers (s : G) ⊔ ⁅F.U, zpowers (s : G)⁆ : Subgroup G) = 16) := by
  rcases source_involution_action_dichotomy d earlier hq chosen previous F hne hZ hcard
    g hgP hgH q s hsX hs hout with hc2 | hswap
  · rcases source_quotient_card_cases d earlier hq chosen previous F hne hZ hcard with h18 | h36
    · exact Or.inl (source_localData_of_c2_and_card_eighteen d earlier hq chosen previous
        F hne hZ hcard g hgP hgH q s hsX hs hout hc2 h18)
    · exact Or.inr (Or.inl ⟨hc2,
        source_twoCore_eq_of_c2 d earlier hq chosen previous F hne hZ hcard
          g hgP hgH q s hsX hs hout hc2,
        source_c2_block_centralizer d earlier hq chosen previous F hne hZ hcard
          g hgP hgH q s hsX hs hout hc2, h36⟩)
  · exact Or.inr (Or.inr ⟨hswap,
      q.elementary_sixteen_of_swap F.U s (congrArg Subtype.val hs) hout hswap⟩)

/-- Apply the proved action alternative to the actual recognition consumer.
The two surviving alternatives still require the source split-block and fusion
contradictions; the witnesses retain the original Wᵍ and Sylow product. -/
theorem source_configuration_or_remaining_branches (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nonempty (DimensionFour.G2ThreeConfiguration G) ∨
      ∃ (q : QuaternionCentralProductData F.U) (g : G) (s : F.H),
        g ∈ L ∧ g ∈ F.P L ∧ g ∉ F.H ∧ (s : G) ∈ F.X g ∧ s ^ 2 = 1 ∧
        (s : G) ∉ F.U ∧ (T : Subgroup G) ⊓ L = F.U ⊔ zpowers (s : G) ∧
        ((q.IsC2 (F.uAction s) ∧ F.U = F.H.pCoreIn 2 ∧
          centralizer (L : Set G) = ⊥ ∧ Nat.card (HStar F.H) = 36) ∨
        ((q.left.map F.U.subtype).map (MulAut.conj (s : G)).toMonoidHom =
          q.right.map F.U.subtype ∧
          ⁅F.U, zpowers (s : G)⁆ = F.U ⊓ centralizer ({(s : G)} : Set G) ∧
          IsElementaryAbelian 2 (zpowers (s : G) ⊔ ⁅F.U, zpowers (s : G)⁆ : Subgroup G) ∧
          Nat.card (zpowers (s : G) ⊔ ⁅F.U, zpowers (s : G)⁆ : Subgroup G) = 16)) := by
  obtain ⟨q⟩ := source_quaternion d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard
  obtain ⟨g,s,hgL,hgP,hgH,hsX,hs,hout,hTL⟩ := source_involution_sylow_exists
    d earlier hq chosen previous.structural previous.alternatives F hne hZ hcard
  rcases source_localData_or_remaining_branches d earlier hq chosen previous F hne hZ hcard
    g hgP hgH q s hsX hs hout with hlocal | hremaining
  · obtain ⟨localData⟩ := hlocal
    exact Or.inl (configuration_of_source_local d earlier hq chosen previous.structural
      previous.alternatives F hne hZ hcard localData)
  · exact Or.inr ⟨q,g,s,hgL,hgP,hgH,hsX,hs,hout,hTL,hremaining⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
