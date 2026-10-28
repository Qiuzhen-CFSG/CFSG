module
public import Stellmacher.Recognition.OddCoreSylow
public import Theory.GroupTheory.NonisolatedFourConnectivity
public import Theory.GroupTheory.ElementaryFourExtension
public import Theory.GroupTheory.IsolatedFourTwoGroup
public import Theory.GroupTheory.IsolatedFourNormalElementary
public import Stellmacher.Recognition.OddCoreQuotientControl
public import Theory.GroupTheory.SolvableFourNormalizerSupplement
public import Theory.GroupTheory.RankTwoNormalAbelian
public import Theory.GroupTheory.PGroup.RankTwoSymplecticType
public import Theory.GroupTheory.PGroup.RankTwoCoreFactors
public import Stellmacher.Recognition.OddCoreWeakSylow
public import Stellmacher.Recognition.CentricInvolutionFusion
public import Theory.GroupTheory.ElementaryWeakCoreCentralFusion
public import Stellmacher.Recognition.NormalEightSylow
public import Theory.GroupTheory.SolvableTwoGeneratedCore
public import Theory.GroupTheory.PGroup.InvolutionFour

/-!
# Small-rank control of the completed odd-core normalizer

In a finite nonsolvable simple N₂ group, fix a Sylow two-subgroup S and an
elementary subgroup A of order at least eight in S. Every nontrivial Q ≤ S
has its full normalizer in the normalizer of the completed odd-core closure
of A.

Janko–Thompson supplies a normal elementary subgroup of order at least eight
in S. GLS2, Corollary 10.22(ii), excludes isolated fours in such a two-group,
so completion and commuting connectivity identify every four-group closure
in S with the closure of A. Naturality then controls subgroups containing fours.

Every involution of S belongs to a four in S. Ambient elementary-eight
extension places that four in an eight inside the involution centralizer.
Its closure still equals the closure of A, and solvable normalizer generation
controls the full centralizer. A nontrivial two-subgroup without a four has a
unique involution; its normalizer therefore lies in this controlled centralizer.

The module also retains the intermediate conditional reductions: quotient
core and Hall-factor obstructions, centric involution movers, comparison up
to conjugacy inside common overgroups, and normalization by core preimages.
Their additional hypotheses remain explicit in their statements.

Sources: GLS, Number 4, Section 18 (including Lemmas 18.7–18.8); GLS,
Number 2, Sections 10 and 22; Janko–Thompson, Main Theorem, Math. Z. 113
(1970), p.385, via `NormalEightSylow`. All closure comparisons use actual
signalizer completion; ambient non-isolation is not identified with
non-isolation in a chosen Sylow.
-/

namespace Stellmacher.Recognition

open scoped Pointwise

/-- Completion also identifies the fixed subgroup of an involution
centralizing the actor, even when that involution is not in the actor. -/
public theorem oddCoreClosure_inf_centralizer_of_centralizes
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (t : G) (ht : orderOf t = 2) (htC : t ∈ Subgroup.centralizer (A : Set G)) :
    involutionOddCoreClosure A ⊓ Subgroup.centralizer ({t} : Set G) =
      involutionOddCore t := by
  let : IsElementaryAbelian 2 (Subgroup.zpowers t) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [← ht]; exact pow_orderOf_eq_one t)
  let B := A ⊔ Subgroup.zpowers t
  let : IsElementaryAbelian 2 B :=
    IsElementaryAbelian.sup_of_le_centralizer (Subgroup.zpowers_le.mpr htC)
  have hB : 8 ≤ Nat.card B := hA.trans (Subgroup.card_le_of_le le_sup_left)
  have htB : t ∈ B := (le_sup_right : Subgroup.zpowers t ≤ B) (Subgroup.mem_zpowers t)
  have htne : t ≠ 1 := by intro h; simp [h] at ht
  have heq := oddCoreClosure_eq_of_le hN B A le_sup_left (by omega)
  rw [← heq]
  exact (involutionOddCoreClosure_complete hN B hB).2.2.2 ⟨t, htB⟩
    (fun h => htne (congrArg Subtype.val h))

/-- Failure of centralizer control gives the precise low-rank quotient
obstruction. Solvability follows from N₂, completion identifies the fixed
subgroup, and the normal rank-three quotient case bounds the two-core. -/
public theorem involutionCentralizer_obstruction_of_not_le_oddCoreClosure_normalizer
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (hAS : A ≤ S)
    (t : G) (ht : orderOf t = 2)
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G))
    (hnot : ¬ Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G)) :
    let H := Subgroup.centralizer ({t} : Set G)
    let N := pPrimeCore 2 H
    Group.IsSolvable H ∧
      involutionOddCoreClosure A ⊓ H = involutionOddCore t ∧
      ∀ D : Subgroup (H ⧸ N), IsElementaryAbelian 2 D →
        D ≤ pCore 2 (H ⧸ N) → Nat.card D < 8 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · by_contra hn
    obtain ⟨U, hU, hnot⟩ :=
      Theory.GroupTheory.exists_nonsolvable_twoLocal_of_involution_centralizer ht hn
    exact hnot (hN U hU)
  · apply oddCoreClosure_inf_centralizer_of_centralizes hN A hA t ht
    intro a ha
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hSC (hAS ha)))
  · intro D hDe hD
    let : IsElementaryAbelian 2 D := hDe
    exact card_lt_eight_of_not_le_oddCoreClosure_normalizer hN A _ hA
      (hAS.trans hSC) _
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card) hnot _ D pCore_isPGroup hD

/-- In the no-normal-four branch, failure of centralizer control gives a
self-centralizing quotient two-core of elementary rank exactly two, all of
whose characteristic abelian subgroups are cyclic. The remaining exclusion
requires ambient fusion; it does not follow from solvability alone. -/
public theorem involutionCentralizer_odd_quotient_core_obstruction
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (hAS : A ≤ S)
    (t : G) (ht : orderOf t = 2)
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G))
    (hno : let H := Subgroup.centralizer ({t} : Set G)
      ∀ U : Subgroup (H ⧸ pPrimeCore 2 H),
        U.Normal → IsElementaryAbelian 2 U → Nat.card U ≠ 4)
    (hnot : ¬ Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G)) :
    let H := Subgroup.centralizer ({t} : Set G)
    let K := H ⧸ pPrimeCore 2 H
    let Q := pCore 2 K
    Group.IsSolvable H ∧ pPrimeCore 2 K = ⊥ ∧
      Subgroup.centralizer (Q : Set K) ≤ Q ∧
      (∃ D : Subgroup K, D ≤ Q ∧ IsElementaryAbelian 2 D ∧ Nat.card D = 4) ∧
      (∀ D : Subgroup K, IsElementaryAbelian 2 D → D ≤ Q → Nat.card D < 8) ∧
      ∀ B : Subgroup Q, B.Characteristic → IsMulCommutative B → IsCyclic B := by
  let H := Subgroup.centralizer ({t} : Set G)
  let K := H ⧸ pPrimeCore 2 H
  obtain ⟨hsolv, -, hrank⟩ :=
    involutionCentralizer_obstruction_of_not_le_oddCoreClosure_normalizer
      hN S A hA hAS t ht hSC hnot
  let : Group.IsSolvable H := hsolv
  have hodd : pPrimeCore 2 K = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hchar : Subgroup.centralizer (pCore 2 K : Set K) ≤ pCore 2 K := by
    rw [← Fitting_eq_pcore K 2 hodd]
    exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable inferInstance
  have hAH : A ≤ H := hAS.trans hSC
  let : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  have hAHcard : 8 ≤ Nat.card (A.subgroupOf H) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv]
  refine ⟨hsolv, hodd, hchar,
    exists_elementary_four_le_pCore_odd_quotient_of_solvable (A.subgroupOf H) hAHcard, hrank, ?_⟩
  intro B hBchar hBcomm
  let : B.Characteristic := hBchar
  let : IsMulCommutative B := hBcomm
  exact Subgroup.isCyclic_characteristic_abelian_of_no_normal_four
    (pCore 2 K) pCore_isPGroup hrank hno B

/-- If an overgroup of the Sylow subgroup normalizes its rank-three closure,
every elementary eight in that overgroup has the same closure. Sylow conjugacy
is performed inside the overgroup, so its conjugating element fixes the closure. -/
public theorem oddCoreClosure_eq_of_le_controlled_overgroup
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A B H : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B)
    (hAS : A ≤ S) (hSH : (S : Subgroup G) ≤ H) (hBH : B ≤ H)
    (hHN : H ≤ Subgroup.normalizer (involutionOddCoreClosure A : Set G)) :
    involutionOddCoreClosure A = involutionOddCoreClosure B := by
  let T := S.subtype hSH
  have hBp : IsPGroup 2 (B.subgroupOf H) :=
    (IsElementaryAbelian.isPGroup 2 B).of_equiv
      (Subgroup.subgroupOfEquivOfLe hBH).symm
  obtain ⟨P, hBP⟩ := hBp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P T
  let e := MulAut.conj (g : G)
  let : IsElementaryAbelian 2 (B.map e.toMonoidHom) := IsElementaryAbelian.map _
  have hBgS : B.map e.toMonoidHom ≤ S := by
    rintro x ⟨b, hb, rfl⟩
    have hbP : (⟨b, hBH hb⟩ : H) ∈ P := hBP hb
    have hbT : (MulAut.conj g) (⟨b, hBH hb⟩ : H) ∈ T := by
      rw [← hg]
      change (MulAut.conj g) • (⟨b, hBH hb⟩ : H) ∈
        (MulAut.conj g) • (P : Set H)
      exact Set.smul_mem_smul_set hbP
    exact hbT
  have heq : involutionOddCoreClosure A =
      involutionOddCoreClosure (B.map e.toMonoidHom) :=
    oddCoreClosure_eq_of_connected hN
      (Subgroup.elementaryCommutingConnected_of_le_twoGroup S A
        (B.map e.toMonoidHom) S.isPGroup' hA
        (by simpa only [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
            using hB) hAS hBgS)
  have hfix : (involutionOddCoreClosure A).map e.toMonoidHom =
      involutionOddCoreClosure A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHN g.property)
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [hfix, involutionOddCoreClosure_map]
  exact heq

/-- Ambient eight extension and control of a Sylow-central element's
centralizer compare the closure of every four-group containing that element. -/
public theorem oddCoreClosure_eq_of_centralizer_control
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (A V : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4) (hAS : A ≤ S)
    (t : G) (htV : t ∈ V)
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G))
    (hCN : Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G)) :
    involutionOddCoreClosure A = involutionOddCoreClosure V := by
  obtain ⟨B, hBe, hB, hVB⟩ :=
    Subgroup.exists_elementary_eight_above_four_of_simple A V hA hV
  let : IsElementaryAbelian 2 B := hBe
  have hBC : B ≤ Subgroup.centralizer ({t} : Set G) := by
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := B)).comm ⟨b, hb⟩ ⟨t, hVB htV⟩))
  exact (oddCoreClosure_eq_of_le_controlled_overgroup hN S A B _ hA hB
    hAS hSC hBC hCN).trans (oddCoreClosure_eq_of_le hN B V hVB (by omega))

/-- Control of a Sylow-central involution's centralizer compares the closure
of every four in that centralizer, even when the four does not contain the
involution. The elementary extension can be taken inside the centralizer. -/
public theorem oddCoreClosure_eq_of_four_le_controlled_involutionCentralizer
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (A V : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4) (hAS : A ≤ S)
    (t : G) (ht : orderOf t = 2)
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G))
    (hVC : V ≤ Subgroup.centralizer ({t} : Set G))
    (hCN : Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G)) :
    involutionOddCoreClosure A = involutionOddCoreClosure V := by
  obtain ⟨B, hBe, hB, hVB, hBC⟩ :=
    Subgroup.exists_elementary_eight_above_four_in_involution_centralizer_of_simple
      A V hA hV t ht hVC
  let : IsElementaryAbelian 2 B := hBe
  exact (oddCoreClosure_eq_of_le_controlled_overgroup hN S A B _ hA hB
    hAS hSC hBC hCN).trans (oddCoreClosure_eq_of_le hN B V hVB (by omega))

/-- The isolated-four comparison reduces to centralizer control only at
the central involutions of that four-group. -/
public theorem oddCoreClosure_eq_of_isolated_four_of_centralizer_control
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (A V : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4) (hAS : A ≤ S) (hVS : V ≤ S)
    (hiso : ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ S → W ≤ Subgroup.centralizer (V : Set G) → W = V)
    (hcontrol : ∀ t : G, orderOf t = 2 → t ∈ V →
      (S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G) →
      Subgroup.centralizer ({t} : Set G) ≤
        Subgroup.normalizer (involutionOddCoreClosure A : Set G)) :
    involutionOddCoreClosure A = involutionOddCoreClosure V := by
  obtain ⟨t, ht, htV, hSC⟩ :=
    Subgroup.exists_central_involution_of_isolated_four_in_sylow S A V hA hV hAS hVS hiso
  exact oddCoreClosure_eq_of_centralizer_control hN S A V hA hV hAS t htV hSC
    (hcontrol t ht htV hSC)

/-- Completion for every elementary four-group, using ambient rank-three
extension in a finite simple group. -/
public theorem involutionOddCoreClosure_four_complete
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (A V : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4) :
    Odd (Nat.card (involutionOddCoreClosure V)) ∧
      Group.IsSolvable (involutionOddCoreClosure V) ∧
      V ≤ Subgroup.normalizer (involutionOddCoreClosure V : Set G) ∧
      ∀ v : V, v ≠ 1 → involutionOddCoreClosure V ⊓
        Subgroup.centralizer ({(v : G)} : Set G) = involutionOddCore (v : G) := by
  obtain ⟨B, hBe, hB, hVB⟩ :=
    Subgroup.exists_elementary_eight_above_four_of_simple A V hA hV
  let : IsElementaryAbelian 2 B := hBe
  have heq := oddCoreClosure_eq_of_le hN B V hVB (by omega)
  have hc := involutionOddCoreClosure_complete hN B hB
  rw [heq] at hc
  refine ⟨hc.1, hc.2.1, hVB.trans hc.2.2.1, ?_⟩
  intro v hv
  exact hc.2.2.2 ⟨v, hVB v.property⟩ (by
    intro h
    exact hv (Subtype.ext (congrArg (fun b : B => (b : G)) h)))

/-- A four-group in the Sylow subgroup which has a distinct commuting
four-group lies in the rank-three odd-core component.  This is the closure
comparison used before the isolated-four residual case. -/
public theorem involutionOddCoreClosure_eq_of_distinct_commuting_four
    {G : Type*} [Group G] [Finite G]
    (hN : IsNTwoGroup G) (S A V W : Subgroup G)
    (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 W]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4)
    (hW : Nat.card W = 4) (hAS : A ≤ S) (hVS : V ≤ S) (hWS : W ≤ S)
    (hcomm : W ≤ Subgroup.centralizer (V : Set G)) (hne : W ≠ V) :
    involutionOddCoreClosure A = involutionOddCoreClosure V :=
  oddCoreClosure_eq_of_connected hN
    (Subgroup.elementaryCommutingConnected_of_distinct_commuting_four
      S A V W hS hA hV hW hAS hVS hWS hcomm hne)

/-- A normal elementary eight in the Sylow subgroup places every four in
the rank-three completed odd-core component. -/
public theorem involutionOddCoreClosure_eq_of_normal_elementary_eight
    {G : Type*} [Group G] [Finite G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (A V : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4)
    (hAS : A ≤ S) (hVS : V ≤ S)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : 8 ≤ Nat.card E) :
    involutionOddCoreClosure A = involutionOddCoreClosure V := by
  let VS := V.subgroupOf (S : Subgroup G)
  let : IsElementaryAbelian 2 VS := IsElementaryAbelian.subgroupOf hVS
  have hVScard : Nat.card VS = 4 := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVS).toEquiv]
  obtain ⟨WS, hWe, hWcard, hWC, hne⟩ :=
    Subgroup.exists_distinct_commuting_four_of_normal_elementary_eight
      S.isPGroup' E VS hE hVScard
  let W := WS.map (S : Subgroup G).subtype
  let : IsElementaryAbelian 2 W := hWe.map _
  have hWcardG : Nat.card W = 4 := by
    simpa only [W, Subgroup.card_map_of_injective (S : Subgroup G).subtype_injective]
      using hWcard
  have hWS : W ≤ S := Subgroup.map_subtype_le _
  have hWcomm : W ≤ Subgroup.centralizer (V : Set G) := by
    rintro w ⟨wS, hwS, rfl⟩ v hv
    exact congrArg Subtype.val (hWC hwS ⟨v, hVS hv⟩ hv)
  have hWne : W ≠ V := by
    intro heq
    apply hne
    apply Subgroup.map_injective (S : Subgroup G).subtype_injective
    change W = VS.map (S : Subgroup G).subtype
    rw [heq, Subgroup.map_subgroupOf_eq_of_le hVS]
  exact involutionOddCoreClosure_eq_of_distinct_commuting_four hN
    (S : Subgroup G) A V W S.isPGroup' hA hV hWcardG hAS hVS hWS hWcomm hWne

/-- Naturality controls N(Q) once its four-groups have a common closure. -/
public theorem normalizer_le_oddCore_normalizer_of_four_closures
    {G : Type*} [Group G] [Finite G] (A Q V : Subgroup G)
    [IsElementaryAbelian 2 V] (hV : Nat.card V = 4) (hVQ : V ≤ Q)
    (hclosure : ∀ B : Subgroup G, IsElementaryAbelian 2 B → Nat.card B = 4 → B ≤ Q →
      involutionOddCoreClosure A = involutionOddCoreClosure B) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  have hAV := hclosure V inferInstance hV hVQ
  intro g hg
  let e := MulAut.conj g
  let : IsElementaryAbelian 2 (V.map e.toMonoidHom) := IsElementaryAbelian.map _
  have hVgQ : V.map e.toMonoidHom ≤ Q := by
    have heq : Q.map e.toMonoidHom = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    exact (Subgroup.map_mono hVQ).trans heq.le
  have hVg := hclosure (V.map e.toMonoidHom) inferInstance
    (by simpa only [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
      using hV) hVgQ
  rw [hAV]
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (involutionOddCoreClosure V).map e.toMonoidHom = _
  rw [involutionOddCoreClosure_map]
  exact hVg.symm.trans hAV

/-- Full normalizer control when all four-groups of Q are nonisolated
inside the given two-subgroup. -/
public theorem normalizer_le_oddCore_normalizer_of_nonisolated_fours
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S A Q V : Subgroup G) (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4)
    (hAS : A ≤ S) (hQS : Q ≤ S) (hVQ : V ≤ Q)
    (hnon : ∀ B : Subgroup G, IsElementaryAbelian 2 B → Nat.card B = 4 → B ≤ Q →
      ∃ W : Subgroup G, IsElementaryAbelian 2 W ∧ Nat.card W = 4 ∧ W ≤ S ∧
        W ≤ Subgroup.centralizer (B : Set G) ∧ W ≠ B) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  apply normalizer_le_oddCore_normalizer_of_four_closures A Q V hV hVQ
  intro B hBe hB hBQ
  let : IsElementaryAbelian 2 B := hBe
  obtain ⟨W, hWe, hW, hWS, hcomm, hne⟩ := hnon B hBe hB hBQ
  let : IsElementaryAbelian 2 W := hWe
  exact oddCoreClosure_eq_of_connected hN
    (Subgroup.elementaryCommutingConnected_of_distinct_commuting_four
      S A B W hS hA hB hW hAS (hBQ.trans hQS) hWS hcomm hne)

/-- Failure of normalizer control forces an elementary four-group of Q
that is isolated among the four-groups of S. -/
public theorem exists_isolated_four_of_normalizer_not_le_oddCore_normalizer
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S A Q V : Subgroup G) (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4)
    (hAS : A ≤ S) (hQS : Q ≤ S) (hVQ : V ≤ Q)
    (hnot : ¬ Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G)) :
    ∃ B : Subgroup G, IsElementaryAbelian 2 B ∧ Nat.card B = 4 ∧ B ≤ Q ∧
      ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 → W ≤ S →
        W ≤ Subgroup.centralizer (B : Set G) → W = B := by
  classical
  by_contra h
  apply hnot
  apply normalizer_le_oddCore_normalizer_of_nonisolated_fours hN S A Q V hS
    hA hV hAS hQS hVQ
  intro B hBe hB hBQ
  by_contra hW
  apply h
  refine ⟨B, hBe, hB, hBQ, ?_⟩
  intro W hWe hWcard hWS hWC
  by_contra hne
  exact hW ⟨W, hWe, hWcard, hWS, hWC, hne⟩

/-- The quotient obstruction has elementary rank exactly two in its
self-centralizing two-core, and has no normal elementary four. The existence
assertion rules out the smaller ranks; the upper bound comes from component
transport through a normal two-subgroup of an odd quotient. -/
public theorem involutionCentralizer_exact_rank_two_obstruction
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (hAS : A ≤ S)
    (t : G) (ht : orderOf t = 2)
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G))
    (hnot : ¬ Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G)) :
    let H := Subgroup.centralizer ({t} : Set G)
    let X := H ⧸ pPrimeCore 2 H
    Group.IsSolvable X ∧ pPrimeCore 2 X = ⊥ ∧
      Subgroup.centralizer (pCore 2 X : Set X) ≤ pCore 2 X ∧
      (∃ D : Subgroup X, D ≤ pCore 2 X ∧ IsElementaryAbelian 2 D ∧ Nat.card D = 4) ∧
      (∀ D : Subgroup X, IsElementaryAbelian 2 D → D ≤ pCore 2 X → Nat.card D < 8) ∧
      ∀ U : Subgroup X, U.Normal → IsElementaryAbelian 2 U → Nat.card U ≠ 4 := by
  let H := Subgroup.centralizer ({t} : Set G)
  let X := H ⧸ pPrimeCore 2 H
  obtain ⟨hsolv, -, hsmall⟩ :=
    involutionCentralizer_obstruction_of_not_le_oddCoreClosure_normalizer
      hN S A hA hAS t ht hSC hnot
  let : Group.IsSolvable H := hsolv
  have hodd : pPrimeCore 2 X = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  refine ⟨inferInstance, hodd, ?_, ?_, hsmall, ?_⟩
  · rw [← Fitting_eq_pcore X 2 hodd]
    exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable inferInstance
  · let : IsElementaryAbelian 2 (A.subgroupOf H) :=
      IsElementaryAbelian.subgroupOf (hAS.trans hSC)
    apply exists_elementary_four_le_pCore_odd_quotient_of_solvable (A.subgroupOf H)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAS.trans hSC)).toEquiv]
  · intro U hUn hUe hU
    let : U.Normal := hUn
    let : IsElementaryAbelian 2 U := hUe
    exact hnot (le_oddCoreClosure_normalizer_of_normal_four_odd_quotient hN A H
      hA (hAS.trans hSC) (pPrimeCore 2 H)
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card) U hU)

/-- Failure of centralizer control is witnessed by an isolated four in a
Sylow lift of the quotient two-core, with a different completed closure.
The lift's normalizer supplements the odd core in the centralizer. Thus the
remaining fusion comparison only needs four-groups in this specific lift. -/
public theorem exists_isolated_core_four_of_centralizer_not_le_oddCoreClosure_normalizer
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (hAS : A ≤ S)
    (t : G) (ht : orderOf t = 2)
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G))
    (hnot : ¬ Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G)) :
    let H := Subgroup.centralizer ({t} : Set G)
    ∃ Q : Subgroup H, Q ≤ S.subtype hSC ∧
      Q.map (QuotientGroup.mk' (pPrimeCore 2 H)) = pCore 2 (H ⧸ pPrimeCore 2 H) ∧
      Subgroup.normalizer (Q : Set H) ⊔ pPrimeCore 2 H = ⊤ ∧
      ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧
        E ≤ Q.map H.subtype ∧
        involutionOddCoreClosure A ≠ involutionOddCoreClosure E ∧
        ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
          W ≤ S → W ≤ Subgroup.centralizer (E : Set G) → W = E := by
  classical
  let H := Subgroup.centralizer ({t} : Set G)
  let T := S.subtype hSC
  let AH := A.subgroupOf H
  let : IsElementaryAbelian 2 AH := IsElementaryAbelian.subgroupOf (hAS.trans hSC)
  have hAH : 8 ≤ Nat.card AH := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAS.trans hSC)).toEquiv]
  obtain ⟨hsolv, hfixed, -⟩ :=
    involutionCentralizer_obstruction_of_not_le_oddCoreClosure_normalizer
      hN S A hA hAS t ht hSC hnot
  let : Group.IsSolvable H := hsolv
  obtain ⟨Q, hQT, ⟨V, hVQ, hVe, hV⟩, hQmap, hsupp⟩ :=
    exists_core_four_containing_normalizer_supplement_of_solvable T AH
      (fun _ ha => hAS ha) hAH
  let QG := Q.map H.subtype
  let VG := V.map H.subtype
  let : IsElementaryAbelian 2 V := hVe
  let : IsElementaryAbelian 2 VG := IsElementaryAbelian.map _
  have hVG : Nat.card VG = 4 :=
    (Subgroup.card_map_of_injective H.subtype_injective).trans hV
  have hVQG : VG ≤ QG := Subgroup.map_mono hVQ
  have hQGS : QG ≤ S := by
    rintro x ⟨q, hq, rfl⟩
    exact hQT hq
  let M := Subgroup.normalizer (involutionOddCoreClosure A : Set G)
  have hNM : (pPrimeCore 2 H).map H.subtype ≤ M := by
    apply le_trans _ (involutionOddCoreClosure A).le_normalizer
    change involutionOddCore t ≤ involutionOddCoreClosure A
    rw [← hfixed]
    exact inf_le_left
  have hbad : ¬ Subgroup.normalizer (QG : Set G) ≤ M := by
    intro hQ
    apply hnot
    have htop : (⊤ : Subgroup H) ≤ M.subgroupOf H := by
      rw [← hsupp]
      apply sup_le
      · intro x hx
        apply hQ
        exact Q.le_normalizer_map H.subtype (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      · intro x hx
        exact hNM (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    intro x hx
    exact htop (Subgroup.mem_top (⟨x, hx⟩ : H))
  have hex : ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧
      E ≤ QG ∧ involutionOddCoreClosure A ≠ involutionOddCoreClosure E := by
    by_contra! h
    exact hbad (normalizer_le_oddCore_normalizer_of_four_closures A QG VG
      hVG hVQG h)
  obtain ⟨E, hEe, hE, hEQ, hne⟩ := hex
  let : IsElementaryAbelian 2 E := hEe
  refine ⟨Q, hQT, hQmap, hsupp, E, hEe, hE, hEQ, hne, ?_⟩
  intro W hWe hW hWS hWC
  by_contra hWE
  let : IsElementaryAbelian 2 W := hWe
  exact hne (involutionOddCoreClosure_eq_of_distinct_commuting_four
    hN S A E W S.isPGroup' hA hE hW hAS (hEQ.trans hQGS) hWS hWC hWE)

/-- The obstruction's Sylow lift is itself of binary symplectic type. The
equivalence is induced by the actual odd quotient map; the isolated four and
the normalizer supplement stay in the original centralizer. Hall's factors
are normal in the lift, not asserted to be normal in the whole centralizer. -/
public theorem exists_isolated_symplectic_core_four_of_centralizer_not_le_oddCoreClosure_normalizer
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (hAS : A ≤ S)
    (t : G) (ht : orderOf t = 2)
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G))
    (hno : let H := Subgroup.centralizer ({t} : Set G)
      ∀ U : Subgroup (H ⧸ pPrimeCore 2 H),
        U.Normal → IsElementaryAbelian 2 U → Nat.card U ≠ 4)
    (hnot : ¬ Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G)) :
    let H := Subgroup.centralizer ({t} : Set G)
    let q := QuotientGroup.mk' (pPrimeCore 2 H)
    let Qbar := pCore 2 (H ⧸ pPrimeCore 2 H)
    ∃ Q : Subgroup H, Q ≤ S.subtype hSC ∧ Q.map q = Qbar ∧
      (∃ e : Q ≃* Qbar, ∀ x : Q, (e x : H ⧸ pPrimeCore 2 H) = q x) ∧
      IsBinarySymplecticType Q ∧
      Subgroup.normalizer (Q : Set H) ⊔ pPrimeCore 2 H = ⊤ ∧
      ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧
        E ≤ Q.map H.subtype ∧
        involutionOddCoreClosure A ≠ involutionOddCoreClosure E ∧
        ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
          W ≤ S → W ≤ Subgroup.centralizer (E : Set G) → W = E := by
  let H := Subgroup.centralizer ({t} : Set G)
  let q := QuotientGroup.mk' (pPrimeCore 2 H)
  obtain ⟨Q, hQS, hmap, hsupp, hfour⟩ :=
    exists_isolated_core_four_of_centralizer_not_le_oddCoreClosure_normalizer
      hN S A hA hAS t ht hSC hnot
  have hinj := Subgroup.injective_comp_subtype_of_coprime_ker q
    (by simpa only [q, QuotientGroup.ker_mk'] using
      (pPrimeCore_coprime_card (p := 2) (G := H))) Q
    ((S.subtype hSC).isPGroup'.to_le hQS)
  let e : Q ≃* pCore 2 (H ⧸ pPrimeCore 2 H) :=
    (MulEquiv.ofBijective (q.subgroupMap Q) ⟨by
      intro x y h
      exact hinj (congrArg Subtype.val h), q.subgroupMap_surjective Q⟩).trans
        (MulEquiv.subgroupCongr hmap)
  obtain ⟨-, -, -, -, -, hchar⟩ :=
    involutionCentralizer_odd_quotient_core_obstruction hN S A hA hAS t ht hSC hno hnot
  have hHall := IsPGroup.isBinarySymplecticType_of_characteristic_abelian
    (pCore_isPGroup (p := 2) (G := H ⧸ pPrimeCore 2 H)) hchar
  exact ⟨Q, hQS, hmap, ⟨e, fun _ => rfl⟩, hHall.of_mulEquiv e.symm, hsupp, hfour⟩

/-- Failure of control forces a nontrivial extraspecial factor in Hall's
quotient-core decomposition. Its rank-two model has order at most thirty-two.
The embedded factors are normal in the core, not asserted normal in the quotient. -/
public theorem involutionCentralizer_nontrivial_hall_factor_obstruction
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (hAS : A ≤ S)
    (t : G) (ht : orderOf t = 2)
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G))
    (hno : let H := Subgroup.centralizer ({t} : Set G)
      ∀ U : Subgroup (H ⧸ pPrimeCore 2 H),
        U.Normal → IsElementaryAbelian 2 U → Nat.card U ≠ 4)
    (hnot : ¬ Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G)) :
    let H := Subgroup.centralizer ({t} : Set G)
    let K := H ⧸ pPrimeCore 2 H
    let Q := pCore 2 K
    ¬ IsBinaryHallFactor Q ∧
      ∃ E D : Subgroup Q, E.Normal ∧ D.Normal ∧
        IsExtraspecial 2 E ∧ IsRankTwoExtraspecialModel E ∧ Nat.card E ≤ 32 ∧
        IsBinaryHallFactor D ∧ D ≤ Subgroup.centralizer (E : Set Q) ∧ E ⊔ D = ⊤ := by
  let H := Subgroup.centralizer ({t} : Set G)
  let q := QuotientGroup.mk' (pPrimeCore 2 H)
  obtain ⟨hsolv, hodd, -, ⟨V, hV, hVe, hVcard⟩, hrank, hchar⟩ :=
    involutionCentralizer_odd_quotient_core_obstruction hN S A hA hAS t ht hSC hno hnot
  let : Group.IsSolvable H := hsolv
  let : IsElementaryAbelian 2 V := hVe
  have hAH : A ≤ H := hAS.trans hSC
  let AH := A.subgroupOf H
  let : IsElementaryAbelian 2 AH := IsElementaryAbelian.subgroupOf hAH
  let f := q.comp AH.subtype
  have hf : Function.Injective f :=
    Subgroup.injective_comp_subtype_of_coprime_ker q
      (by simpa only [q, QuotientGroup.ker_mk'] using
        (pPrimeCore_coprime_card (p := 2) (G := H))) AH
      (IsElementaryAbelian.isPGroup 2 AH)
  let B := (⊤ : Subgroup AH).map f
  let : IsElementaryAbelian 2 (⊤ : Subgroup AH) := {
    exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom (⊤ : Subgroup AH).subtype
      (⊤ : Subgroup AH).subtype_injective).trans
        (IsElementaryAbelian.exponent_dvd_p 2 AH) }
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hB : 8 ≤ Nat.card B := by
    rw [Subgroup.card_map_of_injective hf, Nat.card_congr Subgroup.topEquiv.toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv]
    exact hA
  exact ⟨not_isBinaryHallFactor_pCore_of_elementary_rank_three
    inferInstance hodd B hB V hV hVcard hno,
    exists_rankTwoExtraspecial_hall_factors_pCore inferInstance hodd B hB V hV hVcard
      hno hrank hchar⟩

/-- Ambient fusion moves a Sylow-central involution within a centric subgroup
whose normalizer preserves the completed odd-core closure. This uses simple-group
fusion and the N₂ weak-core theorem, with no assumption of centralizer control. -/
public theorem exists_centric_mover_in_oddCoreClosure_normalizer
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (hAS : A ≤ S)
    (t : G) (ht : orderOf t = 2) (htS : t ∈ S)
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G)) :
    ∃ D : Subgroup G, D ≤ S ∧ t ∈ D ∧
      (S : Subgroup G) ⊓ Subgroup.centralizer (D : Set G) ≤ D ∧
      Subgroup.normalizer (D : Set G) ≤
        Subgroup.normalizer (involutionOddCoreClosure A : Set G) ∧
      ∃ g : G, g ∈ Subgroup.normalizer (D : Set G) ∧
        g⁻¹ * t * g ∈ D ∧ g⁻¹ * t * g ≠ t := by
  let M := Subgroup.normalizer (involutionOddCoreClosure A : Set G)
  have hSM : (S : Subgroup G) ≤ M := sylow_le_normalizer_oddCoreClosure hN S A hAS hA
  have htZ : t ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype := by
    refine Subgroup.mem_map.mpr ⟨⟨t, htS⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro s
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hSC s.property))
  obtain ⟨D, -, hcentric, hDS, htD, g, hg, hgtD, hmove⟩ :=
    exists_centric_extremal_normalizer_moves_involution hG S ⟨t, htS⟩
      ((Subgroup.orderOf_coe (⟨t, htS⟩ : S)).symm.trans ht)
  refine ⟨D, hDS, htD, hcentric, ?_, g, hg, hgtD, hmove⟩
  apply Subgroup.normalizer_le_of_moving_central_involution (S : Subgroup G) M A D
    S.isPGroup' hSM hA hAS ?_ t ht htZ hDS hcentric g⁻¹
    ((Subgroup.normalizer (D : Set G)).inv_mem hg)
    (by simpa only [inv_inv] using hmove)
  intro E B hEe hE4 hES hBe hB8 hBC
  let : IsElementaryAbelian 2 E := hEe
  let : IsElementaryAbelian 2 B := hBe
  exact normalizer_le_normalizer_oddCoreClosure_of_weak_rank
    hG hN S A E E B hAS hA hES le_rfl hE4 (hBC.trans le_sup_right) hB8



/-- Rank-three actors in any common overgroup have conjugate closures there. -/
public theorem exists_conj_oddCoreClosure_eq_of_common_overgroup
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (A B H : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B)
    (hAH : A ≤ H) (hBH : B ≤ H) :
    ∃ g : H, (involutionOddCoreClosure B).map
      (MulAut.conj (g : G)).toMonoidHom = involutionOddCoreClosure A := by
  have hAp : IsPGroup 2 (A.subgroupOf H) :=
    (IsElementaryAbelian.isPGroup 2 A).of_equiv
      (Subgroup.subgroupOfEquivOfLe hAH).symm
  have hBp : IsPGroup 2 (B.subgroupOf H) :=
    (IsElementaryAbelian.isPGroup 2 B).of_equiv
      (Subgroup.subgroupOfEquivOfLe hBH).symm
  obtain ⟨T, hAT⟩ := hAp.exists_le_sylow
  obtain ⟨P, hBP⟩ := hBp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P T
  let e := MulAut.conj (g : G)
  let TG := (T : Subgroup H).map H.subtype
  let : IsElementaryAbelian 2 (B.map e.toMonoidHom) := IsElementaryAbelian.map _
  have hATG : A ≤ TG := by
    intro a ha
    exact ⟨⟨a, hAH ha⟩, hAT ha, rfl⟩
  have hBgT : B.map e.toMonoidHom ≤ TG := by
    rintro x ⟨b, hb, rfl⟩
    have hbP : (⟨b, hBH hb⟩ : H) ∈ P := hBP hb
    have hbT : (MulAut.conj g) (⟨b, hBH hb⟩ : H) ∈ T := by
      rw [← hg]
      change (MulAut.conj g) • (⟨b, hBH hb⟩ : H) ∈
        (MulAut.conj g) • (P : Set H)
      exact Set.smul_mem_smul_set hbP
    exact ⟨_, hbT, rfl⟩
  refine ⟨g, ?_⟩
  rw [involutionOddCoreClosure_map]
  exact (oddCoreClosure_eq_of_connected hN
    (Subgroup.elementaryCommutingConnected_of_le_twoGroup TG A
      (B.map e.toMonoidHom) (T.isPGroup'.map H.subtype) hA
      (by simpa only [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
          using hB) hATG hBgT)).symm


/-- Sylow conjugacy compares rank-three closures up to conjugacy in the
specified overgroup, without requiring that overgroup to control a closure. -/
public theorem exists_conj_oddCoreClosure_eq_of_le_overgroup
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A B H : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B)
    (hAS : A ≤ S) (hSH : (S : Subgroup G) ≤ H) (hBH : B ≤ H) :
    ∃ g : H, (involutionOddCoreClosure B).map
      (MulAut.conj (g : G)).toMonoidHom = involutionOddCoreClosure A :=
  exists_conj_oddCoreClosure_eq_of_common_overgroup hN A B H hA hB
    (hAS.trans hSH) hBH

/-- Every four in the centralizer has a conjugate closure equal to the
rank-three closure. The conjugating element stays in that centralizer. -/
public theorem exists_conj_oddCoreClosure_four_eq_in_involutionCentralizer
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (A V : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4) (hAS : A ≤ S)
    (t : G) (ht : orderOf t = 2)
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G))
    (hVC : V ≤ Subgroup.centralizer ({t} : Set G)) :
    ∃ g : Subgroup.centralizer ({t} : Set G),
      (involutionOddCoreClosure V).map (MulAut.conj (g : G)).toMonoidHom =
        involutionOddCoreClosure A := by
  obtain ⟨B, hBe, hB, hVB, hBC⟩ :=
    Subgroup.exists_elementary_eight_above_four_in_involution_centralizer_of_simple
      A V hA hV t ht hVC
  let : IsElementaryAbelian 2 B := hBe
  have heq := oddCoreClosure_eq_of_le hN B V hVB (by omega)
  simpa only [heq] using
    exists_conj_oddCoreClosure_eq_of_le_overgroup hN S A B _ hA hB hAS hSC hBC

/-- In a simple group of elementary binary rank at least three, all
four-group closures have the same order as a rank-three closure. -/
public theorem card_oddCoreClosure_four_eq
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (A V : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4) (hAS : A ≤ S) :
    Nat.card (involutionOddCoreClosure V) = Nat.card (involutionOddCoreClosure A) := by
  obtain ⟨B, hBe, hB, hVB⟩ :=
    Subgroup.exists_elementary_eight_above_four_of_simple A V hA hV
  let : IsElementaryAbelian 2 B := hBe
  obtain ⟨g, hg⟩ := exists_conj_oddCoreClosure_eq_of_le_overgroup
    hN S A B ⊤ hA hB hAS le_top le_top
  rw [oddCoreClosure_eq_of_le hN B V hVB (by omega)] at hg
  rw [← hg, Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective]

/-- Normalization by the actor alone suffices for closure comparison. -/
public theorem oddCoreClosure_eq_of_actor_normalizes_four_closure
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (A V : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4)
    (hAN : A ≤ Subgroup.normalizer (involutionOddCoreClosure V : Set G)) :
    involutionOddCoreClosure A = involutionOddCoreClosure V := by
  obtain ⟨B, hBe, hB, hVB⟩ :=
    Subgroup.exists_elementary_eight_above_four_of_simple A V hA hV
  let : IsElementaryAbelian 2 B := hBe
  have heq := oddCoreClosure_eq_of_le hN B V hVB (by omega)
  have hBN : B ≤ Subgroup.normalizer (involutionOddCoreClosure V : Set G) := by
    rw [← heq]
    exact B.le_normalizer.trans (normalizer_le_normalizer_involutionOddCoreClosure B)
  obtain ⟨g, hg⟩ := exists_conj_oddCoreClosure_eq_of_common_overgroup
    hN A B _ hA hB hAN hBN
  rw [heq] at hg
  exact hg.symm.trans (Subgroup.mem_normalizer_iff_map_conj_eq.mp g.property)


/-- Full Sylow invariance of the four's closure suffices for comparison.
An eight extending the four lies in its closure normalizer. -/
public theorem oddCoreClosure_eq_of_sylow_normalizes_four_closure
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (A V : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4) (hAS : A ≤ S)
    (hSN : (S : Subgroup G) ≤
      Subgroup.normalizer (involutionOddCoreClosure V : Set G)) :
    involutionOddCoreClosure A = involutionOddCoreClosure V :=
  oddCoreClosure_eq_of_actor_normalizes_four_closure hN A V hA hV (hAS.trans hSN)

/-- The full preimage of the quotient two-core normalizes the closure of
 every four in the involution centralizer. It is normal in the centralizer
 and already controls the rank-three closure. -/
public theorem core_preimage_le_normalizer_four_oddCoreClosure
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (A V : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4) (hAS : A ≤ S)
    (t : G) (ht : orderOf t = 2)
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G))
    (hVC : V ≤ Subgroup.centralizer ({t} : Set G))
    (Q : Subgroup (Subgroup.centralizer ({t} : Set G)))
    (hQS : Q ≤ S.subtype hSC)
    (hQmap : Q.map (QuotientGroup.mk' (pPrimeCore 2
      (Subgroup.centralizer ({t} : Set G)))) =
        pCore 2 ((Subgroup.centralizer ({t} : Set G)) ⧸
          pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)))) :
    let H := Subgroup.centralizer ({t} : Set G)
    let N := pPrimeCore 2 H
    ((pCore 2 (H ⧸ N)).comap (QuotientGroup.mk' N)).map H.subtype ≤
      Subgroup.normalizer (involutionOddCoreClosure V : Set G) := by
  let H := Subgroup.centralizer ({t} : Set G)
  let N := pPrimeCore 2 H
  let K := (pCore 2 (H ⧸ N)).comap (QuotientGroup.mk' N)
  change K.map H.subtype ≤ Subgroup.normalizer (involutionOddCoreClosure V : Set G)
  have hK : K = N ⊔ Q := by
    have hh := congrArg (Subgroup.comap (QuotientGroup.mk' N)) hQmap
    change (Q.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = K at hh
    simpa only [QuotientGroup.comap_map_mk'] using hh.symm
  have hfixed := oddCoreClosure_inf_centralizer_of_centralizes hN A hA t ht
    (fun a ha => Subgroup.mem_centralizer_singleton_iff.mp (hSC (hAS ha)))
  have hKM : K ≤ (Subgroup.normalizer
      (involutionOddCoreClosure A : Set G)).subgroupOf H := by
    rw [hK]
    apply sup_le
    · intro n hn
      have hnR : (n : G) ∈ involutionOddCoreClosure A := by
        have hncore : (n : G) ∈ involutionOddCore t :=
          Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
        rw [← hfixed] at hncore
        exact hncore.1
      exact (involutionOddCoreClosure A).le_normalizer hnR
    · intro q hq
      exact sylow_le_normalizer_oddCoreClosure hN S A hAS hA (hQS hq)
  obtain ⟨g, hg⟩ := exists_conj_oddCoreClosure_four_eq_in_involutionCentralizer
    hN S A V hA hV hAS t ht hSC hVC
  let e := MulAut.conj (g : G)
  have hnormalizers :
      (Subgroup.normalizer (involutionOddCoreClosure V : Set G)).map e.toMonoidHom =
        Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
    rw [Subgroup.map_normalizer_eq_of_bijective _ e.bijective, hg]
  rintro x ⟨q, hq, rfl⟩
  have hqg : (MulAut.conj g) q ∈ K :=
    (inferInstance : K.Normal).conj_mem q hq g
  have hmem : e (q : G) ∈
      (Subgroup.normalizer (involutionOddCoreClosure V : Set G)).map e.toMonoidHom := by
    rw [hnormalizers]
    exact hKM hqg
  change (q : G) ∈ Subgroup.normalizer (involutionOddCoreClosure V : Set G)
  have hh := (Subgroup.mem_map_equiv).mp hmem
  change e.symm (e (q : G)) ∈ Subgroup.normalizer (involutionOddCoreClosure V : Set G) at hh
  simpa only [MulEquiv.symm_apply_apply] using hh

/-- Failure of centralizer control produces a core-contained isolated four
whose closure is normalized by the full quotient-core preimage but not by
the rank-three actor. This isolates the missing ambient fusion implication
without assuming a comparison of the two closures. -/
public theorem exists_core_four_not_normalized_by_actor_of_centralizer_not_le
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (hAS : A ≤ S)
    (t : G) (ht : orderOf t = 2)
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G))
    (hnot : ¬ Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G)) :
    let H := Subgroup.centralizer ({t} : Set G)
    let N := pPrimeCore 2 H
    let K := (pCore 2 (H ⧸ N)).comap (QuotientGroup.mk' N)
    ∃ Q : Subgroup H, Q ≤ S.subtype hSC ∧
      Q.map (QuotientGroup.mk' N) = pCore 2 (H ⧸ N) ∧
      Subgroup.normalizer (Q : Set H) ⊔ N = ⊤ ∧
      ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧
        E ≤ Q.map H.subtype ∧
        K.map H.subtype ≤ Subgroup.normalizer (involutionOddCoreClosure E : Set G) ∧
        ¬ A ≤ Subgroup.normalizer (involutionOddCoreClosure E : Set G) ∧
        ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
          W ≤ S → W ≤ Subgroup.centralizer (E : Set G) → W = E := by
  obtain ⟨Q, hQS, hQmap, hsupp, E, hEe, hE, hEQ, hne, hiso⟩ :=
    exists_isolated_core_four_of_centralizer_not_le_oddCoreClosure_normalizer
      hN S A hA hAS t ht hSC hnot
  let : IsElementaryAbelian 2 E := hEe
  have hEH : E ≤ Subgroup.centralizer ({t} : Set G) :=
    hEQ.trans (Subgroup.map_subtype_le Q)
  refine ⟨Q, hQS, hQmap, hsupp, E, hEe, hE, hEQ, ?_, ?_, hiso⟩
  · exact core_preimage_le_normalizer_four_oddCoreClosure
      hN S A E hA hE hAS t ht hSC hEH Q hQS hQmap
  · intro hAN
    exact hne (oddCoreClosure_eq_of_actor_normalizes_four_closure hN A E hA hE hAN)

/-- In a nonsolvable simple N₂ group, every elementary four in a Sylow
subgroup containing an elementary eight has the same completed closure as
the rank-three actor. Janko–Thompson supplies the normal elementary eight
needed for the local non-isolation argument. -/
public theorem involutionOddCoreClosure_eq_of_four_le_sylow
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A V : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4)
    (hAS : A ≤ S) (hVS : V ≤ S) :
    involutionOddCoreClosure A = involutionOddCoreClosure V := by
  obtain ⟨E, hEn, hEe, hE⟩ :=
    exists_normal_elementary_eight_of_le_sylow hns hN S A hAS hA
  let : E.Normal := hEn
  let : IsElementaryAbelian 2 E := hEe
  exact involutionOddCoreClosure_eq_of_normal_elementary_eight
    hN S A V hA hV hAS hVS E hE

/-- The residual isolated-four comparison. Its isolation hypothesis is
impossible: a normal elementary eight exists in the Sylow, whereas an
isolated four bounds every normal elementary subgroup by four. -/
public theorem involutionOddCoreClosure_eq_of_isolated_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A V : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4)
    (hAS : A ≤ S) (hVS : V ≤ S)
    (_hclosure : involutionOddCoreClosure A ≠ ⊥)
    (hiso : ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ S → W ≤ Subgroup.centralizer (V : Set G) → W = V) :
    involutionOddCoreClosure A = involutionOddCoreClosure V := by
  obtain ⟨E, hEn, hEe, hE⟩ :=
    exists_normal_elementary_eight_of_le_sylow hns hN S A hAS hA
  let : E.Normal := hEn
  let : IsElementaryAbelian 2 E := hEe
  have hbound := Subgroup.card_normal_elementary_le_four_of_isolated_four_in_sylow
    S V hV hVS hiso E
  omega

/-- Every subgroup of the chosen Sylow containing an elementary four has
its full normalizer inside the normalizer of the rank-three closure. -/
public theorem normalizer_le_oddCore_normalizer_of_contains_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A Q V : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4)
    (hAS : A ≤ S) (hQS : Q ≤ S) (hVQ : V ≤ Q) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  apply normalizer_le_oddCore_normalizer_of_four_closures A Q V hV hVQ
  intro B hBe hB hBQ
  let : IsElementaryAbelian 2 B := hBe
  exact involutionOddCoreClosure_eq_of_four_le_sylow
    hns hN S A B hA hB hAS (hBQ.trans hQS)

open scoped IsMulCommutative

/-- A four in the chosen Sylow which centralizes an involution controls its
full centralizer, using solvable normalizer generation in that centralizer. -/
public theorem involutionCentralizer_le_oddCore_normalizer_of_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A V : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4)
    (hAS : A ≤ S) (hVS : V ≤ S)
    (t : G) (ht : orderOf t = 2)
    (hVC : V ≤ Subgroup.centralizer ({t} : Set G)) :
    Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  let C := Subgroup.centralizer ({t} : Set G)
  let M := Subgroup.normalizer (involutionOddCoreClosure A : Set G)
  let : Group.IsSolvable C := hN.isSolvable_involution_centralizer ht
  obtain ⟨B, hBe, hB, hVB, hBC⟩ :=
    Subgroup.exists_elementary_eight_above_four_in_involution_centralizer_of_simple
      A V hA hV t ht hVC
  let : IsElementaryAbelian 2 B := hBe
  have hBA : involutionOddCoreClosure B = involutionOddCoreClosure A :=
    (oddCoreClosure_eq_of_le hN B V hVB (by omega)).trans
      (involutionOddCoreClosure_eq_of_four_le_sylow hns hN S A V hA hV hAS hVS).symm
  let BC := B.subgroupOf C
  let : IsElementaryAbelian 2 BC := IsElementaryAbelian.subgroupOf hBC
  obtain ⟨P, hBP⟩ := (IsElementaryAbelian.isPGroup 2 BC).exists_le_sylow
  obtain ⟨T, hPT⟩ := (P.isPGroup'.map C.subtype).exists_le_sylow
  have hBT : B ≤ T := by
    intro b hb
    exact hPT ⟨⟨b, hBC hb⟩, hBP hb, rfl⟩
  have htop : M.subgroupOf C = ⊤ := by
    apply eq_top_of_normalizer_condition_of_solvable P BC _ hBP
      (by
        change 8 ≤ Nat.card (B.subgroupOf C)
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv]
        exact hB)
    rintro Q hQP ⟨W, hWQ, hWe, hW⟩
    let : IsElementaryAbelian 2 W := hWe
    let WG := W.map C.subtype
    let : IsElementaryAbelian 2 WG := IsElementaryAbelian.map_subtype
    have hWG : Nat.card WG = 4 := by
      simpa only [WG, Subgroup.card_map_of_injective C.subtype_injective] using hW
    have hcontrol := normalizer_le_oddCore_normalizer_of_contains_four
      hns hN T B (Q.map C.subtype) WG hB hWG hBT
      ((Subgroup.map_mono hQP).trans hPT) (Subgroup.map_mono hWQ)
    rw [hBA] at hcontrol
    intro x hx
    exact hcontrol (Q.le_normalizer_map C.subtype ⟨x, hx, rfl⟩)
  exact Subgroup.subgroupOf_eq_top.mp htop

/-- All involution centralizers belonging to the chosen Sylow normalize the
completed odd-core closure. -/
public theorem involutionCentralizer_le_oddCore_normalizer_of_mem_sylow
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (hAS : A ≤ S)
    (t : G) (ht : orderOf t = 2) (htS : t ∈ S) :
    Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  let AS := A.subgroupOf (S : Subgroup G)
  let : IsElementaryAbelian 2 AS := IsElementaryAbelian.subgroupOf hAS
  have hAScard : 4 ≤ Nat.card AS := by
    change 4 ≤ Nat.card (A.subgroupOf (S : Subgroup G))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS).toEquiv]
    omega
  obtain ⟨V, hVe, hV, htV⟩ := S.isPGroup'.exists_elementary_four_mem_of_four_le
    AS hAScard ⟨t, htS⟩ ((Subgroup.orderOf_coe (⟨t, htS⟩ : S)).symm.trans ht)
  let : IsElementaryAbelian 2 V := hVe
  let VG := V.map (S : Subgroup G).subtype
  let : IsElementaryAbelian 2 VG := IsElementaryAbelian.map_subtype
  have hVG : Nat.card VG = 4 := by
    simpa only [VG, Subgroup.card_map_of_injective (S : Subgroup G).subtype_injective]
      using hV
  have htVG : t ∈ VG := ⟨⟨t, htS⟩, htV, rfl⟩
  apply involutionCentralizer_le_oddCore_normalizer_of_four hns hN S A VG hA hVG
    hAS (Subgroup.map_subtype_le _) t ht
  intro v hv
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mul_comm (⟨v, hv⟩ : VG) ⟨t, htVG⟩))

/-- Every nontrivial subgroup of the chosen Sylow has its full normalizer
inside the completed odd-core normalizer. Fours use closure comparison;
without a four the unique involution reduces to its solvable centralizer. -/
public theorem normalizer_le_oddCore_normalizer_of_nontrivial
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A Q : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (hAS : A ≤ S) (hQS : Q ≤ S) (hne : Q ≠ ⊥) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  classical
  by_cases hfour : ∃ V : Subgroup G, IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧ V ≤ Q
  · obtain ⟨V, hVe, hV, hVQ⟩ := hfour
    let : IsElementaryAbelian 2 V := hVe
    exact normalizer_le_oddCore_normalizer_of_contains_four
      hns hN S A Q V hA hV hAS hQS hVQ
  have hQp : IsPGroup 2 Q := S.isPGroup'.to_le hQS
  let : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
  obtain ⟨z, hz, -, huniq⟩ := hQp.exists_central_involution_of_no_elementary_four (by
    intro W hWe hW
    let : IsElementaryAbelian 2 W := hWe
    apply hfour
    exact ⟨W.map Q.subtype, IsElementaryAbelian.map_subtype,
      by simpa only [Subgroup.card_map_of_injective Q.subtype_injective] using hW,
      Subgroup.map_subtype_le _⟩)
  have hzG : orderOf (z : G) = 2 := (Subgroup.orderOf_coe z).trans hz
  apply le_trans _ (involutionCentralizer_le_oddCore_normalizer_of_mem_sylow
    hns hN S A hA hAS z hzG (hQS z.property))
  intro g hg
  let e := Q.normalizerMonoidHom ⟨g, hg⟩
  have hez : e z = z := (huniq (e z) (by
    rw [← map_pow, show z ^ 2 = 1 by rw [← hz]; exact pow_orderOf_eq_one z, map_one])).resolve_left
      (by intro h; have hz1 : z = 1 := e.injective (by simpa using h)
          simp [hz1] at hz)
  have heq := congrArg Subtype.val hez
  change g * (z : G) * g⁻¹ = (z : G) at heq
  exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp heq)

/-- The small-rank uniqueness upgrade under explicit weak-core control.
This is the interface for the remaining binary fusion step in GLS2, Section 22,
and GLS4, Section 18. The proved nontrivial-subgroup theorem already handles
both rank one and isolated rank two, so the weak-core and small-rank hypotheses
need not be used. They are retained here to match that step's exact contract. -/
public theorem normalizer_le_normalizer_oddCoreClosure_of_small_rank
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAS : A ≤ S) (hA : 8 ≤ Nat.card A)
    (_hR : involutionOddCoreClosure A ≠ ⊥)
    (_hweak : ∀ P : Subgroup G, P ≤ (S : Subgroup G) →
      (∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ E ≤ P ∧ 4 ≤ Nat.card E) →
      (∃ B : Subgroup G, IsElementaryAbelian 2 B ∧
        B ≤ P ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (P : Set G)) ∧
        8 ≤ Nat.card B) →
      Subgroup.normalizer (P : Set G) ≤
        Subgroup.normalizer (involutionOddCoreClosure A : Set G))
    (Q : Subgroup G) (hQ : Q ≠ ⊥) (_hQp : IsPGroup 2 Q) (hQS : Q ≤ S)
    (_hsmall : ∀ B : Subgroup G, IsElementaryAbelian 2 B → B ≤ Q → Nat.card B < 8) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) :=
  normalizer_le_oddCore_normalizer_of_nontrivial hns hN S A Q hA hAS hQS hQ

end Stellmacher.Recognition
