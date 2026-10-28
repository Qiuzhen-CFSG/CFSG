module

public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.PGroup.Omega
public import CFSG.Quasithin.Chapter1.Section01
public import Mathlib.Order.Preorder.Finite

/-!
# The ordering and elementary uniqueness arguments of A.5

Here `V(H)` means the conjugate span of the central omega subgroup of the
fixed Sylow group, not the intrinsic signalizer module of A.4.7. The
ordering is the actual product factorization of A.5.2. We prove A.5.3–5,
A.5.7(1), A.5.9 and A.5.10(1–2) by the general conjugate-span arguments.

The complete local conclusions of A.5.7(2–3) and A.5.10(3–4) additionally
need B.2.14 and the characteristic-two inheritance results. The normalizer
argument for A.5.10(3–4) is proved with the nontrivial two-group fact explicit;
its unconditional source specialization remains to be assembled.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp. 61–63.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterA.Section05To06

open Subgroup

variable {G : Type*} [Group G]

/-- The subgroup `Ω₁(Z(T))`, embedded in the ambient group. -/
def centralOmega (T : Sylow 2 G) : Subgroup G :=
  ((omega₁ (Subgroup.center T) (p := 2)).map (Subgroup.center T).subtype).map
    (T : Subgroup G).subtype

/-- The special meaning of `V(H)` in A.5, Chapter 14.1 and Chapter 15. -/
def sourceModule (T : Sylow 2 G) (H : Subgroup G) : Subgroup G :=
  conjugateSpanBy (centralOmega T) H

/-- Source `H(T)`: subgroups with nontrivial two-core containing `T`. -/
def overgroups (T : Sylow 2 G) : Set (Subgroup G) :=
  Chapter1.HOver G (T : Set G)

/-- Source `M(T)`, ordered by inclusion only in this membership predicate. -/
def maximalLocals (T : Sylow 2 G) : Set (Subgroup G) :=
  {M | IsMaximalTwoLocal M ∧ (T : Subgroup G) ≤ M}

/-- The relation of Definition A.5.2. -/
def OrderingLE (T : Sylow 2 G) (H K : Subgroup G) : Prop :=
  ConjugateSpanLE (centralOmega T) H K

/-- Source `H_v(T)`. -/
def normalizerOvergroups (T : Sylow 2 G) : Set (Subgroup G) :=
  {H | H ∈ overgroups T ∧ H = normalizer (sourceModule T H : Set G)}

/-- Maximality in `M(T)` for the ordering of A.5.2. -/
def IsOrderingMaximal (T : Sylow 2 G) (M : Subgroup G) : Prop :=
  M ∈ maximalLocals T ∧
    ∀ K ∈ maximalLocals T, OrderingLE T M K → K = M

/-- The family `V(T)` of A.5.8, ordered by subgroup inclusion. -/
def moduleFamily (T : Sylow 2 G) : Set (Subgroup G) :=
  sourceModule T '' overgroups T

theorem orderingLE_of_le (T : Sylow 2 G) {H K : Subgroup G} (h : H ≤ K) :
    OrderingLE T H K := conjugateSpanLE_of_le _ h

theorem sourceModule_le_of_orderingLE {T : Sylow 2 G} {H K : Subgroup G}
    (h : OrderingLE T H K) : sourceModule T H ≤ sourceModule T K :=
  h.span_le

/-- The three conclusions of A.5.3. -/
theorem lemma_A_5_3 {T : Sylow 2 G} {H K : Subgroup G} (h : OrderingLE T H K) :
    sourceModule T H ≤ sourceModule T K ∧
    K ⊓ centralizer (sourceModule T K : Set G) ≤
      K ⊓ centralizer (sourceModule T H : Set G) ∧
    (H ∈ normalizerOvergroups T →
      K ⊓ centralizer (sourceModule T K : Set G) ≤
        H ⊓ centralizer (sourceModule T H : Set G)) :=
  ⟨h.span_le, h.centralizer_le, fun hH => h.centralizer_le_of_normalizer hH.2⟩

/-- A.5.4, including both equivalences. -/
theorem lemma_A_5_4 {T : Sylow 2 G} {H K : Subgroup G}
    (hH : H ∈ normalizerOvergroups T) (hK : K ∈ normalizerOvergroups T) :
    (H = K ↔ sourceModule T H = sourceModule T K) ∧
    (H = K ↔ OrderingLE T H K ∧ OrderingLE T K H) := by
  constructor
  · constructor
    · exact congrArg (sourceModule T)
    · intro h
      rw [hH.2, h, ← hK.2]
  · constructor
    · rintro rfl
      exact ⟨conjugateSpanLE_refl _ _, conjugateSpanLE_refl _ _⟩
    · rintro ⟨hHK, hKH⟩
      exact conjugateSpanLE_antisymm hH.2 hK.2 hHK hKH

/-- The partial order on `H_v(T)` in A.5.5. It is an explicit structure,
so clients choose it without changing subgroup inclusion elsewhere. -/
@[instance_reducible] def orderingPartialOrder (T : Sylow 2 G) :
    PartialOrder {H : Subgroup G // H ∈ normalizerOvergroups T} where
  le H K := OrderingLE T H.1 K.1
  lt H K := OrderingLE T H.1 K.1 ∧ ¬ OrderingLE T K.1 H.1
  le_refl H := conjugateSpanLE_refl _ _
  le_trans H K L := conjugateSpanLE_trans H.2.2
  le_antisymm H K hHK hKH :=
    Subtype.ext (conjugateSpanLE_antisymm H.2.2 K.2.2 hHK hKH)

/-- A.5.7(1): covering the action of an ordering-maximal local subgroup
forces uniqueness of the maximal two-local overgroup. `OrderingLE T M X`
is precisely `M = X C_M(V(M))` when `X ≤ M`. -/
theorem lemma_A_5_7_1 {T : Sylow 2 G} {M X : Subgroup G}
    (hM : IsOrderingMaximal T M) (hTX : (T : Subgroup G) ≤ X)
    (hXM : X ≤ M) (hcover : OrderingLE T M X) :
    ∀ K : Subgroup G, IsMaximalTwoLocal K → (X ≤ K ↔ K = M) := by
  intro K hK
  constructor
  · intro hXK
    apply hM.2 K ⟨hK, hTX.trans hXK⟩
    intro x hx
    obtain ⟨a, ha, c, hc, heq⟩ := hcover x hx
    exact ⟨a, ⟨ha.1, hXK ha.2⟩, c, hc, heq⟩
  · rintro rfl
    exact hXM

/-- A.5.9(2). -/
theorem lemma_A_5_9_2 {T : Sylow 2 G} {H K : Subgroup G}
    (hHK : OrderingLE T H K) (hKH : OrderingLE T K H) :
    sourceModule T H = sourceModule T K :=
  conjugateSpanBy_eq_of_mutual hHK hKH

/-- A.5.10(1) from its actual inclusion-maximality hypothesis on `V(H)`. -/
theorem lemma_A_5_10_1 {T : Sylow 2 G} {H K : Subgroup G}
    (hmax : Maximal (fun W => W ∈ moduleFamily T) (sourceModule T H))
    (hK : K ∈ overgroups T) (hle : sourceModule T H ≤ sourceModule T K) :
    K ≤ normalizer (sourceModule T H : Set G) := by
  have heq : sourceModule T H = sourceModule T K :=
    le_antisymm hle (hmax.2 ⟨K, hK, rfl⟩ hle)
  rw [heq]
  exact le_normalizer_conjugateSpanBy _ _

/-- A.5.10(2). -/
theorem lemma_A_5_10_2 {T : Sylow 2 G} {H K : Subgroup G}
    (hmax : Maximal (fun W => W ∈ moduleFamily T) (sourceModule T H))
    (hK : K ∈ overgroups T) (h : OrderingLE T H K) :
    K ≤ normalizer (sourceModule T H : Set G) :=
  lemma_A_5_10_1 hmax hK h.span_le

/-- A.5.6 after supplying the two-group fact for `V` from B.2.14.
Normality here is relative to `M`, not to the ambient group. -/
theorem le_of_generated_intersection [Finite G] {T : Sylow 2 G}
    {H M V : Subgroup G} (hM : IsMaximalTwoLocal M)
    (h : OrderingLE T H M) (hVne : V ≠ ⊥) (hVtwo : IsPGroup 2 V)
    (hV : V = conjugateSpanBy (V ⊓ centralOmega T) (H ⊓ M))
    (hMV : M ≤ normalizer (V : Set G)) : H ≤ M := by
  have hloc : IsTwoLocal (normalizer (V : Set G)) := ⟨V, hVne, hVtwo, rfl⟩
  have heq : M = normalizer (V : Set G) := le_antisymm hMV (hM.2 hloc hMV)
  exact le_of_conjugateSpanLE_of_generated_intersection h hV heq

/-- A.5.10(3–4), with the nontrivial two-group conclusion of B.2.14
explicit until that source input is assembled. All local maximality and
uniqueness assertions are derived here. -/
theorem maximal_normalizer_of_maximal_module [Finite G] {T : Sylow 2 G}
    {H : Subgroup G} (hH : H ∈ overgroups T)
    (hmax : Maximal (fun W => W ∈ moduleFamily T) (sourceModule T H))
    (hne : sourceModule T H ≠ ⊥) (htwo : IsPGroup 2 (sourceModule T H)) :
    let N := normalizer (sourceModule T H : Set G)
    IsOrderingMaximal T N ∧
      ∀ K : Subgroup G, IsMaximalTwoLocal K → (H ≤ K ↔ K = N) := by
  let N := normalizer (sourceModule T H : Set G)
  have hHN : H ≤ N := le_normalizer_conjugateSpanBy _ _
  have hloc : IsTwoLocal N := ⟨sourceModule T H, hne, htwo, rfl⟩
  have hlocalOver {K : Subgroup G} (hK : IsMaximalTwoLocal K)
      (hTK : (T : Subgroup G) ≤ K) : K ∈ overgroups T :=
    ⟨Chapter1.mem_H_of_isTwoLocal hK.1, hTK⟩
  have hcontrol {K : Subgroup G} (hK : IsMaximalTwoLocal K) (hHK : H ≤ K) : K ≤ N :=
    lemma_A_5_10_1 hmax (hlocalOver hK (hH.2.trans hHK))
      (conjugateSpanBy_mono le_rfl hHK)
  obtain ⟨M, hNM, hM⟩ := Finite.exists_le_maximal hloc
  have hMN : M = N := le_antisymm (hcontrol hM (hHN.trans hNM)) hNM
  have hN : IsMaximalTwoLocal N := hMN ▸ hM
  refine ⟨⟨⟨hN, hH.2.trans hHN⟩, ?_⟩, ?_⟩
  · intro K hK hNK
    have hVK : sourceModule T H ≤ sourceModule T K :=
      (conjugateSpanBy_mono le_rfl hHN).trans hNK.span_le
    have hKN : K ≤ N := lemma_A_5_10_1 hmax (hlocalOver hK.1 hK.2) hVK
    exact le_antisymm hKN (hK.1.2 hloc hKN)
  · intro K hK
    constructor
    · intro hHK
      have hKN := hcontrol hK hHK
      exact le_antisymm hKN (hK.2 hloc hKN)
    · rintro rfl
      exact hHN

end CFSG.Quasithin.ChapterA.Section05To06

end
