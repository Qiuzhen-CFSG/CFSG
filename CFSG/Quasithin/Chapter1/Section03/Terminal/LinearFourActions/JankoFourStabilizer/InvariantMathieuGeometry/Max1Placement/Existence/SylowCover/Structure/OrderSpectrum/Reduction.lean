module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.Reduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex
public import Theory.SpecificGroups.Janko4.Model.Simplicity.Reduction

/-!
# Reducing the J₄ central-closure orders to two concrete normalizer branches

An elementary normal closure of the restricted Sylow center lies in that
Sylow. Transporting to the literal Mathieu Sylow and applying the checked
quotient-action bound gives order at most 2048. Nontriviality then leaves
binary ranks one through eleven; the large-order endpoint is settled.

The closure's image in the original matrix group has normalizer exactly M.
Indeed, a nontrivial ambient normal two-subgroup would contain the central
involution a, whose certified generator relations normally generate the whole
group. The element ab of order 37 gives a contradiction. This argument needs
no ambient simplicity assumption. Minimality in M consequently becomes
irreducibility under the full ambient normalizer.

Actual Sylow conjugacy transports this image into the specified subgroup
`OddIndex.twoSubgroup`, preserving order and the normalizer conditions.
The remaining normalizer analysis is divided according to containment in the
literal embedded Mathieu kernel. The two final definitions are unproved
contracts, not an exhaustive subgroup table. Their consumer is the conditional
assembly in `OrderSpectrum`.

Source: Aschbacher–Smith, A.3.12 and its sporadic Sylow-overgroup argument,
printed pp.47–48; Aschbacher, *Overgroups of Sylow subgroups in sporadic groups*,
Memoirs AMS 60 (1986), no.343; Kleidman–Wilson, *The maximal subgroups of J₄*
(1988), pp.484–510. The numerical input is the checked Mathieu Sylow-core
calculation. Literal ATLAS matrix and word provenance is retained in its
imports; matching orders are never used in place of an actual comparison.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
open Janko4 Janko4.Cardinality Janko4.LocalStructure
open Janko4.OuterReduction.OddIndex
attribute [local irreducible] Janko4.modelGroup matrixA matrixB max1Subgroup localKernel

private noncomputable def orderSpectrumSylow : Sylow 2 Model :=
  twoSubgroup_isPGroup.toSylow (by
    rw [twoSubgroup, index_map_subtype, localTwoSubgroup_index]
    exact Nat.Prime.not_dvd_mul Nat.prime_two (by decide)
      Janko4.OuterReduction.max1_odd_index_unconditional)

@[simp] private theorem orderSpectrumSylow_coe : orderSpectrumSylow.toSubgroup = twoSubgroup := rfl

private noncomputable def localSylowEquiv : localSylow ≃* orderSpectrumSylow :=
  localTwoSubgroup.equivMapOfInjective SylowCore.Local.subtype Subtype.val_injective

/-- The concrete Mathieu calculation bounds every normal elementary subgroup of an ambient Sylow. -/
private theorem normal_elementary_sylow_card_le (S : Sylow 2 Model) (A : Subgroup S)
    [A.Normal] [IsElementaryAbelian 2 A] : Nat.card A ≤ 2048 := by
  let e : S ≃* localSylow := (S.equiv orderSpectrumSylow).trans localSylowEquiv.symm
  let B : Subgroup localSylow := A.map e.toMonoidHom
  have hB : B.Normal := Normal.map inferInstance e.toMonoidHom e.surjective
  let := hB
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map e.toMonoidHom
  have hc : Nat.card B = Nat.card A := card_map_of_injective e.injective
  by_cases hle : 2048 ≤ Nat.card B
  · have he := localKernel_sylow_unique_of_quotientCentralizerBound
      (SylowCore.quotientCentralizerBound_of_fixedBound SylowCore.normalElementaryFixedBound)
      localSylow B hle
    rw [← hc, he, localKernel_sylow_card]
  · omega

/-- The closure is contained in the restricted Sylow, using relative normality in M. -/
theorem centralClosure_le_restrictedSylow (S : Sylow 2 Model) (M : Subgroup Model)
    (hSM : S.toSubgroup ≤ M) [IsElementaryAbelian 2 (centralClosure S M hSM)] :
    centralClosure S M hSM ≤ (S.subtype hSM).toSubgroup :=
  (IsElementaryAbelian.isPGroup 2 (centralClosure S M hSM)).le_sylow_of_normal _

/-- Upper order bound for the literal normal closure in every overgroup. -/
theorem centralClosure_card_le (S : Sylow 2 Model) (M : Subgroup Model)
    (hSM : S.toSubgroup ≤ M) [IsElementaryAbelian 2 (centralClosure S M hSM)] :
    Nat.card (centralClosure S M hSM) ≤ 2048 := by
  let T := S.subtype hSM
  let A := (centralClosure S M hSM).subgroupOf T.toSubgroup
  let e : T ≃* S := subgroupOfEquivOfLe hSM
  let B := A.map e.toMonoidHom
  have hAelem : IsElementaryAbelian 2 A :=
    IsElementaryAbelian.subgroupOf (centralClosure_le_restrictedSylow S M hSM)
  let := hAelem
  have hB : B.Normal := Normal.map inferInstance e.toMonoidHom e.surjective
  let := hB
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map e.toMonoidHom
  have hc : Nat.card B = Nat.card (centralClosure S M hSM) :=
    (card_map_of_injective e.injective).trans
      (Nat.card_congr (subgroupOfEquivOfLe
        (centralClosure_le_restrictedSylow S M hSM)).toEquiv)
  exact hc ▸ normal_elementary_sylow_card_le S B

/-- The order-2048 branch is settled without maximality or any normalizer catalogue. -/
theorem centralClosure_card_eq_2048_of_le (S : Sylow 2 Model) (M : Subgroup Model)
    (hSM : S.toSubgroup ≤ M) [IsElementaryAbelian 2 (centralClosure S M hSM)]
    (hlarge : 2048 ≤ Nat.card (centralClosure S M hSM)) :
    Nat.card (centralClosure S M hSM) = 2048 :=
  Nat.le_antisymm (centralClosure_card_le S M hSM) hlarge

/-- All remaining possibilities are genuine binary ranks from one through eleven. -/
theorem centralClosure_card_eq_two_pow (S : Sylow 2 Model) (M : Subgroup Model)
    (hSM : S.toSubgroup ≤ M) [IsElementaryAbelian 2 (centralClosure S M hSM)] :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 11 ∧ Nat.card (centralClosure S M hSM) = 2 ^ n := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 (centralClosure S M hSM)).exists_card_eq
  refine ⟨n, ?_, ?_, hn⟩
  · by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at hn
    exact centralClosure_ne_bot S M hSM (eq_bot_of_card_eq _ hn)
  · have hb := centralClosure_card_le S M hSM
    rw [hn] at hb
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb

private theorem center_le_normal_two {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hc : Nat.card (center S) = 2)
    (E : Subgroup G) [E.Normal] (hp : IsPGroup 2 E) (hne : E ≠ ⊥) :
    (center S).map S.toSubgroup.subtype ≤ E := by
  have hES : E ≤ S.toSubgroup := hp.le_sylow_of_normal S
  let A := E.subgroupOf S.toSubgroup
  have hA : A ≠ ⊥ := by
    intro h
    apply hne
    change E.subgroupOf S.toSubgroup = ⊥ at h
    rw [← map_subgroupOf_eq_of_le hES, h, Subgroup.map_bot]
  have hI := center_inf_ne_bot_of_normal S.isPGroup' A hA
  have hdiv : Nat.card (center S ⊓ A : Subgroup S) ∣ 2 :=
    (card_dvd_of_le (show center S ⊓ A ≤ center S from inf_le_left)).trans hc.dvd
  have hIc : Nat.card (center S ⊓ A : Subgroup S) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
    · exact (hI (eq_bot_of_card_eq _ h)).elim
    · exact h
  have heq : center S ⊓ A = center S :=
    eq_of_le_of_card_ge inf_le_left (by rw [hIc, hc])
  have hZA : center S ≤ A := heq.symm.le.trans inf_le_right
  rintro x ⟨s, hs, rfl⟩
  exact hZA hs

/-- The certified central involution normally generates; hence there is no ambient normal two-subgroup. -/
private theorem normal_two_subgroup_eq_bot (E : Subgroup Model) [E.Normal]
    (hp : IsPGroup 2 E) : E = ⊥ := by
  by_contra hne
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := centralizer ({Janko4.a} : Set Model))
  obtain ⟨T, hT⟩ := centralizer_sylow_is_ambient P
  have hcenter : (center T).map T.toSubgroup.subtype = zpowers Janko4.a := by
    rw [hT]
    exact centralizer_sylow_center P
  have hc : Nat.card (center T) = 2 := by
    rw [← card_map_of_injective T.toSubgroup.subtype_injective,
      hcenter, Nat.card_zpowers, Janko4.orderOf_a]
  have hza := center_le_normal_two T hc E hp hne
  rw [hcenter] at hza
  have ha : Janko4.a ∈ E := hza (mem_zpowers _)
  have htop : E = ⊤ := by
    apply top_unique
    have hab : (Janko4.a * Janko4.b) ^ 37 = 1 := by
      rw [← Janko4.orderOf_a_mul_b]
      exact pow_orderOf_eq_one _
    have hgen := Janko4.Simplicity.normalClosure_a_eq_top
      Janko4.toMatrix_a Janko4.toMatrix_b Janko4.b_pow_four hab
    rw [← hgen]
    exact normalClosure_le_normal (Set.singleton_subset_iff.mpr ha)
  have hba : Janko4.b ∈ E := htop ▸ mem_top _
  obtain ⟨n, hn⟩ := hp ⟨Janko4.a * Janko4.b, E.mul_mem ha hba⟩
  have hd : 37 ∣ 2 ^ n := by
    rw [← Janko4.orderOf_a_mul_b]
    apply orderOf_dvd_of_pow_eq_one
    exact congrArg E.subtype hn
  have h37 : Nat.Prime 37 := by decide
  have := h37.dvd_of_dvd_pow hd
  norm_num at this

/-- Maximality identifies M with the actual ambient normalizer of its embedded closure. -/
theorem centralClosure_normalizer_eq (S : Sylow 2 Model) (M : Subgroup Model)
    (hM : IsCoatom M) (hSM : S.toSubgroup ≤ M)
    [IsElementaryAbelian 2 (centralClosure S M hSM)] :
    normalizer ((centralClosure S M hSM).map M.subtype : Set Model) = M := by
  let E := centralClosure S M hSM
  have hMN : M ≤ normalizer (E.map M.subtype : Set Model) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      E.le_normalizer_map M.subtype
  have hproper : normalizer (E.map M.subtype : Set Model) ≠ ⊤ := by
    intro ht
    have hEn : (E.map M.subtype).Normal := normalizer_eq_top_iff.mp ht
    let := hEn
    let : IsElementaryAbelian 2 (E.map M.subtype) := IsElementaryAbelian.map M.subtype
    have hbot := normal_two_subgroup_eq_bot (E.map M.subtype)
      (IsElementaryAbelian.isPGroup 2 _)
    exact centralClosure_ne_bot S M hSM
      ((map_eq_bot_iff_of_injective _ M.subtype_injective).mp hbot)
  exact (hM.le_iff_eq hproper).mp hMN

/-- The ambient normalizer has no proper nontrivial invariant subgroup of A. -/
@[expose] def ClosureNormalizerIrreducible (A : Subgroup Model) : Prop :=
  ∀ B : Subgroup Model, B ≤ A → normalizer (A : Set Model) ≤ normalizer (B : Set Model) →
    B = ⊥ ∨ B = A

/-- Minimality in M becomes irreducibility for the actual full ambient normalizer. -/
theorem centralClosure_normalizer_irreducible (S : Sylow 2 Model) (M : Subgroup Model)
    (hM : IsCoatom M) (hSM : S.toSubgroup ≤ M)
    [IsElementaryAbelian 2 (centralClosure S M hSM)] :
    ClosureNormalizerIrreducible ((centralClosure S M hSM).map M.subtype) := by
  intro B hBE hBN
  have hBM : B ≤ M := hBE.trans (map_subtype_le _)
  have hMN : M ≤ normalizer (B : Set Model) := by
    rwa [centralClosure_normalizer_eq S M hM hSM] at hBN
  have hBn : (B.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hBM).mpr hMN
  let := hBn
  have hle : B.subgroupOf M ≤ centralClosure S M hSM := by
    apply (map_le_map_iff_of_injective M.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hBM]
    exact hBE
  rcases centralClosure_minimal S M hSM (B.subgroupOf M) hle with h | h
  · left
    rw [← map_subgroupOf_eq_of_le hBM, h, Subgroup.map_bot]
  · right
    rw [← map_subgroupOf_eq_of_le hBM, h]

private theorem closureNormalizerIrreducible_map (A : Subgroup Model)
    (hA : ClosureNormalizerIrreducible A) (e : MulAut Model) :
    ClosureNormalizerIrreducible (A.map e.toMonoidHom) := by
  intro B hB hN
  have hle : B.map e.symm.toMonoidHom ≤ A := by
    simpa [map_map] using map_mono (f := e.symm.toMonoidHom) hB
  have hn : normalizer (A : Set Model) ≤ normalizer (B.map e.symm.toMonoidHom : Set Model) := by
    have hm := map_mono (f := e.symm.toMonoidHom) hN
    rw [map_equiv_normalizer_eq, map_equiv_normalizer_eq] at hm
    simpa [map_map] using hm
  rcases hA _ hle hn with h | h
  · left
    have hm := congrArg (Subgroup.map e.toMonoidHom) h
    simpa [map_map] using hm
  · right
    have hm := congrArg (Subgroup.map e.toMonoidHom) h
    simpa [map_map] using hm

/-- A closure transported by genuine ambient conjugation to the specified matrix Sylow. -/
structure FixedSylowClosure (A : Subgroup Model) : Prop where
  le_sylow : A ≤ twoSubgroup
  sylow_normalizes : twoSubgroup ≤ normalizer (A : Set Model)
  elementary : IsElementaryAbelian 2 A
  nontrivial : A ≠ ⊥
  maximal_normalizer : IsCoatom (normalizer (A : Set Model))
  irreducible : ClosureNormalizerIrreducible A

/-- The exact canonical closure gives a fixed-Sylow candidate of the same order. -/
theorem centralClosure_fixedSylow (S : Sylow 2 Model) (M : Subgroup Model)
    (hM : IsCoatom M) (hSM : S.toSubgroup ≤ M)
    [IsElementaryAbelian 2 (centralClosure S M hSM)] :
    ∃ A : Subgroup Model, FixedSylowClosure A ∧
      Nat.card A = Nat.card (centralClosure S M hSM) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model S orderSpectrumSylow
  let e := MulAut.conj g
  have hS : S.toSubgroup.map e.toMonoidHom = twoSubgroup := congrArg Sylow.toSubgroup hg
  let E := (centralClosure S M hSM).map M.subtype
  let A := E.map e.toMonoidHom
  have hES : E ≤ S.toSubgroup := by
    rintro x ⟨m, hm, rfl⟩
    exact centralClosure_le_restrictedSylow S M hSM hm
  have hEN : normalizer (E : Set Model) = M := centralClosure_normalizer_eq S M hM hSM
  have hEelem : IsElementaryAbelian 2 E := IsElementaryAbelian.map M.subtype
  let := hEelem
  have hAelem : IsElementaryAbelian 2 A := IsElementaryAbelian.map e.toMonoidHom
  have hEne : E ≠ ⊥ := by
    intro h
    exact centralClosure_ne_bot S M hSM
      ((map_eq_bot_iff_of_injective _ M.subtype_injective).mp h)
  refine ⟨A, ⟨?_, ?_, hAelem, ?_, ?_, ?_⟩, ?_⟩
  · exact hS ▸ map_mono hES
  · change twoSubgroup ≤ normalizer (E.map e.toMonoidHom : Set Model)
    rw [← hS, ← map_equiv_normalizer_eq, hEN]
    exact map_mono hSM
  · intro h
    exact hEne ((map_eq_bot_iff_of_injective _ e.injective).mp h)
  · change IsCoatom (normalizer (E.map e.toMonoidHom : Set Model))
    rw [← map_equiv_normalizer_eq, hEN]
    exact (e.mapSubgroup.isCoatom_iff M).mpr hM
  · exact closureNormalizerIrreducible_map E
      (centralClosure_normalizer_irreducible S M hM hSM) e
  · exact (card_map_of_injective e.injective).trans (card_map_of_injective M.subtype_injective)

/-- The actual characteristic Mathieu kernel, embedded in the original matrix group. -/
abbrev orderSpectrumKernel : Subgroup Model :=
  (localKernel matrixA_mul_self matrixB_pow_four).map SylowCore.Local.subtype

/-- Remaining normalizer analysis for small elementary subgroups inside the Mathieu kernel. -/
@[expose] def SmallKernelClosureOrders : Prop :=
  ∀ A : Subgroup Model, FixedSylowClosure A → A ≤ orderSpectrumKernel →
    Nat.card A < 2048 → Nat.card A = 2 ∨ Nat.card A = 8

/-- Independent remaining normalizer analysis for small elementary subgroups outside the kernel. -/
@[expose] def SmallOutsideKernelClosureOrders : Prop :=
  ∀ A : Subgroup Model, FixedSylowClosure A → ¬ A ≤ orderSpectrumKernel →
    Nat.card A < 2048 → Nat.card A = 2 ∨ Nat.card A = 8

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
