module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.HyperplaneReduction
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.ElementaryCore.Cardinality
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.GeneratedCore

/-!
# Noncyclic hyperplane supports for Fitting offenders

For a hyperplane B of a noncyclic starred cubic actor A, the actual image
of C = C_(O_p(G))(B) is faithful on U = C_V(B). Its image is normal in the
image of C A, and the rank-one actor there has actual ratio strictly below
two. The cyclic support theorem therefore gives p = 3 and a commutator of
order three. Faithfulness on C transports this order back to [C,A]; the
inclusion U → V transports its moved plane and fixed complement exactly.
No local equality with a global cubic minimum is required.

For the D.2.14 consumer, |A| = 4 and C_(O_3(G))(A) = 1 imply [C,A] = C
by coprime decomposition. This supplies the existing `HyperplaneSupport`
input to the elementary-core argument. The common-centralizer premise
remains with the D.2.14 assembly owner.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
D.2.13(5) and the paragraph preceding (+) in D.2.14, printed pp.184--186
(1 March 2004 manuscript).
-/

public section
namespace CFSG.Quasithin.ChapterD
open Representation.BinaryOffender Subgroup
open scoped IsMulCommutative ENNReal commutatorElement

private theorem ns_commutator_subgroupOf {G : Type*} [Group G]
    {C A H : Subgroup G} (hC : C ≤ H) (hA : A ≤ H) :
    ⁅C.subgroupOf H, A.subgroupOf H⁆ = (⁅C, A⁆).subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le hC, map_subgroupOf_eq_of_le hA,
    map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup C A).trans (sup_le hC hA))]

private theorem ns_moved_comp {G K V : Type*} [Group G] [Group K]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (f : K →* G)
    (U : Submodule (ZMod 2) V) (A : Subgroup K) :
    subspaceCommutator (ρ.comp f) U A = subspaceCommutator ρ U (A.map f) := by
  unfold subspaceCommutator
  congr 1
  ext v
  constructor
  · rintro ⟨a, ha, w, hw, rfl⟩
    exact ⟨f a, mem_map_of_mem f ha, w, hw, rfl⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, w, hw, rfl⟩
    exact ⟨a, ha, w, hw, rfl⟩

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem ns_relative_rank_one
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : IsElementaryTwo A)
    (hr : rank A = 1) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (C : Subgroup G) (hC : IsPGroup p C) (hn : A ≤ normalizer (C : Set G))
    (hm : ⁅C, A⁆ ≠ ⊥) (hlt : actionRatio ρ A < 2) :
    p = 3 ∧ Nat.card (⁅C, A⁆ : Subgroup G) = 3 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⁅C, A⁆) = 2 ∧
      IsCompl (subspaceCommutator ρ ⊤ ⁅C, A⁆) (fixedSpace ρ (⁅C, A⁆ ⊔ A)) := by
  let H := C ⊔ A
  have hCH : C ≤ H := le_sup_left
  have hAH : A ≤ H := le_sup_right
  have hDH : ⁅C, A⁆ ≤ H := Subgroup.commutator_le_sup C A
  let : (C.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer hn)
  have hCp : IsPGroup p (C.subgroupOf H) :=
    hC.of_injective (subgroupOfEquivOfLe hCH).toMonoidHom
      (subgroupOfEquivOfLe hCH).injective
  have hCF : C.subgroupOf H ≤ fittingSubgroup H :=
    le_sSup ⟨inferInstance, hCp.isNilpotent⟩
  let : IsElementaryAbelian 2 A := hA.2
  have hAn : A.subgroupOf H ≠ ⊥ := by
    intro hz
    apply hA.1
    rw [← map_subgroupOf_eq_of_le hAH, hz, Subgroup.map_bot]
  have hAm : IsElementaryTwo (A.subgroupOf H) :=
    ⟨hAn, IsElementaryAbelian.subgroupOf hAH⟩
  have hmn : ⁅C.subgroupOf H, A.subgroupOf H⁆ ≠ ⊥ := by
    intro hz
    apply hm
    have he := congrArg (Subgroup.map H.subtype) hz
    simpa only [map_commutator, map_subgroupOf_eq_of_le hCH,
      map_subgroupOf_eq_of_le hAH, Subgroup.map_bot] using he
  have hratio : actionRatio (ρ.comp H.subtype) (A.subgroupOf H) < 2 := by
    simpa only [actionRatio, fixedCodim_subgroupOf ρ hAH, rank_subgroupOf hAH] using hlt
  obtain ⟨hp3, _, _, hc, _, hd, hs⟩ := normal_prime_group_rank_one_ratio_lt_two
    (ρ.comp H.subtype) (hf.comp H.subtype_injective) hAm
    ((rank_subgroupOf hAH).trans hr) hp (C.subgroupOf H) hCp hCF hmn hratio
  have hmoved : subspaceCommutator (ρ.comp H.subtype) ⊤
      ⁅C.subgroupOf H, A.subgroupOf H⁆ = subspaceCommutator ρ ⊤ ⁅C, A⁆ := by
    rw [ns_moved_comp, map_commutator,
      map_subgroupOf_eq_of_le hCH, map_subgroupOf_eq_of_le hAH]
  have hfixed : fixedSpace (ρ.comp H.subtype)
      (⁅C.subgroupOf H, A.subgroupOf H⁆ ⊔ A.subgroupOf H) =
        fixedSpace ρ (⁅C, A⁆ ⊔ A) := by
    rw [fixedSpace_comp_map, Subgroup.map_sup, map_commutator,
      map_subgroupOf_eq_of_le hCH, map_subgroupOf_eq_of_le hAH]
  rw [ns_commutator_subgroupOf hCH hAH] at hc
  have hcard := Nat.card_congr (subgroupOfEquivOfLe hDH).toEquiv
  exact ⟨hp3, hcard.symm.trans hc, hmoved ▸ hd, hmoved ▸ hfixed ▸ hs⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem ns_restricted_commutator {C A : Subgroup G}
    (U : Submodule (ZMod 2) V)
    (hC : C ≤ subspaceStabilizer ρ U) (hA : A ≤ subspaceStabilizer ρ U) :
    restrictedSubgroup ρ U ⁅C, A⁆ =
      ⁅restrictedSubgroup ρ U C, restrictedSubgroup ρ U A⁆ := by
  unfold restrictedSubgroup
  rw [← map_commutator, ns_commutator_subgroupOf hC hA]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem ns_restricted_sup {C A : Subgroup G}
    (U : Submodule (ZMod 2) V)
    (hC : C ≤ subspaceStabilizer ρ U) (hA : A ≤ subspaceStabilizer ρ U) :
    restrictedSubgroup ρ U (C ⊔ A) =
      restrictedSubgroup ρ U C ⊔ restrictedSubgroup ρ U A := by
  have he : (C ⊔ A).subgroupOf (subspaceStabilizer ρ U) =
      C.subgroupOf (subspaceStabilizer ρ U) ⊔ A.subgroupOf (subspaceStabilizer ρ U) := by
    apply Subgroup.map_injective (subspaceStabilizer ρ U).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hC, map_subgroupOf_eq_of_le hA,
      map_subgroupOf_eq_of_le (sup_le hC hA)]
  unfold restrictedSubgroup
  rw [he, Subgroup.map_sup]

private theorem ns_hyperplane_support
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hr : 1 < rank A) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (B : Subgroup G) (hBA : B ≤ A) (hh : rank B + 1 = rank A)
    (hm : ⁅pCore p G ⊓ centralizer (B : Set G), A⁆ ≠ ⊥) :
    p = 3 ∧ Nat.card (⁅pCore p G ⊓ centralizer (B : Set G), A⁆ : Subgroup G) = 3 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ (fixedSpace ρ B)
        ⁅pCore p G ⊓ centralizer (B : Set G), A⁆) = 2 ∧
      Disjoint (subspaceCommutator ρ (fixedSpace ρ B)
        ⁅pCore p G ⊓ centralizer (B : Set G), A⁆)
        (fixedSpace ρ (⁅pCore p G ⊓ centralizer (B : Set G), A⁆ ⊔ A)) ∧
      subspaceCommutator ρ (fixedSpace ρ B)
        ⁅pCore p G ⊓ centralizer (B : Set G), A⁆ ⊔
        fixedSpace ρ (⁅pCore p G ⊓ centralizer (B : Set G), A⁆ ⊔ A) = fixedSpace ρ B := by
  let U := fixedSpace ρ B
  let C := pCore p G ⊓ centralizer (B : Set G)
  let D := ⁅C,A⁆
  obtain ⟨hk, _, hi, hI, hlt⟩ :=
    source_lemma_D_2_13_hyperplane_restriction ρ hf hA hr hp B hBA hh hm
  have hCstab : C ≤ subspaceStabilizer ρ U :=
    le_stabilizer_fixedSpace_of_commutator_eq_bot ρ C B
      (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right)
  have hAstab : A ≤ subspaceStabilizer ρ U :=
    fixedSpace_subactor_stabilized ρ hA.1.2.1 hBA
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hAC : A ≤ normalizer (C : Set G) := by
    apply (le_inf (le_normalizer_of_normal (H := pCore p G)) ?_).trans
      inf_normalizer_le_normalizer_inf
    exact ((A.le_centralizer.trans (centralizer_le hBA)).trans
      (centralizer_le_normalizer (B : Set G))).trans
        (normalizer_le_normalizer_centralizer B)
  have hDC : D ≤ C := le_normalizer_iff_commutator_le_left.mp hAC
  have hDstab := hDC.trans hCstab
  have hDker : subspaceKernel ρ U D = ⊥ := by
    apply le_bot_iff.mp
    intro d hd
    exact hk.le ⟨hDC hd.1, hd.2⟩
  have hDcard := card_subspaceKernel_mul_image ρ U D hDstab
  rw [hDker, Subgroup.card_bot, one_mul] at hDcard
  have hDn : restrictedSubgroup ρ U D ≠ ⊥ := by
    intro hz
    apply hm
    apply Subgroup.card_eq_one.mp
    rw [← hDcard, hz, Subgroup.card_bot]
  have hCp : IsPGroup p C := pCore_isPGroup.to_le inf_le_left
  have hIp : IsPGroup p (restrictedSubgroup ρ U C) :=
    hCp.of_surjective (restrictedActionSurjection ρ U C hCstab)
      (restrictedActionSurjection_surjective ρ U C hCstab)
  have hcomm := ns_restricted_commutator ρ U hCstab hAstab
  have hIn : restrictedSubgroup ρ U A ≤ normalizer
      (restrictedSubgroup ρ U C : Set (subspaceActionImage ρ U)) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    rw [← hcomm]
    exact restrictedSubgroup_mono ρ U hDC
  obtain ⟨hp3, hcard, hdim, hsplit⟩ := ns_relative_rank_one
    (subspaceImageRepresentation ρ U) (subspaceImageRepresentation_injective ρ U)
    hI.1 hi hp (restrictedSubgroup ρ U C) hIp hIn
    (hcomm ▸ hDn) (hlt.trans_le hA.1.1)
  rw [← hcomm] at hcard hdim hsplit
  have hmov : (subspaceCommutator (subspaceImageRepresentation ρ U) ⊤
      (restrictedSubgroup ρ U D)).map U.subtype = subspaceCommutator ρ U D := by
    simpa only [Submodule.map_top, Submodule.range_subtype] using
      subspaceCommutator_restricted_map ρ U D hDstab ⊤
  have hfix : (fixedSpace (subspaceImageRepresentation ρ U)
      (restrictedSubgroup ρ U D ⊔ restrictedSubgroup ρ U A)).map U.subtype =
        fixedSpace ρ (D ⊔ A) := by
    rw [← ns_restricted_sup ρ U hDstab hAstab,
      fixedSpace_restrictedSubgroup ρ U (D ⊔ A) (sup_le hDstab hAstab),
      Submodule.map_comap_subtype]
    exact inf_eq_right.mpr (fixedSpace_antitone ρ (hBA.trans le_sup_right))
  have hdimMap := (Submodule.equivMapOfInjective U.subtype U.subtype_injective
    (subspaceCommutator (subspaceImageRepresentation ρ U) ⊤
      (restrictedSubgroup ρ U D))).finrank_eq
  rw [hmov] at hdimMap
  have hdj := Submodule.disjoint_map U.subtype_injective hsplit.disjoint
  rw [hmov, hfix] at hdj
  have hsum := congrArg (Submodule.map U.subtype) hsplit.sup_eq_top
  rw [Submodule.map_sup, hmov, hfix, Submodule.map_top, Submodule.range_subtype] at hsum
  exact ⟨hp3, hDcard.symm.trans hcard, hdimMap.symm.trans hdim, hdj, hsum⟩

/-- D.2.13(5): a noncyclic starred actor can move only the three-core. -/
theorem source_lemma_D_2_13_noncyclic_prime
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hr : 1 < rank A) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hm : ⁅pCore p G, A⁆ ≠ ⊥) : p = 3 := by
  obtain ⟨B, hBA, hh, hn⟩ := exists_moved_primeCore_hyperplane ρ hA hp hm
  exact (ns_hyperplane_support ρ hf hA hr hp B hBA hh hn).1

/-- D.2.13(5) on every moved hyperplane: the literal commutator has order
three and its plane has the fixed complement asserted in the source. -/
theorem source_lemma_D_2_13_noncyclic_support
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hr : 1 < rank A) (B : Subgroup G) (hBA : B ≤ A)
    (hh : rank B + 1 = rank A)
    (hm : ⁅pCore 3 G ⊓ centralizer (B : Set G), A⁆ ≠ ⊥) :
    Nat.card (⁅pCore 3 G ⊓ centralizer (B : Set G), A⁆ : Subgroup G) = 3 ∧
      Nonempty ((⁅pCore 3 G ⊓ centralizer (B : Set G), A⁆ : Subgroup G) ≃*
        Multiplicative (ZMod 3)) ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ (fixedSpace ρ B)
        ⁅pCore 3 G ⊓ centralizer (B : Set G), A⁆) = 2 ∧
      Disjoint (subspaceCommutator ρ (fixedSpace ρ B)
        ⁅pCore 3 G ⊓ centralizer (B : Set G), A⁆)
        (fixedSpace ρ (⁅pCore 3 G ⊓ centralizer (B : Set G), A⁆ ⊔ A)) ∧
      subspaceCommutator ρ (fixedSpace ρ B)
        ⁅pCore 3 G ⊓ centralizer (B : Set G), A⁆ ⊔
        fixedSpace ρ (⁅pCore 3 G ⊓ centralizer (B : Set G), A⁆ ⊔ A) = fixedSpace ρ B := by
  obtain ⟨_, hc, hd, hj, hs⟩ := ns_hyperplane_support ρ hf hA hr
    (by decide : Odd 3) B hBA hh hm
  refine ⟨hc, ?_, hd, hj, hs⟩
  have e := (zmodCyclicMulEquiv (isCyclic_of_prime_card hc)).symm
  rw [hc] at e
  exact ⟨e⟩

/-- An actual cyclic model equivalence for the original ambient commutator. -/
noncomputable def noncyclicHyperplaneSupportEquiv
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hr : 1 < rank A) (B : Subgroup G) (hBA : B ≤ A)
    (hh : rank B + 1 = rank A)
    (hm : ⁅pCore 3 G ⊓ centralizer (B : Set G), A⁆ ≠ ⊥) :
    (⁅pCore 3 G ⊓ centralizer (B : Set G), A⁆ : Subgroup G) ≃*
      Multiplicative (ZMod 3) :=
  (source_lemma_D_2_13_noncyclic_support ρ hf hA hr B hBA hh hm).2.1.some

/-- The D.2.14 application preceding (+). The common centralizer premise
supplied by the SQTK argument makes each hyperplane centralizer its own
commutator with A, so D.2.13 supplies `ElementaryCore.HyperplaneSupport`. -/
theorem source_lemma_D_2_14_hyperplaneSupport
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hcard : Nat.card A = 4)
    (hfix : pCore 3 G ⊓ centralizer (A : Set G) = ⊥) :
    ElementaryCore.HyperplaneSupport ρ (pCore 3 G) A := by
  have hr : rank A = 2 := by norm_num [rank, hcard]
  intro B hBA hBr hBn
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  let C := pCore 3 G ⊓ centralizer (B : Set G)
  have hAC : A ≤ normalizer (C : Set G) := by
    apply (le_inf (le_normalizer_of_normal (H := pCore 3 G)) ?_).trans
      inf_normalizer_le_normalizer_inf
    exact ((A.le_centralizer.trans (centralizer_le hBA)).trans
      (centralizer_le_normalizer (B : Set G))).trans
        (normalizer_le_normalizer_centralizer B)
  have hCfix : C ⊓ centralizer (A : Set G) = ⊥ := by
    apply le_bot_iff.mp
    intro c hc
    exact hfix.le ⟨hc.1.1, hc.2⟩
  have hcomm : ⁅C,A⁆ = C := ElementaryCore.commutator_eq C A
    (pCore_isPGroup.to_le inf_le_left) hcard hAC hCfix
  obtain ⟨hc, _, hd, _, _⟩ := source_lemma_D_2_13_noncyclic_support ρ hf hA
    (by omega) B hBA (by omega) (hcomm ▸ hBn)
  change Nat.card C = 3 ∧ Module.finrank (ZMod 2) (subspaceCommutator ρ (fixedSpace ρ B) C) = 2
  change Nat.card (⁅C,A⁆ : Subgroup G) = 3 at hc
  change Module.finrank (ZMod 2) (subspaceCommutator ρ (fixedSpace ρ B) ⁅C,A⁆) = 2 at hd
  exact ⟨hcomm ▸ hc, hcomm ▸ hd⟩

end CFSG.Quasithin.ChapterD
