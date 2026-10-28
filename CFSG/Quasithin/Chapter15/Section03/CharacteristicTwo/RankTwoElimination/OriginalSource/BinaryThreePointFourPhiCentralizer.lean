module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCoreSizes
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalCoreSections
public import Theory.Representation.PSL3Two.NaturalDualCentralizer
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# The original Frattini centralizer in the binary four carrier

The actual kernel intersection Q intersect N has order 2^17, whereas the
Frattini centralizer in Q has order 2^14. It therefore acts nontrivially
on Phi(Q). The marked irreducible dual section Phi(Q)/Z(Q) forces its
fixed subgroup to be exactly Z(Q). The whole point kernel and any subgroup
centralizing it inherit the corresponding intersection bounds.

All groups and quotient maps are the original point source. No invariance
of Phi(Q) under C, or containment Q in N, is assumed. The size argument is
specific to PSL4(2); the two orders coincide in the PSL5(2) row.
Source: MS93(4.5)(v)--(vii), printed p.895, and the full-Sylow binary flag
placement in Aschbacher--Smith 15.3.58.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
universe u
variable {G : Type u} [Group G]

private theorem irreducible_section_dichotomy
    {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    {L D Z T : Subgroup G} {a : L →* A} {σ : Representation (ZMod 2) A V}
    [IsIrreducible σ] (ha : Function.Surjective a)
    (hs : HasSectionModel L D Z a σ)
    (hZT : Z ≤ T) (hTD : T ≤ D) (hLT : L ≤ normalizer T) : T = Z ∨ T = D := by
  obtain ⟨hZD,hLD,_,hn,e,he⟩ := hs
  let := hn
  let p := e.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf D))
  have hp : Function.Surjective p := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : p.ker = Z.subgroupOf D := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let U : Subrepresentation σ := {
    toSubmodule := AddSubgroup.toZModSubmodule 2 ((T.subgroupOf D).map p).toAddSubgroup'
    apply_mem_toSubmodule g := by
      intro v hv
      obtain ⟨l,rfl⟩ := ha g
      change Multiplicative.ofAdd v ∈ (T.subgroupOf D).map p at hv
      obtain ⟨x,hx,hv⟩ := hv
      let y := D.normalizerMonoidHom (inclusion hLD l) x
      have hyT : (y : G) ∈ T := (mem_normalizer_iff.mp (hLT l.property) x).mp hx
      change Multiplicative.ofAdd (σ (a l) v) ∈ (T.subgroupOf D).map p
      refine ⟨y,hyT,?_⟩
      apply Multiplicative.toAdd.injective
      have hh := he l x y rfl
      change (p y).toAdd = σ (a l) (p x).toAdd at hh
      rw [hh,hv]
      rfl }
  rcases eq_bot_or_eq_top U with hbot | htop
  · left
    apply le_antisymm ?_ hZT
    intro t ht
    have hv : (p ⟨t,hTD ht⟩).toAdd ∈ U := mem_map_of_mem p ht
    rw [hbot] at hv
    have hz : (⟨t,hTD ht⟩ : D) ∈ p.ker := hv
    rw [hk] at hz
    exact hz
  · right
    apply le_antisymm hTD
    intro d hd
    have hv : (p ⟨d,hd⟩).toAdd ∈ U := htop ▸ Submodule.mem_top
    change p ⟨d,hd⟩ ∈ (T.subgroupOf D).map p at hv
    obtain ⟨t,ht,heq⟩ := hv
    have hz : (⟨d,hd⟩ : D) / t ∈ p.ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_div,heq,div_self']
    rw [hk] at hz
    have hh := T.mul_mem (hZT hz) ht
    change d / (t : G) * (t : G) ∈ T at hh
    simpa only [div_mul_cancel] using hh

private theorem centralizer_of_irreducible_section
    {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    {L Q Phi Z R : Subgroup G} {a : L →* A} {σ : Representation (ZMod 2) A V}
    [IsIrreducible σ] (ha : Function.Surjective a)
    (hs : HasSectionModel L Phi Z a σ)
    (hRQ : R ≤ Q) (hLR : L ≤ normalizer R)
    (hZQ : Z ≤ centralizer (Q : Set G))
    (hnot : ¬ R ≤ Q ⊓ centralizer (Phi : Set G)) :
    Phi ⊓ centralizer (R : Set G) = Z := by
  have hZ : Z ≤ Phi ⊓ centralizer (R : Set G) :=
    le_inf hs.1 (hZQ.trans (centralizer_le hRQ))
  have hnormal : L ≤ normalizer (Phi ⊓ centralizer (R : Set G)) :=
    (le_inf hs.2.1 (hLR.trans (normalizer_le_normalizer_centralizer R))).trans
      inf_normalizer_le_normalizer_inf
  rcases irreducible_section_dichotomy ha hs hZ inf_le_left hnormal with h | h
  · exact h
  · exfalso
    exact hnot (le_inf hRQ (le_centralizer_iff.mp (h.symm.le.trans inf_le_right)))


variable [Finite G]

/-- The original kernel intersection fixes precisely Z(Q) inside Phi(Q) in the PSL4 row. -/
theorem binary_three_source_four_phi_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2) :
    let C := centralizer ({z} : Set G)
    let N := C.pCoreIn 2
    let Q := LinearThree.commutatorCore c.L
    let Phi := frattiniIn Q
    let ZQ := sCenter Q
    let D := Q ⊓ centralizer (Phi : Set G)
    let R := Q ⊓ N
    ¬ R ≤ D ∧ Phi ⊓ centralizer (R : Set G) = ZQ ∧
      Phi ⊓ centralizer (N : Set G) = ZQ ⊓ centralizer (N : Set G) ∧
      ∀ W : Subgroup G, W ≤ centralizer (N : Set G) → W ⊓ Phi ≤ ZQ := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let ZQ := sCenter Q
  let D := Q ⊓ centralizer (Phi : Set G)
  let R := Q ⊓ N
  have hRcard : Nat.card R = 131072 := by
    have hh := (binary_three_source_binary_core_sizes
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK
      (Or.inl rfl) hm).2
    simpa only [Nat.reduceSub,Nat.reduceMul,Nat.reducePow] using hh
  obtain ⟨a,hs,_,ht⟩ := binary_three_large_distance_original_core_sections
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  have hDcard : Nat.card D = 16384 := by
    obtain ⟨_,_,_,hn,ev,_⟩ := ht
    let := hn
    have hquot : Nat.card (Q ⧸ D.subgroupOf Q) = 64 := by
      rw [Nat.card_congr ev.toEquiv]
      change Nat.card ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) = 64
      rw [Nat.card_prod]
      have h8 : Nat.card (Fin 3 → ZMod 2) = 8 := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Module.finrank_pi,
          Fintype.card_fin,Nat.card_zmod]
        norm_num
      rw [h8]
    have hmul := card_eq_card_quotient_mul_card_subgroup (D.subgroupOf Q)
    have hD : Nat.card (D.subgroupOf Q) = Nat.card D :=
      Nat.card_congr (subgroupOfEquivOfLe (show D ≤ Q from inf_le_left)).toEquiv
    have hQ : Nat.card Q = 1048576 :=
      (binary_three_large_distance_original_core_structure
        hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.2.2.1
    rw [hQ,hquot,hD] at hmul
    omega
  have hnot : ¬ R ≤ D := by
    intro hh
    have hh' := card_le_of_le hh
    rw [hRcard,hDcard] at hh'
    omega
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  have hLQ : c.L ≤ normalizer Q := c.L.le_normalizer.trans
    (normalizer_le_normalizer_commutatorCore c.L)
  have hLN : c.L ≤ normalizer N := hLC.trans (C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C)))
  have hLR : c.L ≤ normalizer R := (le_inf hLQ hLN).trans inf_normalizer_le_normalizer_inf
  have hZQ : ZQ ≤ centralizer (Q : Set G) := by
    rintro _ ⟨x,hx,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
  let : IsIrreducible BinaryLinearThree.W.dual := BinaryLinearThree.IrreducibleCatalogue.dual_irreducible
  have hfix : Phi ⊓ centralizer (R : Set G) = ZQ :=
    centralizer_of_irreducible_section
      (a.surjective.comp (QuotientGroup.mk'_surjective _)) hs inf_le_left hLR hZQ hnot
  have hfixN : Phi ⊓ centralizer (N : Set G) = ZQ ⊓ centralizer (N : Set G) := by
    apply le_antisymm
    · apply le_inf ?_ inf_le_right
      rw [←hfix]
      exact inf_le_inf le_rfl (centralizer_le inf_le_right)
    · exact inf_le_inf hs.1 le_rfl
  refine ⟨hnot,hfix,hfixN,?_⟩
  intro W hW
  have hh : W ⊓ Phi ≤ Phi ⊓ centralizer (N : Set G) := le_inf inf_le_right (inf_le_left.trans hW)
  exact hh.trans (hfixN.le.trans inf_le_left)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
