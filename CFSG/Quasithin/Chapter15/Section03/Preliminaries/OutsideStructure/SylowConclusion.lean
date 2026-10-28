module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.Sylow
public import Theory.Quasithin.EvenCharacteristic
public import Theory.GroupTheory.TwoLocalCoreObstruction

/-!
# The Sylow conclusion for an outside overgroup

Transport the residual uniqueness dichotomy along conjugacy of Sylow subgroups
inside M. A strict two-overgroup of S already has full Sylow order, so its
join with Y₊ would be a uniqueness subgroup in M. The nontrivial two-core
of I places I in a maximal two-local, contradicting I ≰ M.

The noncentral action input must be obtained from the genuine natural action
for each choice of Y₊; it is not inferred merely from Y₊ ≠ 1.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.11(1), p.1124.
-/

public section

open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure
variable {G : Type*} [Group G] [Finite G]

/-- Transport 15.3.2(4) from the fixed Sylow subgroup to any Sylow subgroup of M. -/
theorem uniqueness_of_sylow (T P : Sylow 2 G) (M V X : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hPM : (P : Subgroup G) ≤ M)
    (hMV : M ≤ normalizer (V : Set G))
    (hPX : (P : Subgroup G) ≤ X) (hXM : X ≤ M)
    (h24 : ∀ W : Subgroup G, (T : Subgroup G) ≤ W → W ≤ M →
      twoResidualAmbient W ≤ M ⊓ centralizer (V : Set G) ∨
        Chapter4.UniqueMaximalOvergroup W M)
    (hact : ¬ twoResidualAmbient X ≤ centralizer (V : Set G)) :
    Chapter4.UniqueMaximalOvergroup X M := by
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M (P.subtype hPM) (T.subtype hTM)
  let e := MulAut.conj (m : G)
  have hMe : M.map e.toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer m.property)
  have hTX : (T : Subgroup G) ≤ X.map e.toMonoidHom := by
    intro x hx
    have hx' : (⟨x, hTM hx⟩ : M) ∈ T.subtype hTM := hx
    rw [← hm] at hx'
    obtain ⟨p, hp, hpx⟩ := hx'
    exact mem_map.mpr ⟨p, hPX hp, congrArg Subtype.val hpx⟩
  have hXeM : X.map e.toMonoidHom ≤ M := (map_mono hXM).trans_eq hMe
  have hu : Chapter4.UniqueMaximalOvergroup (X.map e.toMonoidHom) M := by
    rcases h24 _ hTX hXeM with hc | hu
    · exfalso
      apply hact
      intro r hr v hv
      have her : e r ∈ twoResidualAmbient (X.map e.toMonoidHom) := by
        rw [← map_twoResidualAmbient_of_subgroup_image X e.toMonoidHom _ rfl]
        exact mem_map_of_mem _ hr
      have hev : e v ∈ V := (hMV m.property v).mp hv
      have hh := (hc her).2 (e v) hev
      apply e.injective
      simpa only [map_mul] using hh
    · exact hu
  refine ⟨hu.1, hXM, ?_⟩
  intro N hN hXN
  have heq := hu.2.2 (N.map e.toMonoidHom)
    (Theory.GroupTheory.isMaximalTwoLocal_map e hN) (map_mono hXN)
  exact map_injective e.injective (heq.trans hMe.symm)

/-- A strict two-overgroup of a subgroup of half the Sylow order is itself Sylow. -/
theorem sylow_of_strict_overgroup (T : Sylow 2 G) (S P : Subgroup G)
    (hST : S ≤ (T : Subgroup G))
    (hindex : (S.subgroupOf (T : Subgroup G)).index = 2)
    (hP : IsPGroup 2 P) (hSP : S < P) : ∃ U : Sylow 2 G, (U : Subgroup G) = P := by
  have hnotone : (S.subgroupOf P).index ≠ 1 := by
    intro hi
    exact not_le_of_gt hSP (subgroupOf_eq_top.mp (index_eq_one.mp hi))
  have htwo : 2 ≤ (S.subgroupOf P).index := by
    have hpos := (S.subgroupOf P).index_ne_zero_of_finite
    omega
  have hPc : Nat.card S * (S.subgroupOf P).index = Nat.card P := by
    simpa only [Nat.card_congr (subgroupOfEquivOfLe hSP.le).toEquiv] using
      (S.subgroupOf P).card_mul_index
  have hTc : Nat.card S * 2 = Nat.card T := by
    simpa only [hindex, Nat.card_congr (subgroupOfEquivOfLe hST).toEquiv] using
      (S.subgroupOf (T : Subgroup G)).card_mul_index
  obtain ⟨U, hPU⟩ := hP.exists_le_sylow
  refine ⟨U, (eq_of_le_of_card_ge hPU ?_).symm⟩
  calc
    Nat.card U = Nat.card T := by rw [U.card_eq_multiplicity, T.card_eq_multiplicity]
    _ = Nat.card S * 2 := hTc.symm
    _ ≤ Nat.card S * (S.subgroupOf P).index := Nat.mul_le_mul_left _ htwo
    _ = Nat.card P := hPc
/-- Clause (1), once the two-perfectness and nontrivial natural action of Y₊
are supplied. The uniqueness and normalizer inputs are 15.3.2(4) and 15.3.6(2). -/
theorem lemma_15_3_11_1_of_action (T : Sylow 2 G) (M V Yplus S I : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hYM : Yplus ≤ M)
    (hST : S ≤ (T : Subgroup G))
    (hindex : (S.subgroupOf (T : Subgroup G)).index = 2)
    (hNM : normalizer (S : Set G) ≤ M)
    (hMV : M ≤ normalizer (V : Set G))
    (h24 : ∀ X : Subgroup G, (T : Subgroup G) ≤ X → X ≤ M →
      twoResidualAmbient X ≤ M ⊓ centralizer (V : Set G) ∨
        Chapter4.UniqueMaximalOvergroup X M)
    (hperfect : twoResidualAmbient Yplus = Yplus)
    (hact : ¬ Yplus ≤ centralizer (V : Set G))
    (hI : I ∈ outsideFamily Yplus S M) :
    ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = S := by
  have hSI : S ≤ I := le_sup_right.trans hI.1.2
  have hYI : Yplus ≤ I := le_sup_left.trans hI.1.2
  have hSp : IsPGroup 2 S := T.isPGroup'.to_le hST
  obtain ⟨P, hSP⟩ := (hSp.comap_subtype (K := I)).exists_le_sylow
  let Q := (P : Subgroup I).map I.subtype
  have hSQ : S ≤ Q := by
    rw [← map_subgroupOf_eq_of_le hSI]
    exact map_mono hSP
  have hQp : IsPGroup 2 Q := P.isPGroup'.map I.subtype
  have hQM : Q ≤ M := two_overgroup_le_of_index_two T S M Q hST hindex hNM hQp hSQ
  have hQI : Q ≤ I := map_subtype_le _
  refine ⟨P, ?_⟩
  change Q = S
  by_contra hne
  obtain ⟨U, hU⟩ := sylow_of_strict_overgroup T S Q hST hindex hQp
    (lt_of_le_of_ne hSQ (Ne.symm hne))
  have hres : Yplus ≤ twoResidualAmbient (Yplus ⊔ Q) := by
    exact hperfect.ge.trans (residual_mono (show Yplus ≤ Yplus ⊔ Q from le_sup_left))
  have hu := uniqueness_of_sylow T U M V (Yplus ⊔ Q) hTM (hU ▸ hQM) hMV
    (hU ▸ le_sup_right) (sup_le hYM hQM) h24
    (fun hc => hact (hres.trans hc))
  have hcore : pCore 2 I ≠ ⊥ := by
    intro he
    apply hI.1.1
    change (pCore 2 I).map I.subtype = ⊥
    rw [he, Subgroup.map_bot]
  obtain ⟨N, hN, hIN⟩ := Theory.GroupTheory.exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot I hcore
  have hNM' := hu.2.2 N hN ((sup_le hYI hQI).trans hIN)
  exact hI.2 (hNM' ▸ hIN)
end CFSG.Quasithin.Chapter15.Section03.OutsideStructure

end
