module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeCubicIndex
public import Theory.GroupTheory.NormalizedSupCard

/-!
# A cubic index bound from the two full original cores

The full original orbit moves R0 onto the join of [R0,L] and its exchanged
copy. Both lie in R0 and the first is normalized by R0, so their product
has order at most the square of the full MS core order. No commutation
of the two components or of their full cores is assumed. When the full
core has order64, the actual containing core Q has cubic fixed index at
most65536. The two remaining small primes will be treated separately.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02 ChapterC.BinaryMS
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

omit [Finite G] in
private theorem relative_commutator_sup (R A B : Subgroup G)
    (ha : A ≤ normalizer (R : Set G)) (hb : B ≤ normalizer (R : Set G)) :
    ⁅R,A ⊔ B⁆ = ⁅R,A⁆ ⊔ ⁅R,B⁆ := by
  let W := ⁅R,A⁆ ⊔ ⁅R,B⁆
  have hWR : W ≤ R := sup_le (le_normalizer_iff_commutator_le_left.mp ha)
    (le_normalizer_iff_commutator_le_left.mp hb)
  have haW : A ≤ normalizer (W : Set G) := le_normalizer_iff_commutator_le_right.mpr
    ((commutator_mono le_rfl hWR).trans (by rw [commutator_comm]; exact le_sup_left))
  have hbW : B ≤ normalizer (W : Set G) := le_normalizer_iff_commutator_le_right.mpr
    ((commutator_mono le_rfl hWR).trans (by rw [commutator_comm]; exact le_sup_right))
  apply le_antisymm ?_ (sup_le (commutator_mono le_rfl le_sup_left)
    (commutator_mono le_rfl le_sup_right))
  rw [commutator_comm]
  exact commutator_sup_le_of_relative_normal (A ⊔ B) A B R W (sup_le haW hbW)
    le_sup_left le_sup_right (by rw [commutator_comm]; exact le_sup_left)
    (by rw [commutator_comm]; exact le_sup_right)

/-- The orbit movement of the original join core is bounded by the square
of the full MS core order, using the actual exchanged full core. -/
theorem normalizerEscape_orbit_core_moved_card_le_square
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (s : NaturalData D)
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal) :
    Nat.card (⁅(localJoin T L).pCoreIn 2,localOrbit T L⁆ : Subgroup G) ≤
      Nat.card ((commutatorCore
        (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))).map
          (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))).subtype)^2 := by
  let R := (localJoin T L).pCoreIn 2
  let C := ⁅R,L⁆
  let Ct := C.map (MulAut.conj s.exchange).toMonoidHom
  have hJR : localJoin T L ≤ normalizer (R : Set G) :=
    (localJoin T L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have ht : R.map (MulAut.conj s.exchange).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (hJR (mem_sup_right s.exchange_mem))
  have hCt : Ct = ⁅R,L.map (MulAut.conj s.exchange).toMonoidHom⁆ := by
    dsimp only [Ct,C]
    rw [map_commutator,ht]
  have hLt : L.map (MulAut.conj s.exchange).toMonoidHom ≤ localJoin T L :=
    ((orbit_eq_pair s).symm ▸ le_sup_right).trans le_sup_left
  have hCtR : Ct ≤ R := hCt ▸ le_normalizer_iff_commutator_le_left.mp (hLt.trans hJR)
  have hgen : ⁅R,localOrbit T L⁆ = C ⊔ Ct := by
    rw [orbit_eq_pair s,relative_commutator_sup R L _
      (((le_componentOrbit L T).trans le_sup_left).trans hJR) (hLt.trans hJR),←hCt]
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes C Ct
    (hCtR.trans (normalizer_commutator_ge_left R L))
  have hpos : 0 < Nat.card (C ⊓ Ct : Subgroup G) := Nat.card_pos
  have hcard : Nat.card Ct = Nat.card C := card_map_of_injective (MulAut.conj s.exchange).injective
  rw [hcard] at hh
  rw [←normalizerEscape_join_core_component D (selected_nonnormal s) hout s.quotient]
  change Nat.card (⁅R,localOrbit T L⁆ : Subgroup G) ≤ Nat.card C^2
  rw [hgen]
  nlinarith

namespace Parabolics
open Chapter1 Chapter1.XiEmbedding
variable {H P : Subgroup G} {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

/-- Order64 for the full original MS core bounds the original cubic
centralizer index in Q by65536, with no whole-core replacement. -/
theorem Data.collapsed_fullCore64_cubic_index (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal)
    (hcard : Nat.card ((commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))).map
        (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))).subtype) = 64) :
    let Q := (enlargedResidual T L H).pCoreIn 2
    (Q ⊓ centralizer (P : Set G)).relIndex Q ≤ 65536 := by
  let Q := (enlargedResidual T L H).pCoreIn 2
  let N := Q ⊓ (localJoin T L).pCoreIn 2
  let M := ⁅N,P⁆
  let C := N ⊓ centralizer (P : Set G)
  have hPJ : P ≤ localJoin T L :=
    hi.complement_le.trans ((map_subtype_le _).trans h.le_join)
  have hPQ : P ≤ normalizer (Q : Set G) :=
    (hi.complement_le.trans h.residual_le_enlargedResidual).trans
      ((enlargedResidual T L H).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hPR : P ≤ normalizer ((localJoin T L).pCoreIn 2 : Set G) :=
    hPJ.trans ((localJoin T L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hPN : P ≤ normalizer (N : Set G) :=
    (le_inf hPQ hPR).trans inf_normalizer_le_normalizer_inf
  have hN2 : IsPGroup 2 N := (isPGroup_pCoreIn 2 _).to_le inf_le_left
  have hcop : Nat.Coprime (Nat.card P) (Nat.card N) :=
    IsPGroup.coprime_card_of_ne 3 2 (by decide) P N hi.odd_complement.isPGroup hN2
  have hMcard : Nat.card M ≤ 4096 := by
    have hle : M ≤ ⁅(localJoin T L).pCoreIn 2,localOrbit T L⁆ :=
      commutator_mono inf_le_right (hi.complement_le.trans h.residual_le_orbit)
    have hb := normalizerEscape_orbit_core_moved_card_le_square D s hout
    rw [hcard] at hb
    exact (Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)).trans hb
  let : Group.IsNilpotent N := hN2.isNilpotent
  have hdec : N = M ⊔ C :=
    eq_commutator_sup_centralizer_of_solvable_coprime N P hPN inferInstance hcop
  have hCN : C.relIndex N ≤ 4096 := by
    rw [hdec,relIndex_sup_of_normalizes M C (inf_le_left.trans (normalizer_commutator_ge_left N P))]
    exact (Nat.le_of_dvd Nat.card_pos (relIndex_dvd_card C M)).trans hMcard
  have hNQ : N.relIndex Q = 16 := by
    have hh := h.collapsed_core_centralizer_relIndex f hi hP hc
    rwa [h.core_action_kernel_eq_intersection f] at hh
  have hCQ : C.relIndex Q ≤ 65536 := by
    rw [←relIndex_mul_relIndex C N Q inf_le_left inf_le_left,hNQ]
    omega
  exact (relIndex_le_of_le_left (show C ≤ Q ⊓ centralizer (P : Set G) from
    inf_le_inf_right _ inf_le_left) (show C.relIndex Q ≠ 0 from index_ne_zero_of_finite)).trans hCQ

end Parabolics
end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
