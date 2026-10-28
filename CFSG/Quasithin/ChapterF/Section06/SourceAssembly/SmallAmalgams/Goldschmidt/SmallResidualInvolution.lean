module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SmallResidualCrossing
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MaximalNormalizer

/-!
# A small involution centralizer in the opposite local group

The four-group in an A₄ residual centralizes the first two-core and crosses
the opposite two-core. A crossing involution therefore centralizes a
subgroup of index at most two in that opposite core. The literal opposite
local group and its own core are retained, ready for the small residual
recognition theorem.

Source: Goldschmidt (4.2), *Automorphisms of trivalent graphs* (1980),
printed p.392, the choice of v outside the opposite two-core.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem CubicTreeAction.exists_small_centralizer_involution_of_alternating
    (h : CubicTreeAction F)
    (eR : pResidual 2 (F false) ≃* alternatingGroup (Fin 4))
    (eA : ((F false) ⧸ pCore 2 (F false)) ≃* Equiv.Perm (Fin 3)) :
    ∃ v : F true, orderOf v = 2 ∧ v ∉ pCore 2 (F true) ∧
      (centralizer ({v} : Set (F true))).relIndex (pCore 2 (F true)) ≤ 2 := by
  let : Finite (F false) := h.finite false
  let : Finite (F true) := h.finite true
  let T := F false ⊓ F true
  let Q := (F false).pCoreIn 2
  let R := (F true).pCoreIn 2
  let V := ((pResidual 2 (F false)).pCoreIn 2).map (F false).subtype
  have hQT : Q ≤ T := h.local_twoCore_le_overlap false
  have hRT : R ≤ T := h.local_twoCore_le_overlap true
  let : Finite T := Finite.of_injective (inclusion inf_le_left) (inclusion_injective inf_le_left)
  let : Finite R := Finite.of_injective (inclusion (hRT.trans inf_le_right))
    (inclusion_injective (hRT.trans inf_le_right))
  obtain ⟨hsplit, _, hVe, _, hVC, _, _, _⟩ := alternating_residual_core_split eR
  have hVQ : V ≤ Q := by
    apply map_mono
    exact hsplit.symm ▸ le_sup_left
  let : IsElementaryAbelian 2 ((pResidual 2 (F false)).pCoreIn 2) := hVe
  have hVp : IsElementaryAbelian 2 V := IsElementaryAbelian.of_injective
    (equivMapOfInjective ((pResidual 2 (F false)).pCoreIn 2) (F false).subtype
      (F false).subtype_injective).symm.toMonoidHom
    (equivMapOfInjective ((pResidual 2 (F false)).pCoreIn 2) (F false).subtype
      (F false).subtype_injective).symm.injective
  obtain ⟨v, hv, hn⟩ := SetLike.not_le_iff_exists.mp
    (h.alternating_residual_core_not_le_opposite eR)
  have hvB : v ∈ F true := (hQT (hVQ hv)).2
  let vB : F true := ⟨v, hvB⟩
  have hvne : vB ≠ 1 := by
    intro he
    have he' : v = 1 := congrArg Subtype.val he
    exact hn (he' ▸ R.one_mem)
  have hv2 : vB ^ 2 = 1 := by
    apply Subtype.ext
    let : IsElementaryAbelian 2 V := hVp
    exact congrArg (fun z : V => (z : G)) (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (⟨v, hv⟩ : V))
  have hQB : Q ≤ F true := hQT.trans inf_le_right
  have hc : Q.subgroupOf (F true) ≤ centralizer ({vB} : Set (F true)) := by
    intro q hq
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    obtain ⟨w, hw, hwv⟩ := hv
    obtain ⟨a, ha, haq⟩ := hq
    have hh := hVC hw a ha
    have hh' := congrArg (fun z : F false => (z : G)) hh
    change (a : G) * (w : G) = (w : G) * (a : G) at hh'
    change (q : G) * v = v * (q : G)
    simpa only [show (w : G) = v from hwv, show (a : G) = (q : G) from haq] using hh'
  have hQi : Q.relIndex T = 2 := by
    have ha : Q.relIndex (F false) = 6 := by
      change (((pCore 2 (F false)).map (F false).subtype).subgroupOf (F false)).index = 6
      rw [show ((pCore 2 (F false)).map (F false).subtype).subgroupOf (F false) =
        pCore 2 (F false) from comap_map_eq_self_of_injective (F false).subtype_injective _]
      exact SymmetricThreeTwoCore.core_index eA
    have hh := relIndex_mul_relIndex Q T (F false) hQT inf_le_left
    rw [h.overlap_relIndex false, ha] at hh
    omega
  have hQR : Q.relIndex R ≤ 2 := by
    have hh := relIndex_le_of_le_right (H := Q) hRT (hQi ▸ (by decide : 2 ≠ 0))
    exact hh.trans_eq hQi
  have hRmap : R.subgroupOf (F true) = pCore 2 (F true) :=
    comap_map_eq_self_of_injective (F true).subtype_injective _
  refine ⟨vB, orderOf_eq_prime hv2 hvne, ?_, ?_⟩
  · intro hvR
    exact hn (mem_map_of_mem (F true).subtype hvR)
  · have hh := relIndex_le_of_le_left (L := pCore 2 (F true)) hc
      ((Q.subgroupOf (F true)).subgroupOf (pCore 2 (F true))).index_ne_zero_of_finite
    apply hh.trans
    rw [← hRmap, relIndex_subgroupOf (hRT.trans inf_le_right)]
    exact hQR

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
