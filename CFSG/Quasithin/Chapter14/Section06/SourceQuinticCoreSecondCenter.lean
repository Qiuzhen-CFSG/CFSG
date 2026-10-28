module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCoreCenter
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveRootAction

/-!
# The second center of the original large quintic core

Its intersection with the actual five-residual is the original span.
Coprime decomposition reduces any remaining second-center element to an
actual five-fixed root. Such a root has full-span commutator with the residual,
contradicting central commutators. No core model or seed is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original quintic span is the full second center in the large branch. -/
theorem source_quintic_large_core_second_center
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    (Subgroup.upperCentralSeries (H.pCoreIn 2) 2).map (H.pCoreIn 2).subtype =
      conjugateSpanBy (localModule T M) H := by
  classical
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let R := ⁅Q,A⁆
  let Z := centralInvolutions T
  let P := (Subgroup.upperCentralSeries Q 2).map Q.subtype
  change P = U
  have hPQ : P ≤ Q := map_subtype_le _
  have hcenter : (center Q).map Q.subtype = Z :=
    source_quintic_full_core_center hG T hempty hM hu hmany hcard e H hH hi
  obtain ⟨_,_,_,_,_,_,_,hupper,hRcenter,_⟩ := source_quintic_large_five_residual_structure
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
  change (center R).map R.subtype = Z at hRcenter
  have hAQ : A ≤ normalizer (Q : Set G) := hAH.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hRQ : R ≤ Q := le_normalizer_iff_commutator_le_left.mp hAQ
  have hAP : A ≤ normalizer (P : Set G) := hAQ.trans
    (normalizer_le_normalizer_characteristic_image Q (Subgroup.upperCentralSeries Q 2))
  have hPcomm : ⁅P,Q⁆ ≤ Z := by
    have hh := map_mono (f := Q.subtype)
      (Subgroup.commutator_upperCentralSeries_top_le (G := Q) 1)
    rw [map_commutator,←MonoidHom.range_eq_map,range_subtype,
      Subgroup.upperCentralSeries_one,hcenter] at hh
    exact hh
  have hPRU : P ⊓ R ≤ U := by
    intro x hx
    have hxupper : (⟨x,hx.2⟩ : R) ∈ Subgroup.upperCentralSeries R 2 := by
      rw [Subgroup.mem_upperCentralSeries_succ_iff]
      intro r
      rw [Subgroup.upperCentralSeries_one]
      have hz : ⁅x,(r : G)⁆ ∈ Z := hPcomm
        (commutator_mem_commutator hx.1 (hRQ r.property))
      rw [←hRcenter] at hz
      obtain ⟨z,hz,he⟩ := hz
      have he' : z = ⁅(⟨x,hx.2⟩ : R),r⁆ := Subtype.ext he
      exact he' ▸ hz
    exact hupper.le (mem_map_of_mem R.subtype hxupper)
  have hCU : P ⊓ centralizer (A : Set G) ≤ U := by
    intro t ht
    by_cases htR : t ∈ R
    · exact hPRU ⟨ht.1,htR⟩
    have hroot := (source_quintic_large_five_root_action
      hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
      (source_quintic_large_five_residual_centralizer
        hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA)
      t ⟨hPQ ht.1,ht.2⟩ htR).2
    change ⁅R,zpowers t⁆ = U at hroot
    have hUZ : U ≤ Z := by
      rw [←hroot,commutator_comm]
      exact (commutator_mono (zpowers_le.mpr ht.1) hRQ).trans hPcomm
    have hh := card_le_of_le hUZ
    have hUcard : Nat.card U = 32 := (source_quintic_span_card_and_core_radical
      hG T hempty hM hu hmany hcard e H hH hi).1
    have hZcard : Nat.card Z = 2 := plane_centralInvolutions_card T M hM.1.2 hcard e
    rw [hUcard,hZcard] at hh
    omega
  have hpP : IsPGroup 2 P := (isPGroup_pCoreIn 2 H).to_le hPQ
  let : Group.IsNilpotent P := hpP.isNilpotent
  have hcop : (Nat.card P).Coprime (Nat.card A) := by
    obtain ⟨n,hn⟩ := hpP.exists_card_eq
    rw [hn,hA]
    exact (by decide : Nat.Coprime 2 5).pow_left n
  have hdecomp : P = ⁅P,A⁆ ⊔ (P ⊓ centralizer (A : Set G)) :=
    eq_commutator_sup_centralizer_of_solvable_coprime P A hAP
      (inferInstance : Group.IsSolvable P) hcop.symm
  have hPAU : ⁅P,A⁆ ≤ U := hPRU.trans' (le_inf
    (le_normalizer_iff_commutator_le_left.mp hAP) (commutator_mono hPQ le_rfl))
  apply le_antisymm
  · rw [hdecomp]
    exact sup_le hPAU hCU
  · have hUQ : U ≤ Q := (source_quintic_full_core_layers
      hG T hempty hM hu hmany hcard e H hH hi).1.ge.trans (commutator_le_self Q)
    intro u huU
    refine mem_map_of_mem Q.subtype (show (⟨u,hUQ huU⟩ : Q) ∈
      Subgroup.upperCentralSeries Q 2 from ?_)
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro q
    rw [Subgroup.upperCentralSeries_one]
    have hz : ⁅u,(q : G)⁆ ∈ Z := (source_quintic_core_commutators
      hG T hempty hM hu hmany hcard e H hH hi).2.le
        (commutator_mem_commutator huU q.property)
    rw [←hcenter] at hz
    obtain ⟨z,hz,he⟩ := hz
    have he' : z = ⁅(⟨u,hUQ huU⟩ : Q),q⁆ := Subtype.ext he
    exact he' ▸ hz

end CFSG.Quasithin.Chapter14.Section06
