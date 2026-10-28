module
public import Theory.GroupTheory.WeakClosedSquareFusion
public import Theory.SpecificGroups.BinaryFiveAffine.SylowInvolutions
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondarySylowSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingWeakClosureSource
/-!
# Square transfer in the original single-A5 source

The selected involution u separates the central involution z from all
noncentral involutions of P. The original maximal-core calculation gives
C_G(z)=M, so a normal subgroup F of M containing S separates an order-four
class whose square is z. The ambient simple group has no subgroup normal
of index two; transfer therefore puts a conjugate of z outside S in T.

Source: Aschbacher--Smith 2.4.29, printed p.546.
-/
public section
namespace CFSG.Quasithin.Chapter2
open Subgroup Stellmacher
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_square_fusion_of_marks
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hu : ∀N:Subgroup G, IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M)
    (hST : (d.S:Subgroup d.H).map d.H.subtype<(T:Subgroup G))
    (hsingle:d.L0=d.block)
    (hA:ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD:(T:Subgroup G) ⊓ centralizer (d.block.map d.H.subtype:Set G)=⊥)
    (eH:d.H≃*BinaryFiveAffine.W) :
    let P := ((pResidual 2 (M ⊓ d.block.map d.H.subtype : Subgroup G)).map
      (M ⊓ d.block.map d.H.subtype).subtype).pCoreIn 2
    let S := (d.S:Subgroup d.H).map d.H.subtype
    let J := elementaryAbelianMaxJ S
    let u:G := (eH.symm BinaryFiveAffine.t:d.H)
    let z:G := (eH.symm BinaryFiveAffine.standardZ:d.H)
    u∈P → orderOf u=2 → u∈(center J).map J.subtype →
    u∉(center P).map P.subtype → (center P).map P.subtype=zpowers z →
    M ⊓ centralizer ({u}:Set G)=(T:Subgroup G) ⊓ centralizer ({u}:Set G) →
    ((T:Subgroup G) ⊓ centralizer ({u}:Set G)).relIndex (T:Subgroup G)=2 →
    ∀F:Subgroup G, S≤F → F≤M → M≤normalizer (F:Set G) →
    (frattini S).map S.subtype≤P →
    ∀j∈(T:Subgroup G), orderOf j=4 → j^2=z → j∉F →
    ∃i∈(T:Subgroup G), i∉S ∧ orderOf i=2 ∧ IsConj z i := by
  intro P S J u z huP hu2 huJ huZ hZ hMu hi F hSF _hFM hn hphi j hjT hj4 hjsq hjF
  have huT:u∈(T:Subgroup G) :=
    ((map_subtype_le _).trans ((sSup_le fun _ h=>h.1).trans hST.le)) huJ
  have hzZ:z∈(center P).map P.subtype := hZ.symm ▸ mem_zpowers z
  have hz2:orderOf z=2 :=
    (orderOf_injective d.H.subtype d.H.subtype_injective (eH.symm BinaryFiveAffine.standardZ)).trans
      ((eH.symm.orderOf_eq _).trans BinaryFiveAffine.standardZ_order)
  have hsep := (d.single_alternating_secondary_sylow_of_marked_centralizer
    hG T hM hTM hu hST hsingle hA u hu2 huT hMu hi).2.2 z hzZ
  have hweak := d.single_alternating_center_weak_closed_of_marks
    hG T hM hTM hu hST hsingle hA hD u z huP hu2 huZ hzZ hz2 hsep
  have hcent:centralizer ({z}:Set G)=M := by
    have he := (d.single_alternating_maximal_core_of_centralizer_bot
      hG T hM hTM hu hST hsingle hA hD).2
    rw [hZ] at he
    apply le_antisymm
    · rw [he,le_centralizer_iff,zpowers_le]
      intro x hx
      exact mem_centralizer_singleton_iff.mp hx
    · rw [he]
      exact centralizer_le (show ({z}:Set G)⊆(zpowers z:Set G) from
        Set.singleton_subset_iff.mpr (mem_zpowers z))
  have hno:∀K:Subgroup G, K.Normal→K.index≠2 := by
    let : IsSimpleGroup G := hG.simple
    intro K hnormal hindex
    rcases hnormal.eq_bot_or_eq_top with hb|ht
    · have hc:Nat.card G=2 := by simpa only [hb,index_bot] using hindex
      let : IsCyclic G := isCyclic_of_prime_card hc
      exact hG.nonabelian inferInstance
    · simp only [ht,index_top] at hindex
      omega
  exact T.exists_isConj_involution_outside_of_weak_closed_square hno S P F hST.le
    (d.single_alternating_sylow_index_source hG T hM hTM hu hST hsingle hA).1
    hSF hphi j z hjT hj4 hjsq hjF hz2 (hcent ▸ hn) hweak
end CFSG.Quasithin.Chapter2
