module
public import Theory.GroupTheory.WeakClosedCoreFusion
public import Theory.SpecificGroups.BinaryFiveAffine.SylowInvolutions
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondarySylowSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingWeakClosureSource
/-!
# Excluding the first residual-factor fusion class

The original selected pair involution u separates z from the noncentral
involutions of P, so z is weakly closed in P. A two-perfect factor centralizing
y has its two-core killed by the marked quotient of C_G(z) with odd
 two-residual. If that core contains z, conjugating y to z contradicts weak
closure whenever y lies outside S.

The marked quotient and residual factor are supplied by the full72 residual
packet. Source: Aschbacher--Smith 2.4.29, printed p.546.
-/
public section
namespace CFSG.Quasithin.Chapter2
open Subgroup Stellmacher
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_weak_core_not_isConj_of_marks
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
    ∀{B:Type*} [Group B] [Finite B] (f:M→*B),
    f.ker.map M.subtype≤P → Odd (Nat.card (pResidual 2 B)) →
    ∀ (L:Subgroup G), IsPPerfect 2 L →
    ∀y:G, y∉S → L≤centralizer ({y}:Set G) → z∈L.pCoreIn 2 → ¬IsConj z y := by
  intro P S J u z huP hu2 huJ huZ hZ hMu hi B _ _ f hker hodd L hp y hy hLC hzL
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
  have hzS:z∈S := (d.single_borel_core_placement hsingle).1 (map_subtype_le _ hzZ)
  exact not_isConj_of_weak_closed_core_and_odd_residual M P f hker hodd z y
    hcent hweak L hp hLC hzL (fun hh=>hy (hh.symm ▸ hzS))
end CFSG.Quasithin.Chapter2
