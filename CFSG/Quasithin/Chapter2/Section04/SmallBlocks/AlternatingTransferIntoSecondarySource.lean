module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSquareTransferSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingWeakCoreFusionSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingNoncentralFusionSource
/-!
# Transfer into the original secondary involution centralizer

Square transfer supplies a fused involution outside S. The first residual
factor class is excluded by weak closure. The remaining class fixes a
noncentral involution of P, and the order-nine orbit moves that involution
to the original u using conjugators in M. The residual normal subgroup
preserves the outside-S marking, giving an actual fused involution in T_u.

The residual, coset-class and fixed-vector premises are supplied by the
original full72 factor and marked transvection packets.
Source: Aschbacher--Smith 2.4.29, printed p.546.
-/
public section
namespace CFSG.Quasithin.Chapter2
open Subgroup Stellmacher
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_transfer_into_secondary_of_marks
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
    ∀(L F:Subgroup G), IsPPerfect 2 L →
    S≤F → F≤M → M≤normalizer (F:Set G) → (T:Subgroup G) ⊓ F≤S →
    (frattini S).map S.subtype≤P →
    ∀ y j v:G, y∉S → L≤centralizer ({y}:Set G) → z∈L.pCoreIn 2 →
    j∈(T:Subgroup G) → orderOf j=4 → j^2=z → j∉F →
    (∀i∈(T:Subgroup G), i∉S → orderOf i=2 → IsConj z i →
      (∃m∈M,m*i*m⁻¹=y) ∨ (∃m∈M,m*i*m⁻¹=v)) →
    (orderOf v=2 → ∃b∈P, orderOf b=2 ∧ b∉(center P).map P.subtype ∧ v*b=b*v) →
    ∃r∈(T:Subgroup G) ⊓ centralizer ({u}:Set G), r∉S ∧ orderOf r=2 ∧ IsConj z r := by
  intro P S J u z huP hu2 huJ huZ hZ hMu hi B _ _ f hker hodd L F hp
    hSF hFM hn hTF hphi y j v hy hLC hzL hjT hj4 hjsq hjF hclass hfixed
  obtain ⟨i,hiT,hiS,hi2,hzi⟩ := d.single_alternating_square_fusion_of_marks
    hG T hM hTM hu hST hsingle hA hD eH huP hu2 huJ huZ hZ hMu hi
    F hSF hFM hn hphi j hjT hj4 hjsq hjF
  have hny := d.single_alternating_weak_core_not_isConj_of_marks
    hG T hM hTM hu hST hsingle hA hD eH huP hu2 huJ huZ hZ hMu hi
    f hker hodd L hp y hy hLC hzL
  rcases hclass i hiT hiS hi2 hzi with hm | hm
  · obtain ⟨m,_,hm⟩ := hm
    exact (hny (hzi.trans (isConj_iff.mpr ⟨m,hm⟩))).elim
  · obtain ⟨m,hmM,hmv⟩ := hm
    have hv2:orderOf v=2 := by
      rw [←hmv]
      exact ((MulAut.conj m).orderOf_eq i).trans hi2
    obtain ⟨b,hbP,hb2,hbZ,hvb⟩ := hfixed hv2
    obtain ⟨n,hnM,hnu⟩ := d.single_alternating_noncentral_involutions_conjugator
      hG T hM hTM hu hST hsingle hA hD b hbP hb2 hbZ u huP hu2 huZ
    obtain ⟨r,hr,hrS,hri2,hir⟩ := exists_fused_outside_in_marked_centralizer M
      (T:Subgroup G) S F hTM hSF hTF hn u b v i
      (hMu ▸ inf_le_left) hiT hiS ⟨m,hmM,hmv⟩ ⟨n,hnM,hnu⟩ hvb
    exact ⟨r,hr,hrS,hri2.trans hi2,hzi.trans hir⟩
end CFSG.Quasithin.Chapter2
