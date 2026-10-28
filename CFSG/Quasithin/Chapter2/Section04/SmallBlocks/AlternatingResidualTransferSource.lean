module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingOutsideClassesSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTransferIntoSecondarySource
public import Theory.GroupTheory.CentralSquareCoset

/-!
# Transfer into the original secondary involution centralizer

The actual outside classes supply a square root of the marked central
involution outside the residual transfer subgroup. Square transfer produces
a fused involution outside the original selected Sylow. Its first possible
class contradicts weak closure and the odd residual image; its second class
fixes a noncentral core involution, which the actual maximal subgroup moves
to the retained secondary involution. The residual transfer subgroup is
normal in that maximal subgroup, so this movement preserves the outside mark.

Source: Aschbacher--Smith 2.4.29, printed p.546.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_residual_transfer_of_marks
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
    (frattini S).map S.subtype≤P →
    ∃r∈(T:Subgroup G) ⊓ centralizer ({u}:Set G), r∉S ∧ orderOf r=2 ∧ IsConj z r := by
  classical
  intro P S J u z huP hu2 huJ huZ hZ hMu hi hphi
  have hz2:orderOf z=2 :=
    (orderOf_injective d.H.subtype d.H.subtype_injective (eH.symm BinaryFiveAffine.standardZ)).trans
      ((eH.symm.orderOf_eq _).trans BinaryFiveAffine.standardZ_order)
  obtain ⟨y,a,L,hyT,hyS,hyZ,haP,_ha4,ha2,hc,_hLM,hp,hzL,hLC,hclass,hfixed⟩ :=
    d.single_alternating_outside_classes_of_center_mark hG T hM hTM hu hST hsingle hA hD
      z hz2 hZ
  obtain ⟨c⟩ := d.single_alternating_residual_factors hG T hM hTM hu hST hsingle hA hD
  let F := c.transferSubgroup
  have hPS:P≤S := (d.single_borel_core_placement hsingle).1
  have hSM:S≤M := hST.le.trans hTM
  have hSF:S≤F := by
    change S≤c.transferSubgroup
    rw [c.transferSubgroup_def]
    exact le_sup_right
  have hFM:F≤M := by
    change c.transferSubgroup≤M
    rw [c.transferSubgroup_def]
    exact sup_le (map_subtype_le _) hSM
  have hTF:(T:Subgroup G) ⊓ F≤S := by
    rw [inf_comm]
    exact c.transfer_subgroup_inf_sylow.le
  have haF:a∈F := hSF (hPS haP)
  have hy2:y^2=1 ∨ y^2=z := by
    have hh:y^2∈zpowers z := hZ ▸ hyZ
    rw [mem_zpowers_iff_mem_range_orderOf,hz2] at hh
    obtain ⟨n,hn,he⟩:=Finset.mem_image.mp hh
    have hn2:n<2:=Finset.mem_range.mp hn
    interval_cases n <;> simp_all
  obtain ⟨j,hjT,hj4,hjsq,hjF⟩ := exists_order_four_central_square_outside
    (T:Subgroup G) F y a z hyT (hST.le (hPS haP))
      (fun hyF=>hyS (hTF ⟨hyT,hyF⟩)) haF hy2 ha2 hz2 hc.eq
  have hker:c.action.ker.map M.subtype≤P := by
    rw [c.action_ker]
    exact (d.single_alternating_maximal_core_of_centralizer_bot
      hG T hM hTM hu hST hsingle hA hD).1.le
  have hodd:Odd (Nat.card (pResidual 2 BinaryFourPlus.Wreath)) := by
    rw [c.quotient_residual_card]
    decide
  exact d.single_alternating_transfer_into_secondary_of_marks
    hG T hM hTM hu hST hsingle hA hD eH huP hu2 huJ huZ hZ hMu hi
    c.action hker hodd L F hp hSF hFM c.transfer_subgroup_normalized hTF hphi
    y j (y*a) hyS hLC hzL hjT hj4 hjsq hjF
    (fun i hiT hiS hi2 _=>hclass i hiT hiS hi2) hfixed
end CFSG.Quasithin.Chapter2
