module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Transport

/-! Intrinsic recognition of the six noncentral four-groups inside a
forty-five-point rectangle. A subgroup of order four containing no conjugate
of the marked involution is one of the six literal four-subgroups. -/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessHeld
open UniquenessLinear UniquenessMathieu.SourceNormalizer
open UniquenessLinear.PlaneTensor
open UniquenessLinear.PlaneCensus (Code)
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

private theorem exceptional_of_not_fused (h : (F.fusion F.plane).ncard=45)
    (x : Code) (hx : x≠0) (hn : ¬IsConj z (element F x)) : Sextet.exceptional x=true := by
  apply (Sextet.exceptional_iff x).mpr
  refine ⟨hx,?_⟩
  have hf : Sextet.fused x≠true := fun he => hn ((plane_fusion_iff_fused F h x).mpr he)
  cases he : Sextet.fused x <;> simp_all

/-- A four-subgroup avoiding the distinguished involution class is exactly
one of the six intrinsic marked fours. -/
theorem exists_unique_planeFour_of_pure_four
    (h : (F.fusion F.plane).ncard=45) (A : Subgroup G)
    (hAP : A≤F.plane) (hA : Nat.card A=4)
    (hpure : ∀ a∈A, a≠1 → ¬IsConj z a) : ∃! i : Fin 6, A=planeFour F i := by
  have hA0 : A≠⊥ := by intro he; rw [he,card_bot] at hA; omega
  have hex : ∃ a∈A, a≠1 := by
    by_contra hh
    push Not at hh
    exact hA0 (eq_bot_iff.mpr (fun a ha => mem_bot.mpr (hh a ha)))
  obtain ⟨a,ha,ha1⟩ := hex
  obtain ⟨i,hi,hui⟩ := exists_unique_planeFour F h a (hAP ha) ha1 (hpure a ha ha1)
  have hle : A≤planeFour F i := by
    intro b hb
    by_cases hb1 : b=1
    · exact hb1 ▸ (planeFour F i).one_mem
    by_cases hba : b=a
    · exact hba ▸ hi
    obtain ⟨x,hx⟩ := (sourceEquiv F).surjective ⟨a,hAP ha⟩
    obtain ⟨y,hy⟩ := (sourceEquiv F).surjective ⟨b,hAP hb⟩
    have hxa : element F x=a := congrArg Subtype.val hx
    have hyb : element F y=b := congrArg Subtype.val hy
    have hx0 : x≠0 := fun he => ha1 (hxa.symm.trans (he ▸ element_zero F))
    have hy0 : y≠0 := fun he => hb1 (hyb.symm.trans (he ▸ element_zero F))
    have hxy : x≠y := fun he => hba (hyb.symm.trans ((congrArg (element F) he).symm.trans hxa))
    have hxy0 : x ^^^ y≠0 := fun he => hxy (BitVec.xor_eq_zero_iff.mp he)
    have hxyA : element F (x ^^^ y)∈A := by rw [element_xor,hxa,hyb]; exact A.mul_mem ha hb
    have hxy1 : element F (x ^^^ y)≠1 := by
      intro he
      apply hxy0
      exact element_injective F (he.trans (element_zero F).symm)
    have hex := exceptional_of_not_fused F h x hx0 (hxa.symm ▸ hpure a ha ha1)
    have hey := exceptional_of_not_fused F h y hy0 (hyb.symm ▸ hpure b hb hb1)
    have hexy := exceptional_of_not_fused F h (x ^^^ y) hxy0 (hpure _ hxyA hxy1)
    obtain ⟨j,hj⟩ := Sextet.exceptional_triple x y hxy hex hey hexy
    have hxj : x∈Sextet.line j := by rw [←hj]; simp
    have hyj : y∈Sextet.line j := by rw [←hj]; simp
    have hji : j=i := hui j ((mem_planeFour F j a).mpr ⟨x,hxj,hxa⟩)
    exact hji ▸ ((mem_planeFour F j b).mpr ⟨y,hyj,hyb⟩)
  have he : A=planeFour F i := eq_of_le_of_card_ge hle (by rw [hA,planeFour_card])
  exact ⟨i,he,fun j hj => planeFour_injective F (hj.symm.trans he)⟩

end Theory.GroupTheory.TransvectionFive.UniquenessHeld
