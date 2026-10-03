module

public import Stellmacher.Recognition.GTwoSixtyFourModel
public import Theory.SpecificGroups.C4SquareSignSwapCentric

/-!
# Exceptional centric subgroups of the order-64 G₂ Sylow

The marked equivalence with the sign-and-swap model transports the intrinsic
centric classification to the actual Sylow intersection. It identifies the
transfer subgroup and both vertex cores, so the two large alternatives retain
their exact ambient subgroup identities. The smaller alternatives transport
elementary abelianness and the actual commuting central-product factors.

Source: Stellmacher (8.6)(a), `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven SevenSix

universe u

private theorem centralProduct_map
    {H G : Type*} [Group H] [Group G]
    {N K : Type u} [Group N] [Group K]
    (X : Subgroup H) (f : H →* G) (hf : Function.Injective f)
    (hX : IsCentralProductModel X N K) :
    IsCentralProductModel (X.map f) N K := by
  obtain ⟨B, C, ⟨eB⟩, ⟨eC⟩, hjoin, hinter, hcomm, hcenter⟩ := hX
  refine ⟨B.map f, C.map f,
    ⟨(B.equivMapOfInjective f hf).symm.trans eB⟩,
    ⟨(C.equivMapOfInjective f hf).symm.trans eC⟩, ?_, ?_, ?_, ?_⟩
  · rw [hjoin, Subgroup.map_sup]
  · rw [← Subgroup.map_inf B C f hf, Subgroup.card_map_of_injective hf, hinter]
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    rw [← map_mul, ← map_mul, hcomm b hb c hc]
  · rw [← Subgroup.map_inf B C f hf]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨zX, hzX, heq⟩ := hcenter hz
    change (zX : H) = z at heq
    refine ⟨⟨f z, Subgroup.mem_map_of_mem f (heq ▸ zX.property)⟩, ?_, rfl⟩
    change (⟨f z, _⟩ : X.map f) ∈ Subgroup.center (X.map f)
    rw [Subgroup.mem_center_iff]
    rintro ⟨_, y, hy, rfl⟩
    apply Subtype.ext
    change f y * f z = f z * f y
    rw [← map_mul, ← map_mul]
    apply congrArg f
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hzX ⟨y, hy⟩)
    simpa only [Subgroup.coe_mul, heq] using h

/-- A centric subgroup outside the canonical transfer subgroup, whose
automorphism group is not a two-group, is elementary abelian of order eight,
a central product `C₄ * Q₈`, or one of the two distinguished vertex cores. -/
public theorem gTwo_card64_centric_classification
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64)
    (X : Subgroup G) (hXS : X ≤ (data.sylowIntersection : Subgroup G))
    (hc : subgroupCentralizerIn (data.sylowIntersection : Subgroup G) X ≤ X)
    (haut : ¬ IsPGroup 2 (MulAut X))
    (hout : ¬ X.subgroupOf (data.sylowIntersection : Subgroup G) ≤
      gTwoCard64TransferSubgroup data) :
    letI := data.groupK
    letI := data.finiteK
    (IsElementaryAbelian 2 X ∧ Nat.card X = 8) ∨
      IsCentralProductModel X C4 Q8 ∨
      X = (QAt data.Γ data.criticalPath.a).map data.embedding ∨
      X = (QAt data.Γ data.criticalPath.firstStep).map data.embedding := by
  let := data.groupK
  let := data.finiteK
  let S := (data.sylowIntersection : Subgroup G)
  obtain ⟨e, hU, hQa, hQb⟩ := gTwo_card64_marked_equiv data hcard
  let Y := (X.subgroupOf S).map e.toMonoidHom
  let f : C4SquareSignSwap.Model →* G := S.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := S.subtype_injective.comp e.symm.injective
  have map_back (H : Subgroup G) (hHS : H ≤ S) :
      ((H.subgroupOf S).map e.toMonoidHom).map f = H := by
    rw [Subgroup.map_map]
    have he : f.comp e.toMonoidHom = S.subtype := by ext x; simp [f]
    rw [he, Subgroup.map_subgroupOf_eq_of_le hHS]
  have hYX : Y.map f = X := map_back X hXS
  let eY : Y ≃* X := hYX ▸ Y.equivMapOfInjective f hf
  have hcY : Subgroup.centralizer (Y : Set C4SquareSignSwap.Model) ≤ Y := by
    intro y hy
    have hx : (e.symm y : G) ∈ X := by
      apply hc
      refine ⟨(e.symm y).property, ?_⟩
      intro x hx
      have h := hy (e ⟨x, hXS hx⟩)
        (Subgroup.mem_map_of_mem e.toMonoidHom hx)
      have h' := congrArg f h
      simpa [f] using h'
    exact ⟨e.symm y, hx, e.apply_symm_apply y⟩
  have hautY : ¬ IsPGroup 2 (MulAut Y) := by
    intro h
    exact haut (h.of_equiv (MulAut.congr eY))
  have houtY : ¬ Y ≤ C4SquareSignSwap.transfer := by
    intro h
    apply hout
    apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    simpa only [hU] using h
  rcases C4SquareSignSwap.centric_classification Y hcY hautY houtY with
    hEA | hCP | hcore | hcore
  · left
    let _ : IsElementaryAbelian 2 Y := hEA.1
    have hEA' := IsElementaryAbelian.map (p := 2) (A := Y) f
    rw [hYX] at hEA'
    exact ⟨hEA', (Nat.card_congr eY.toEquiv).symm.trans hEA.2⟩
  · right; left
    have h := centralProduct_map Y f hf (show IsCentralProductModel Y C4 Q8 from hCP)
    rwa [hYX] at h
  · right; right; left
    rw [← hQa] at hcore
    have h := congrArg (fun H : Subgroup C4SquareSignSwap.Model => H.map f) hcore
    rw [hYX, map_back _ (gTwo_card64_cores_le_sylow data).1] at h
    exact h
  · right; right; right
    rw [← hQb] at hcore
    have h := congrArg (fun H : Subgroup C4SquareSignSwap.Model => H.map f) hcore
    rw [hYX, map_back _ (gTwo_card64_cores_le_sylow data).2] at h
    exact h

end Stellmacher.Recognition
