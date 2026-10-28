module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis

/-!
# Tensor constituents without a two-core identification

The normal elementary order-eight actor supplies a pure S₃ involution.
Its displacement space is the unique Sylow-invariant component constituent,
with a cubic-translate complement. The previously proved natural and deleted
complement calculations then put the first moved plane in the actual
intersection E. Extraspecial central-kernel lifting gives X₁ ∈ Y.

The argument uses only the indicated local action and intersection data;
it does not require U = O₂(H). The original-flag consumer is in CommonSource.
Source: Aschbacher--Smith 14.4.10(1--2), printed pp.1010--1011.
-/

public noncomputable section
open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.TensorGeometry
open LargerDimension LargerDimension.Tensor LargerDimension.Tensor.Invariant
variable {G : Type*} [Group G] [Finite G]
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {H U T P : Subgroup G} {g : G}

/-- The order-eight actor constructs the constituent without identifying U
with the entire two-core. -/
theorem selectedConstituent (c : CaseFiveCoordinates hAD (V := W) H U)
    (hpT : IsPGroup 2 (c.actorImage T))
    (hXT : conjugateLayer U P g ≤ T)
    [IsElementaryAbelian 2 (c.actorImage (conjugateLayer U P g))]
    (hcard : Nat.card (c.actorImage (conjugateLayer U P g)) = 8)
    (hfixed : c.image P ≤ fixedSpace (sourceTensorAction c.constituent) (c.actorImage T)) :
    Nonempty (c.SelectedConstituent T P g) := by
  have hK := c.actorImage_component
  obtain ⟨s,hs,hs2,hsmem⟩ := Tensor.exists_pure_involution (c.actorImage (conjugateLayer U P g)) hcard
  obtain ⟨n,hn,hfix,hmove⟩ := exists_frame s hs2 hs
  have hsT : (s,(1 : D)) ∈ c.actorImage T := c.actorImage_mono hXT hsmem
  obtain ⟨x,hx,he⟩ := hsmem
  change c.actor x = (s,1) at he
  have hinv : c.actorImage T ≤
      subspaceStabilizer (sourceTensorAction c.constituent) (Invariant.first n hn) := by
    apply le_subspaceStabilizer
    intro a ha z hz
    apply (fixed_iff n hn c.constituent s hfix hmove _).mp
    have hc : (s,(1 : D)) * a = a * (s,1) := by
      apply Prod.ext
      · exact (first_coordinates_commute (c.actorImage T) hpT _ _ hsT ha).eq
      · simp
    rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply,
      (fixed_iff n hn c.constituent s hfix hmove z).mpr hz]
  refine ⟨{
    element := x
    element_mem := hx
    element_ne_one := ?_
    element_centralizes := ?_
    firstSpace := Invariant.first n hn
    secondSpace := Invariant.second n hn
    first_eq_range := ?_
    second_eq_translate := second_translate n hn c.constituent
    isCompl := compl n hn
    first_irreducible := c.frame_first_irreducible hK n hn
    constituentEquiv := firstEquiv n hn
    constituent_equivariant := ?_
    second_invariant := ?_
    T_invariant := hinv
    point_le_fixed := hfixed
    fixed_le_first := ?_
    unique := fun M hM hMT => c.unique_frame_first hK s hsT n hn hfix hmove M hM hMT
  }⟩
  · intro hx1
    rw [hx1,map_one] at he
    exact hs (congrArg Prod.fst he).symm
  · apply mem_centralizer_iff.mpr
    intro y hy
    apply c.actor.injective
    have hym : c.actor y ∈ c.actorImage (component H) := mem_map_of_mem _ hy
    rw [hK] at hym
    have hy1 : (c.actor y).1 = 1 := hym.1
    simp only [map_mul,he,Prod.ext_iff,Prod.fst_mul,Prod.snd_mul,hy1,one_mul,mul_one,and_self]
  · rw [he]
    exact first_range n hn c.constituent s hfix hmove
  · intro a v
    simp only [firstEquiv_apply,pair_component,map_zero]
  · rw [hK]
    exact (prod_mono le_rfl le_top).trans (second_component_invariant n hn c.constituent)
  · intro z hz
    exact (fixed_iff n hn c.constituent s hfix hmove z).mp (hz ⟨(s,1),hsT⟩)


/-- The existing two concrete complement calculations give the first member
of Y from the actual normal elementary actor. No two-core equality is used. -/
theorem first_mem_Y (c : CaseFiveCoordinates hAD (V := W) H U)
    [IsExtraspecial 2 U]
    (S : Sylow 2 (Three × D)) (hS : (S : Subgroup (Three × D)) = c.actorImage T)
    (s : c.SelectedConstituent T P g)
    (hT : T ≤ H) (hUT : U ≤ T) (hPU : P ≤ U)
    (hZP : center U ≤ P.subgroupOf U)
    (hr : Module.finrank (ZMod 2) (c.image P) = 1)
    (hXT : conjugateLayer U P g ≤ T)
    (hPE : P ≤ intersectionLayer U P g)
    (he : IsElementaryAbelian 2 (c.actorImage (conjugateLayer U P g)))
    (hc : Nat.card (c.actorImage (conjugateLayer U P g)) = 8)
    (hn : ((c.actorImage (conjugateLayer U P g)).subgroupOf (c.pointCentralizer P)).Normal)
    (hb : ⁅conjugateLayer U P g, centralLayer U P⁆ ≤ intersectionLayer U P g) :
    first H ∈ YFamily H T P (intersectionLayer U P g) := by
  have hne : c.image P ≠ ⊥ := by intro h; rw [h, finrank_bot] at hr; omega
  obtain ⟨v, hv, hv0⟩ := (c.image P).ne_bot_iff.mp hne
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hr hv hv0
  have hvfirst := s.fixed_le_first (s.point_le_fixed hv)
  let B := c.canonicalForm
  let a : ComplementIntersectionData c.constituent := {
    sylow := S
    actor := c.actorImage (conjugateLayer U P g)
    actor_le_sylow := by rw [hS]; exact c.actorImage_mono hXT
    actor_elementary := he
    actor_card := hc
    point := v
    point_ne_zero := hv0
    point_fixed := by
      intro x hx
      exact s.point_le_fixed hv ⟨x, hS.le hx⟩
    actor_normal := by
      change ((c.actorImage (conjugateLayer U P g)).subgroupOf
        (subspaceKernel (sourceTensorAction c.constituent) (Submodule.span (ZMod 2) {v}) ⊤)).Normal
      rw [← hspan]
      exact hn
    form := B.form
    form_alt := B.alternating c
    form_nondegenerate := B.nondegenerate c
    form_invariant := B.invariant c
    element := c.actor s.element
    element_mem := mem_map_of_mem c.actor.toMonoidHom s.element_mem
    element_ne_one := fun h => s.element_ne_one (c.actor.injective (h.trans c.actor.map_one.symm))
    element_centralizes := by
      rw [← c.actorImage_component]
      apply mem_centralizer_iff.mpr
      rintro _ ⟨k, hk, rfl⟩
      simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
        congrArg c.actor (mem_centralizer_iff.mp s.element_centralizes k hk)
    firstSpace := s.firstSpace
    secondSpace := s.secondSpace
    first_eq_range := s.first_eq_range
    second_eq_translate := s.second_eq_translate
    isCompl := s.isCompl
    point_mem_first := hvfirst }
  have hcalc := source_complement_intersection c.actor_case c.constituent_model a
  change sourceTensorAction c.constituent (cubicActor D) v ∈
    subspaceCommutator (sourceTensorAction c.constituent)
      ((Submodule.span (ZMod 2) {v}).orthogonalBilin B.form ⊓ s.secondSpace)
      (c.actorImage (conjugateLayer U P g) ⊓
        (⊥ : Subgroup Three).prod (AltFive.subgroupOf D)) at hcalc
  have hW : c.image (centralLayer U P) = (c.image P).orthogonalBilin B.form :=
    c.image_centralizer P hPU B.form B.commutes_iff
  rw [← hspan, ← hW, ← c.actorImage_component] at hcalc
  have hbound : subspaceCommutator (sourceTensorAction c.constituent)
      (c.image (centralLayer U P) ⊓ s.secondSpace)
      (c.actorImage (conjugateLayer U P g) ⊓ c.actorImage (component H)) ≤
      c.image (intersectionLayer U P g) := by
    have hsource : ⁅centralLayer U P, conjugateLayer U P g⁆ ≤ intersectionLayer U P g := by
      rwa [commutator_comm]
    apply le_trans _ (c.source_commutator_bound (show centralLayer U P ≤ U from inf_le_left)
      (hXT.trans hT) hsource)
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, hx, w, hw, rfl⟩
      exact Submodule.subset_span ⟨x, hx.1, w, hw.1, rfl⟩
  apply c.first_mem_Y_of_image_le hT hUT hPU hZP
    (hZP.trans (subgroupOf_mono U hPE)) hr
  rw [c.first_image_eq_cubicPlane hPU v hspan]
  apply Submodule.span_le.mpr
  intro w hw
  rcases hw with rfl | rfl
  · exact c.image_mono hPE hv
  · exact hbound hcalc

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.TensorGeometry
