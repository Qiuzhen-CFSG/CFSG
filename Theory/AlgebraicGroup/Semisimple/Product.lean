module

public import Theory.AlgebraicGroup.Irreducible.Product
public import Theory.AlgebraicGroup.Radical.Existence
public import Theory.AlgebraicGroup.Semisimple.Defs

/-!
# Semisimplicity of algebraic-group products

The direct product of two semisimple algebraic groups is semisimple.  Its
connectedness follows from irreducibility of products.  For radical
triviality, project an arbitrary connected normal solvable closed subgroup to
each factor.  Its two closed images are again connected, normal, and solvable,
so semisimplicity of the factors makes both images trivial; the product
projections then detect that the original subgroup is trivial.

This is the product reduction used for the semisimple root-system
decomposition in GLS3, Chapter 1, Theorem 1.10.6.
-/

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private theorem variety_prod_isConnected
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (hG : Variety.IsConnected G) (hH : Variety.IsConnected H) :
    Variety.IsConnected (Variety.prod G H) := by
  have hI := prodSet_irreducible_of_irreducible
    (connectedAlgebraicGroup_irreducible G hG)
    (connectedAlgebraicGroup_irreducible H hH)
  have hprod : Variety.prodSet
      (Set.univ : Set (Variety.Point G))
      (Set.univ : Set (Variety.Point H)) =
      (Set.univ : Set (Variety.Point (Variety.prod G H))) := by
    ext z
    simp [Variety.prodSet]
  rw [hprod] at hI
  exact hI.isConnected

omit [IsAlgClosed k] in
private theorem ClosedSubgroup.carrierVariety_isConnected
    {G : Variety k} [AlgebraicGroup G] (S : ClosedSubgroup G)
    (hS : _root_.IsConnected (S : Set (Variety.Point G))) :
    Variety.IsConnected S.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph S.isZariskiClosed
  let : ConnectedSpace
      {x : Variety.Point G // x ∈ (S : Set (Variety.Point G))} :=
    Subtype.connectedSpace hS
  let : ConnectedSpace (Variety.Point S.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

private theorem Morphism.imageClosedSubgroup_normal_of_normal_of_surjective
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : Morphism G H) (hf : Function.Surjective f.onPoints)
    (N : ClosedSubgroup G) (hN : N.toSubgroup.Normal) :
    (f.comp N.inclusion).imageClosedSubgroup.toSubgroup.Normal := by
  let q := f.comp N.inclusion
  have hq : q.imageClosedSubgroup.toSubgroup =
      N.toSubgroup.map f.onPoints := by
    ext y
    constructor
    · intro hy
      change y ∈ q.image at hy
      obtain ⟨x, rfl⟩ := hy
      exact ⟨N.inclusion.onPoints x, (N.pointEquiv x).property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      change f.onPoints x ∈ q.image
      let xN : Variety.Point N.carrierVariety := N.pointEquiv.symm ⟨x, hx⟩
      refine ⟨xN, ?_⟩
      change f.onPoints (N.inclusion.onPoints xN) = f.onPoints x
      congr 1
  rw [hq]
  exact Subgroup.Normal.map hN f.onPoints hf

/-- The direct product of two semisimple algebraic groups is semisimple. -/
public theorem semisimple_product
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (hG : IsSemisimpleAlgebraicGroup G)
    (hH : IsSemisimpleAlgebraicGroup H) :
    IsSemisimpleAlgebraicGroup (Variety.prod G H) := by
  refine ⟨variety_prod_isConnected hG.1 hH.1, ?_⟩
  intro R hR
  letI : AlgebraicGroup R.carrierVariety := R.carrierAlgebraicGroup
  have hRvar : Variety.IsConnected R.carrierVariety :=
    R.carrierVariety_isConnected hR.connected
  let pG := Morphism.fst G H
  let pH := Morphism.snd G H
  let fG := pG.comp R.inclusion
  let fH := pH.comp R.inclusion
  let I_G := fG.imageClosedSubgroup
  let I_H := fH.imageClosedSubgroup
  have hpGsurj : Function.Surjective pG.onPoints :=
    Function.LeftInverse.surjective (product_fst_inl G H)
  have hpHsurj : Function.Surjective pH.onPoints :=
    Function.LeftInverse.surjective (product_snd_inr G H)
  have hIGnormal : I_G.toSubgroup.Normal := by
    dsimp only [I_G, fG]
    exact pG.imageClosedSubgroup_normal_of_normal_of_surjective
      hpGsurj R hR.normal
  have hIHnormal : I_H.toSubgroup.Normal := by
    dsimp only [I_H, fH]
    exact pH.imageClosedSubgroup_normal_of_normal_of_surjective
      hpHsurj R hR.normal
  have hIGconnected : _root_.IsConnected
      (I_G : Set (Variety.Point G)) :=
    fG.imageClosedSubgroup_isConnected hRvar
  have hIHconnected : _root_.IsConnected
      (I_H : Set (Variety.Point H)) :=
    fH.imageClosedSubgroup_isConnected hRvar
  have hIGsolvable : Group.IsSolvable
      (Variety.Point I_G.carrierVariety) :=
    fG.imageClosedSubgroup_isSolvable hR.solvable
  have hIHsolvable : Group.IsSolvable
      (Variety.Point I_H.carrierVariety) :=
    fH.imageClosedSubgroup_isSolvable hR.solvable
  obtain ⟨R_G, hRG⟩ := exists_radical G
  obtain ⟨R_H, hRH⟩ := exists_radical H
  have hIGle : I_G ≤ R_G :=
    hRG.maximal I_G hIGnormal hIGconnected hIGsolvable
  have hIHle : I_H ≤ R_H :=
    hRH.maximal I_H hIHnormal hIHconnected hIHsolvable
  have hIGbot : I_G.toSubgroup = ⊥ := by
    apply le_antisymm
    · rw [← hG.2 R_G hRG]
      exact hIGle
    · exact bot_le
  have hIHbot : I_H.toSubgroup = ⊥ := by
    apply le_antisymm
    · rw [← hH.2 R_H hRH]
      exact hIHle
    · exact bot_le
  apply le_antisymm
  · intro z hz
    apply Subgroup.mem_bot.mpr
    let zR : Variety.Point R.carrierVariety := R.pointEquiv.symm ⟨z, hz⟩
    have hzR : R.inclusion.onPoints zR = z := by
      change (R.pointEquiv zR).val = z
      simp [zR]
    have hpGz : pG.onPoints z = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hIGbot]
      change pG.onPoints z ∈ fG.image
      refine ⟨zR, ?_⟩
      change pG.onPoints (R.inclusion.onPoints zR) = pG.onPoints z
      rw [hzR]
    have hpHz : pH.onPoints z = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hIHbot]
      change pH.onPoints z ∈ fH.image
      refine ⟨zR, ?_⟩
      change pH.onPoints (R.inclusion.onPoints zR) = pH.onPoints z
      rw [hzR]
    apply (Variety.prodPointEquiv G H).injective
    exact Prod.ext hpGz hpHz
  · exact bot_le

end Theory.AlgebraicGroup
