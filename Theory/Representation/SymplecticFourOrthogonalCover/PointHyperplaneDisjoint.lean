module
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedLifting
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Geometry
public import Theory.SpecificGroups.SymplecticFour.MaximalElementary.RootFixed
public import Theory.Representation.BinaryOffender.SubspaceAction
/-!
# Point-radical displacement in a symplectic central cover

The point radical preserves the natural quadratic form on its displacement
hyperplane. Thus its displacement on the full inverse image of that hyperplane
has zero intersection with the entire fixed kernel of any central cover.
The argument descends from the universal orthogonal cover; it works over every
finite field of characteristic two and retains the complete fixed layer.

Source: MS93 (3.6), printed p.871, the paired seed-commutator intersection.
-/

public noncomputable section
open Matrix Subgroup Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
namespace Representation.SymplecticFourOrthogonalCover
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem point_radical_correction_zero_on_hyperplane
    (b : Sp F) (hb : b ∈ pointRadicalAmbient) (v : Natural (K := F))
    (hv : v ∈ (form F).orthogonal (point F)) : correction b v = 0 := by
  obtain ⟨b,hb,rfl⟩ := hb
  rw [pointRadical_eq_element b hb]
  have hv0 : v (.inr 0) = 0 := by
    have he := hv (e 0) (Submodule.subset_span (Set.mem_singleton (e (F := F) 0)))
    simpa [form_apply,Theory.SpecificGroups.SymplecticFour.e] using he
  apply (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp
  have he := correction_square (pointRadicalElement
    (b.val.val (.inl 1) (.inr 0)) (b.val.val (.inr 1) (.inr 0))
    (b.val.val (.inl 0) (.inr 0))).val v
  have hq : rowQuadratic ((pointRadicalElement
    (b.val.val (.inl 1) (.inr 0)) (b.val.val (.inr 1) (.inr 0))
    (b.val.val (.inl 0) (.inr 0))).val.val *ᵥ v) = rowQuadratic v := by
    simp [rowQuadratic,pointRadicalElement,pointRadicalMatrix,mulVec,dotProduct,
      Fintype.sum_sum_type,Fin.sum_univ_two,hv0]
  rw [hq] at he
  exact (add_eq_left.mp he.symm)

private theorem point_conjugate_action (g q : Sp F) (w : Space (K := F)) :
    fullAction ((MulAut.conj g) q) (fullAction g w) = fullAction g (fullAction q w) := by
  rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
  congr 2
  simp [MulAut.conj_apply,mul_assoc]

open Representation.BinaryOffender
variable [Algebra (ZMod 2) F]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) (L (K := F)) W}

/-- Displacement of the full preimage of a point radical's natural hyperplane
has trivial intersection with the entire fixed kernel of a central cover. -/
theorem point_hyperplane_commutator_disjoint
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (A : Subgroup (L (K := F))) (g : Sp F)
    (hA : (A.map (commutator (Sp F)).subtype).map (MulAut.conj g).toMonoidHom =
      pointRadicalAmbient) :
    Disjoint (subspaceCommutator σ
      ((displacementSpace (A.map (commutator (Sp F)).subtype)).restrictScalars (ZMod 2) |>.comap p.toLinearMap)
      A) (fixed σ) := by
  obtain ⟨f,hf,hpf⟩ := exists_cover_quotient p hp
  let D : Submodule (ZMod 2) (Space (K := F)) :=
    ((LinearMap.snd (ZMod 2) (Natural (K := F)) F).comp
      ((fullAction g).restrictScalars (ZMod 2))).ker
  have hmove : subspaceCommutator σ
      ((displacementSpace (A.map (commutator (Sp F)).subtype)).restrictScalars (ZMod 2) |>.comap p.toLinearMap)
      A ≤ D.map f.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b,hb,w,hw,rfl⟩
    obtain ⟨x,rfl⟩ := hf w
    refine ⟨binaryAction b x-x,?_,?_⟩
    · have hx : x.1 ∈ displacementSpace (A.map (commutator (Sp F)).subtype) := by
        change p (f x) ∈ displacementSpace (A.map (commutator (Sp F)).subtype) at hw
        rwa [hpf x] at hw
      have hxg : (fullAction g x).1 ∈ (form F).orthogonal (point F) := by
        rw [←PointRadicalAction.radical_displacement]
        change (fullAction g x).1 ∈ displacementSpace (pointRadicalAmbient (F := F))
        rw [←hA,PointRadicalAction.displacement_conjugate]
        exact ⟨x.1,hx,rfl⟩
      have hbg : (MulAut.conj g) b.val ∈ pointRadicalAmbient :=
        hA ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom (mem_map_of_mem _ hb)
      have hc := point_radical_correction_zero_on_hyperplane
        ((MulAut.conj g) b.val) hbg (fullAction g x).1 hxg
      change (fullAction g (fullAction b.val x-x)).2=0
      rw [map_sub,←point_conjugate_action]
      change (fullAction g x).2 + correction ((MulAut.conj g) b.val) (fullAction g x).1 -
        (fullAction g x).2 = 0
      simp only [hc,add_zero,sub_self]
    · change f (binaryAction b x-x) = σ b (f x)-f x
      rw [map_sub,f.isIntertwining]
  apply Disjoint.mono_left hmove
  rw [Submodule.disjoint_def]
  rintro w ⟨x,hx,rfl⟩ hw
  have hfst : x.1=0 := by
    have he : p (f x)=0 := (cover_fixed_kernel p hp).le hw
    exact (hpf x).symm.trans he
  have hsnd : x.2=0 := by
    have he : (fullAction g x).2=0 := hx
    simpa only [fullAction_apply,hfst,map_zero,add_zero] using he
  have hx0 : x=0 := Prod.ext hfst hsnd
  simp only [hx0,map_zero]

end Representation.SymplecticFourOrthogonalCover
