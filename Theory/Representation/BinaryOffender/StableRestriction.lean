module
public import Theory.Representation.BinaryOffender.FixedCodimTransport
public import Theory.ElementaryAbelian.Quotient

/-!
# Restricting stable families to an actor subgroup

Faithful actor inclusion and equality of fixed codimensions preserve best
offenders, conjugacy and equal-weight descent. The only nonemptiness
requirement is an actual member supported in the subgroup.
The paired S₅ source application uses this on each coordinate axis.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G H V W : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) H W)

private theorem elementary_map_iff (f : G →* H) (hf : Function.Injective f)
    (A : Subgroup G) : IsElementaryTwo (A.map f) ↔ IsElementaryTwo A := by
  constructor
  · intro ha
    let : IsElementaryAbelian 2 (A.map f) := ha.2
    let e := A.equivMapOfInjective f hf
    refine ⟨fun h => ha.1 (by rw [h,Subgroup.map_bot]),
      IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective⟩
  · intro ha
    let : IsElementaryAbelian 2 A := ha.2
    exact ⟨fun h => ha.1 ((Subgroup.map_eq_bot_iff_of_injective A hf).mp h),
      IsElementaryAbelian.map f⟩

/-- Stable families restrict along a faithful actor inclusion whenever the
fixed codimensions are unchanged and the restricted family is nonempty. -/
theorem IsStable.restrict_of_fixedCodim
    (f : G →* H) (hf : Function.Injective f)
    (hc : ∀ A, fixedCodim ρ A = fixedCodim σ (A.map f))
    {P : Set (Subgroup H)} (hP : IsStable σ P)
    (hne : ∃ A : Subgroup G, A.map f ∈ P) :
    IsStable ρ {A : Subgroup G | A.map f ∈ P} := by
  refine ⟨hne,?_,?_,?_⟩
  · intro A hA
    have hh := hP.2.1 _ hA
    refine ⟨(elementary_map_iff f hf A).mp hh.1,fun B hB => ?_⟩
    exact (weight_le_map_iff_of_fixedCodim ρ σ f hf hc B A).mp
      (hh.2 _ (map_mono hB))
  · intro A hA g
    have hh := hP.2.2.1 _ hA (f g)
    have he : (A.map (MulAut.conj g).toMonoidHom).map f =
        (A.map f).map (MulAut.conj (f g)).toMonoidHom := by
      rw [map_map,map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
    change (A.map (MulAut.conj g).toMonoidHom).map f ∈ P
    rwa [he]
  · intro A hA B hB hBA
    apply hP.2.2.2 _ hA _ ((elementary_map_iff f hf B).mpr hB)
    refine ⟨map_mono hBA.1,le_antisymm ?_ ?_⟩
    · exact (weight_le_map_iff_of_fixedCodim ρ σ f hf hc B A).mpr hBA.2.le
    · exact (weight_le_map_iff_of_fixedCodim ρ σ f hf hc A B).mpr hBA.2.ge
end Representation.BinaryOffender

