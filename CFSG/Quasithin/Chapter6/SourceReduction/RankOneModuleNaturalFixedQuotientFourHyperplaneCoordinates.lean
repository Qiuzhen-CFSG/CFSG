module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourHyperplaneOrbits
public import CFSG.Quasithin.Chapter6.Section01.SourceBasic
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.Representation.BinaryConjugationCoordinates

/-!
# Hermitian coordinates aligned with the actual inner Sylow subgroup

Sylow conjugacy changes both the quotient marking and vector coordinates.
The resulting actual conjugation model sends T∩L to the upper root subgroup;
the original ambient Sylow T is retained. This is the coordinate preparation
for selecting an L-conjugate of an escaping hyperplane in 6.1.4, printed p.665.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter6.Source.FourHyperplaneGeometry
open OrthogonalFourMinus.FiniteModel OrthogonalFourMinus.HermitianEquiv
open Matrix.SpecialLinearGroup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L B : Subgroup G} {s : ℕ} [NeZero s]

local instance sylowCoordinatesFixedAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance sylowCoordinatesBinaryModule : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- The actual quotient epimorphism and module coordinates can simultaneously
place the prescribed inner Sylow subgroup in upper-root position. -/
theorem exists_hermitian_sylow_coordinates
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hm : IsConjugationModel L B (SL2.BinarySmall.hermitian s)) :
    ∃ (q : L →* Matrix.SpecialLinearGroup (Fin 2) (Field s))
      (f : B ≃* Multiplicative (Space s)),
      Function.Surjective q ∧
      (∀ (l : L) (v : B),
        (f (B.normalizerMonoidHom ⟨l,hm.normalizes l.property⟩ v)).toAdd =
          SL2.BinarySmall.hermitian s (q l) (f v).toAdd) ∧
      ((T : Subgroup G).subgroupOf L).map q = upperUnipotent (Field s) := by
  have hN := hm.normalizes
  obtain ⟨e,f,hf⟩ := hm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  let S := P.mapSurjective hq
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq
    (Matrix.SpecialLinearGroup (Fin 2) (Field s)) S (upperUnipotentSylow (Field s) 2)
  have hS : (S : Subgroup _).map (MulAut.conj a).toMonoidHom =
      upperUnipotent (Field s) := by
    change ((a • S : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) (Field s))) :
      Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s))) = _
    rw [ha]
    rfl
  let ρ := SL2.BinarySmall.hermitian s
  let A := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom a)
  let f' := f.trans A.toAddEquiv.toMultiplicative
  let q' := (MulAut.conj a).toMonoidHom.comp q
  have hact (l : L) (v : B) :
      (f (B.normalizerMonoidHom ⟨l,hN l.property⟩ v)).toAdd =
        ρ (q l) (f v).toAdd := by
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.ext
    change (f.symm (f (B.normalizerMonoidHom ⟨l,hN l.property⟩ v)) : G) = _
    rw [f.symm_apply_apply]
    exact (hf l v).symm
  refine ⟨q',f',(MulAut.conj a).surjective.comp hq,?_,?_⟩
  · intro l v
    change ρ a (f (B.normalizerMonoidHom ⟨l,hN l.property⟩ v)).toAdd =
      ρ (a * q l * a⁻¹) (ρ a (f v).toAdd)
    rw [hact,map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,
      ρ.inv_self_apply]
  · change ((T : Subgroup G).subgroupOf L).map
      ((MulAut.conj a).toMonoidHom.comp q) = _
    rw [←Subgroup.map_map,←hP]
    exact hS

end CFSG.Quasithin.Chapter6.Source.FourHyperplaneGeometry
