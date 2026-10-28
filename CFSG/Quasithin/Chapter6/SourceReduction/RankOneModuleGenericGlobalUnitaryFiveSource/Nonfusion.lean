module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourSingularity
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.Thompson

/-!
# Ambient separation of the two unitary-five Hermitian involution types

The marked action on Z(O₂(L)) identifies determinant zero with centralization
by a Sylow two-subgroup of L. Its full normalizer preserves that condition.
The proved full-Sylow Thompson identity therefore makes singularity invariant
under ambient conjugacy. The diagonal and off-diagonal Hermitian vectors give
two actual nonconjugate involutions in the original core center.

The intrinsic singularity transport follows the same general argument as
the U₄ source companion, applied here to the U₅ center and its actual quotient
marking. This is separation, not coverage of all ambient involutions.
Source: Aschbacher–Smith F.4.35, printed p.292 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryFiveSource
open Representation.OrthogonalFourMinus.FiniteModel
open Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourSingularity
variable {G : Type*} [Group G] [Finite G] (L Q : Subgroup G)
variable (m : ℕ) [NeZero m]

private theorem marked_singular_iff
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field m))
    (f : Q ≃* Multiplicative (Space m))
    (hf : ∀ (l : L) (v : Q),
      (f.symm (Multiplicative.ofAdd (action m (e (QuotientGroup.mk' (pCore 2 L) l))
        (f v).toAdd)) : G) = (l : G)*(v : G)*(l : G)⁻¹)
    (x : Q) : form m (f x).toAdd = 0 ↔
      ∃ P : Sylow 2 L, ∀ l ∈ (P : Subgroup L), (l : G)*(x : G)*(l : G)⁻¹ = x := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfix (l : L) : action m (q l) (f x).toAdd = (f x).toAdd ↔
      (l : G)*(x : G)*(l : G)⁻¹ = x := by
    constructor
    · intro he
      have hh := hf l x
      change (f.symm (Multiplicative.ofAdd (action m (q l) (f x).toAdd)) : G) = _ at hh
      rw [he] at hh
      have hx : f.symm (Multiplicative.ofAdd (f x).toAdd) = x := f.symm_apply_apply x
      exact hh.symm.trans (congrArg Subtype.val hx)
    · intro he
      apply Multiplicative.ofAdd.injective
      apply f.symm.injective
      have hx : f.symm (Multiplicative.ofAdd (f x).toAdd) = x := f.symm_apply_apply x
      exact (Subtype.ext ((hf l x).trans he)).trans hx.symm
  rw [singular_iff_fixed_sylow]
  constructor
  · rintro ⟨P,hP⟩
    obtain ⟨R,hR⟩ := Sylow.mapSurjective_surjective hq 2 P
    refine ⟨R,fun l hl => (hfix l).mp (hP (q l) ?_)⟩
    rw [←hR]
    exact ⟨l,hl,rfl⟩
  · rintro ⟨P,hP⟩
    refine ⟨P.mapSurjective hq,?_⟩
    rintro _ ⟨l,hl,rfl⟩
    exact (hfix l).mpr (hP l hl)

private theorem sylow_centralizes_conjugate
    (g : G) (hg : g ∈ normalizer (L : Set G)) (x : G)
    (h : ∃ P : Sylow 2 L, ∀ l ∈ (P : Subgroup L), (l : G)*x*(l : G)⁻¹ = x) :
    ∃ P : Sylow 2 L, ∀ l ∈ (P : Subgroup L),
      (l : G)*(g*x*g⁻¹)*(l : G)⁻¹ = g*x*g⁻¹ := by
  obtain ⟨P,hP⟩ := h
  let c := L.normalizerMonoidHom ⟨g,hg⟩
  refine ⟨P.mapSurjective (f := c.toMonoidHom) c.surjective,?_⟩
  rintro _ ⟨l,hl,rfl⟩
  have hc : ((c l : L) : G) = g*(l : G)*g⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
  change ((c l : L) : G)*(g*x*g⁻¹)*((c l : L) : G)⁻¹ = _
  rw [hc]
  calc
    (g*(l : G)*g⁻¹)*(g*x*g⁻¹)*(g*(l : G)*g⁻¹)⁻¹ =
        g*((l : G)*x*(l : G)⁻¹)*g⁻¹ := by group
    _ = g*x*g⁻¹ := by rw [hP l hl]

private theorem marked_normalizer_singular
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field m))
    (f : Q ≃* Multiplicative (Space m))
    (hf : ∀ (l : L) (v : Q),
      (f.symm (Multiplicative.ofAdd (action m (e (QuotientGroup.mk' (pCore 2 L) l))
        (f v).toAdd)) : G) = (l : G)*(v : G)*(l : G)⁻¹)
    (x y : Q) (g : G) (hg : g ∈ normalizer (L : Set G))
    (hxy : g*(x : G)*g⁻¹ = y) :
    form m (f x).toAdd = 0 ↔ form m (f y).toAdd = 0 := by
  rw [marked_singular_iff L Q m e f hf,marked_singular_iff L Q m e f hf]
  constructor
  · intro h
    have hh := sylow_centralizes_conjugate L g hg x h
    rwa [hxy] at hh
  · intro h
    have hh := sylow_centralizes_conjugate L g⁻¹ ((normalizer (L : Set G)).inv_mem hg) y h
    have he : g⁻¹*(y : G)*(g⁻¹)⁻¹ = x := by rw [←hxy]; group
    rwa [he] at hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryFiveSource

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.RankOne Representation.OrthogonalFourMinus.CartanFixed
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- Ambient conjugacy on the original plane-core center preserves the
Hermitian singular locus, with its canonical quotient action retained. -/
theorem Preparation.unitaryFive_hermitian_fusion
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    let Z := (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype
    ∃ (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field 2))
      (f : Z ≃* Multiplicative (Space 2)),
      (∀ (l : L) (v : Z),
        (f.symm (Multiplicative.ofAdd (action 2 (e (QuotientGroup.mk' (pCore 2 L) l))
          (f v).toAdd)) : G) = (l : G)*(v : G)*(l : G)⁻¹) ∧
      ∀ x y : Z, IsConj (x : G) (y : G) →
        (form 2 (f x).toAdd = 0 ↔ form 2 (f y).toAdd = 0) := by
  obtain ⟨e,f,hf⟩ := d.unitaryFive_plane_center_hermitian_model h hH hp U hc
  refine ⟨e,f,hf,?_⟩
  intro x y hxy
  obtain ⟨g,hg,he⟩ := d.unitaryFive_plane_center_fusion h hH hp U hc x.property y.property hxy
  exact UnitaryFiveSource.marked_normalizer_singular L _ 2 e f hf x y g hg he

/-- Two explicit Hermitian types yield distinct ambient involution classes
in the original plane-core center. -/
theorem Preparation.unitaryFive_two_nonconjugate_involutions
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    let Z := (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype
    ∃ x ∈ Z, ∃ y ∈ Z, orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y := by
  let Z := (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype
  obtain ⟨_,f,_,hf⟩ := d.unitaryFive_hermitian_fusion h hH hp U hc
  let x := f.symm (Multiplicative.ofAdd (rootVector 2 1))
  let y := f.symm (Multiplicative.ofAdd (movedVector 2))
  have hxcoord : (f x).toAdd = rootVector 2 1 :=
    congrArg Multiplicative.toAdd (f.apply_symm_apply _)
  have hycoord : (f y).toAdd = movedVector 2 :=
    congrArg Multiplicative.toAdd (f.apply_symm_apply _)
  have hxs : form 2 (f x).toAdd = 0 := by
    rw [hxcoord,rootVector,form_coordinates]
    simp
  have hys : form 2 (f y).toAdd = 1 := by rw [hycoord,movedVector_form]
  have hx1 : (x : G) ≠ 1 := by
    intro he
    have hx : x = 1 := Subtype.ext he
    have hh := congrArg (fun v : Space 2 => v.val 0 0) hxcoord
    rw [hx,map_one] at hh
    exact zero_ne_one hh
  have hy1 : (y : G) ≠ 1 := by
    intro he
    have hy : y = 1 := Subtype.ext he
    rw [hy,map_one] at hys
    exact zero_ne_one ((map_zero (form 2)).symm.trans hys)
  let : IsElementaryAbelian 2 Z :=
    ((d.unitaryFive_plane_core_structure h hH hp U hc).2.1).map (L.pCoreIn 2).subtype
  refine ⟨x,x.property,y,y.property,
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G) x.property) hx1,
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) (y : G) y.property) hy1,?_⟩
  intro hxy
  have hh := (hf x y hxy).mp hxs
  rw [hys] at hh
  exact one_ne_zero hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
