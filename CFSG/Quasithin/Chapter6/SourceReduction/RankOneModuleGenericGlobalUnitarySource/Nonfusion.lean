module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourSingularity
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.AmbientThompson

/-!
# Ambient nonfusion of the two Hermitian unitary-four involution types

The native determinant vanishes exactly on vectors fixed by some Sylow
subgroup of the acting SL₂. Through the literal quotient map L → L/O₂(L),
this is equivalent to centralization by some Sylow two-subgroup of L.
Surjective Sylow transport retains the full quotient kernel. Conjugation
by N_G(L) preserves the latter condition; the proved ambient Thompson
fusion theorem therefore shows that conjugacy in the original G preserves
Hermitian singularity on O₂(L).

The singular diagonal vector and the nonsingular off-diagonal vector give
two nonconjugate ambient involutions. The coordinates and their original
quotient-action marking are constructed from the prepared comparison;
there is no realization, local-fusion or ambient-order premise. Both
ordinary and degree-two rows and both orientations are retained.

Source: Aschbacher–Smith F.4.35, printed p.292 of `refs/quasithin.pdf`.
This proves separation on the original core; outer-involution transfer,
full-normalizer realization and F.4.42–43 still require their source arguments.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitarySource
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

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitarySource

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.RankOne Representation.OrthogonalFourMinus.CartanFixed
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The original core has Hermitian coordinates in which ambient conjugacy
preserves singularity. The quotient action and all original kernels are retained. -/
theorem Preparation.unitary_hermitian_fusion
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m) [NeZero m]
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    ∃ (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field m))
      (f : L.pCoreIn 2 ≃* Multiplicative (Space m)),
      (∀ (l : L) (v : L.pCoreIn 2),
        (f.symm (Multiplicative.ofAdd (action m (e (QuotientGroup.mk' (pCore 2 L) l))
          (f v).toAdd)) : G) = (l : G)*(v : G)*(l : G)⁻¹) ∧
      ∀ x y : L.pCoreIn 2, IsConj (x : G) (y : G) →
        (form m (f x).toAdd = 0 ↔ form m (f y).toAdd = 0) := by
  obtain ⟨e,f,hf⟩ := d.unitary_core_hermitian_model h hH hp m hm hc
  refine ⟨e,f,hf,?_⟩
  intro x y hxy
  obtain ⟨g,hg,he⟩ := d.unitary_core_fusion h hH hp m hm hc x.property y.property hxy
  exact UnitarySource.marked_normalizer_singular L (L.pCoreIn 2) m e f hf x y g hg he

/-- The two Hermitian types give distinct ambient involution classes in the
original left core, for ordinary and degree-two comparisons in either orientation. -/
theorem Preparation.unitary_core_two_nonconjugate_involutions
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    ∃ x ∈ L.pCoreIn 2, ∃ y ∈ L.pCoreIn 2,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨_,f,_,hf⟩ := d.unitary_hermitian_fusion h hH hp m hm hc
  let x := f.symm (Multiplicative.ofAdd (rootVector m 1))
  let y := f.symm (Multiplicative.ofAdd (movedVector m))
  have hxcoord : (f x).toAdd = rootVector m 1 :=
    congrArg Multiplicative.toAdd (f.apply_symm_apply _)
  have hycoord : (f y).toAdd = movedVector m :=
    congrArg Multiplicative.toAdd (f.apply_symm_apply _)
  have hxs : form m (f x).toAdd = 0 := by
    rw [hxcoord,rootVector,form_coordinates]
    simp
  have hys : form m (f y).toAdd = 1 := by rw [hycoord,movedVector_form]
  have hx1 : (x : G) ≠ 1 := by
    intro he
    have hx : x = 1 := Subtype.ext he
    have hh := congrArg (fun v : Space m => v.val 0 0) hxcoord
    rw [hx,map_one] at hh
    exact zero_ne_one hh
  have hy1 : (y : G) ≠ 1 := by
    intro he
    have hy : y = 1 := Subtype.ext he
    rw [hy,map_one] at hys
    exact zero_ne_one ((map_zero (form m)).symm.trans hys)
  let : IsElementaryAbelian 2 (pCore 2 L) :=
    (d.unitary_core_structure h hH.1.1.2 hp m hm hc).2.2.1
  let : IsElementaryAbelian 2 (L.pCoreIn 2) := IsElementaryAbelian.map L.subtype
  refine ⟨x,x.property,y,y.property,
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G) x.property) hx1,
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) (y : G) y.property) hy1,?_⟩
  intro hxy
  have hh := (hf x y hxy).mp hxs
  rw [hys] at hh
  exact one_ne_zero hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
