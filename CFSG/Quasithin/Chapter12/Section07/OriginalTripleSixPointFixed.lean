module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointQuotient
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointResidual
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointCommutator

/-!
# The exact fixed four-group of the original point residual

The residual surjects onto the actual vector stabilizer. The natural
quotient has no fixed vector, so a vector of U centralized by Lt lies in
the original field point Vt. The converse is the field-line calculation.
As U lies in Lt, this also identifies U intersect Z(Lt) with the same Vt.

Source: Aschbacher--Smith, 12.7.4(2--3), printed pp.839--840, and the
original central-point input to 12.7.5.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The fixed subgroup of the original whole U is precisely its original
scalar four-group, for the actual two-residual Lt. -/
theorem tripleSixPoint_residual_fixed (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    let C := K ⊓ centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 C).map C.subtype
    U ⊓ centralizer (Lt : Set G) = tripleSixPoint D a t := by
  let C := K ⊓ centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 C).map C.subtype
  let f := tripleSixPointCoordinates D a
  let v := (f t).toAdd
  let q := tripleSixPointCentralizerProjection D a t
  have hv : v ≠ 0 := by
    intro hz
    have hh : f t = 1 := hz
    exact ht (f.injective (hh.trans f.map_one.symm))
  have hP := tripleSixPoint_full_weight D a t ht heven
  let eA := Hexacode.fullWeightVectorStabilizerEquiv v hv hP
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (Hexacode.fullWeightVectorStabilizer v) :=
    Group.IsPerfect.ofSurjective (f := eA.symm.toMonoidHom) eA.symm.surjective
  have himage : (pResidual 2 C).map q = ⊤ := by
    rw [tripleSixPointCentralizerResidual_eq_solvableResidual D a t ht heven,
      map_solvableResidual_eq q (tripleSixPointCentralizerProjection_surjective D a t),
      solvableResidual_eq_top]
  obtain ⟨e,b,hb⟩ := Hexacode.fullWeightVectorQuotient_natural v hv hP
  apply le_antisymm
  · rintro u ⟨hu,huc⟩
    let uU : U := ⟨u,hu⟩
    have hfix (g : Hexacode.fullWeightVectorStabilizer v) :
        Hexacode.evenAction g.val (f uU).toAdd = (f uU).toAdd := by
      obtain ⟨c,hc,hcg⟩ := show g ∈ (pResidual 2 C).map q by rw [himage]; trivial
      have he := tripleSixPointCentralizerProjection_conjugate D a t c uU
      have hcomm := (mem_centralizer_iff.mp huc) c (mem_map_of_mem C.subtype hc)
      have hconj : (c : G) * u * (c : G)⁻¹ = u := mul_inv_eq_of_eq_mul hcomm
      rw [hconj] at he
      have he' : f.symm (Multiplicative.ofAdd
          (Hexacode.evenAction (q c).val (f uU).toAdd)) = uU := Subtype.ext he
      have hh := congrArg f he'
      rw [f.apply_symm_apply] at hh
      have hx := congrArg Multiplicative.toAdd hh
      change Hexacode.evenAction (q c).val (f uU).toAdd = (f uU).toAdd at hx
      rw [hcg] at hx
      exact hx
    have hzero : (Submodule.span Hexacode.F {v}).mkQ (f uU).toAdd = 0 := by
      apply b.injective
      rw [map_zero]
      apply SL2FourNatural.natural_fixed_eq_zero
      intro g
      obtain ⟨r,rfl⟩ := e.surjective g
      change specialLinearNatural 2 (e r)
        (b ((Submodule.span Hexacode.F {v}).mkQ (f uU).toAdd)) = _
      rw [←hb,Hexacode.fullWeightVectorQuotientAction_mk]
      exact congrArg (fun x => b ((Submodule.span Hexacode.F {v}).mkQ x)) (hfix r)
    exact ⟨uU,(Submodule.Quotient.mk_eq_zero _).mp hzero,rfl⟩
  · have hp := tripleSixPoint_properties D a t ht
    exact le_inf hp.2.1 (le_centralizer_iff.mp
      ((map_subtype_le (pResidual 2 C)).trans hp.2.2.2.2))

/-- The original scalar point is exactly the part of the residual center
inside the unchanged chosen module. -/
theorem tripleSixPoint_residual_center (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    let C := K ⊓ centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 C).map C.subtype
    U ⊓ centerIn Lt = tripleSixPoint D a t := by
  let C := K ⊓ centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 C).map C.subtype
  have hUL : U ≤ Lt := (tripleSixPointCentralizerResidual_commutator D a t ht heven).2
  change U ⊓ (Lt ⊓ centralizer (Lt : Set G)) = _
  rw [←inf_assoc,inf_eq_left.mpr hUL]
  exact tripleSixPoint_residual_fixed D a t ht heven

end CFSG.Quasithin.Chapter12.Section07
