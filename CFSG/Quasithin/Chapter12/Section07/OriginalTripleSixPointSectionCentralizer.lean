module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointResidual
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.SectionCentralizer
public import Theory.Representation.HexacodeAction.FullWeightVectorCommutant
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# The original triple-six section centralizer fixes the chosen module

An element of the section centralizer normalizes the original U and commutes
with the point residual modulo its two-core. That core centralizes U by the
actual vector-stabilizer projection. The residual projects onto the whole
vector stabilizer, so the element induces a commuting binary endomorphism
in the original chart. It fixes the specified nonzero vector, forcing that
endomorphism to be the identity.

Source: Aschbacher--Smith, 12.7.4--12.7.5, printed pp.839--840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource ChapterA.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The section centralizer of the actual point residual inside the actual
point normalizer centralizes the unchanged whole chosen module U. -/
theorem tripleSixPoint_twoSectionCentralizer_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    let C := K ⊓ centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 C).map C.subtype
    let Mt := normalizer (K : Set G) ⊓ centralizer ({(t : G)} : Set G)
    twoSectionCentralizer Lt Mt ≤ centralizer (U : Set G) := by
  dsimp only
  let C := K ⊓ centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 C).map C.subtype
  let Mt := normalizer (K : Set G) ⊓ centralizer ({(t : G)} : Set G)
  let f := tripleSixPointCoordinates D a
  let v := (f t).toAdd
  let q := tripleSixPointCentralizerProjection D a t
  have hCU : C ≤ normalizer (U : Set G) := inf_le_left.trans D.normalizes
  let β : C →* MulAut U := U.normalizerMonoidHom.comp (inclusion hCU)
  have hchart (c : C) (u : U) :
      Hexacode.evenAction (q c).val (f u).toAdd = (f (β c u)).toAdd := by
    have he := tripleSixPointCentralizerProjection_conjugate D a t c u
    have he' : f.symm (Multiplicative.ofAdd
        (Hexacode.evenAction (q c).val (f u).toAdd)) = β c u := Subtype.ext he
    have hh := congrArg f he'
    rw [f.apply_symm_apply] at hh
    exact congrArg Multiplicative.toAdd hh
  have hcoreC : C.pCoreIn 2 ≤ centralizer (U : Set G) := by
    rintro z ⟨c, hc, rfl⟩
    have hq : q c = 1 := by
      change c ∈ q.ker
      rw [tripleSixPointCentralizerProjection_ker_eq_core D a t ht heven]
      exact hc
    apply mem_centralizer_iff.mpr
    intro u hu
    have he := tripleSixPointCentralizerProjection_conjugate D a t c ⟨u, hu⟩
    change ((f.symm (Multiplicative.ofAdd
      (Hexacode.evenAction (q c).val (f ⟨u, hu⟩).toAdd))) : G) = _ at he
    rw [hq] at he
    simp only [OneMemClass.coe_one, map_one, Module.End.one_apply] at he
    change ((f.symm (f ⟨u, hu⟩)) : G) = (c : G) * u * (c : G)⁻¹ at he
    rw [f.symm_apply_apply] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  have hcoreLt : Lt.pCoreIn 2 ≤ centralizer (U : Set G) :=
    (pCoreIn_mono_of_normalizes (map_subtype_le _) (le_normalizer_embedded_pResidual 2 C)).trans
      hcoreC
  have hv : v ≠ 0 := by
    intro hz
    have hh : f t = 1 := hz
    exact ht (f.injective (hh.trans f.map_one.symm))
  have hP := tripleSixPoint_full_weight D a t ht heven
  let e := Hexacode.fullWeightVectorStabilizerEquiv v hv hP
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (Hexacode.fullWeightVectorStabilizer v) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have himage : (pResidual 2 C).map q = ⊤ := by
    rw [tripleSixPointCentralizerResidual_eq_solvableResidual D a t ht heven,
      map_solvableResidual_eq q (tripleSixPointCentralizerProjection_surjective D a t),
      solvableResidual_eq_top]
  have hMtU : Mt ≤ normalizer (U : Set G) :=
    h.source_point_normalizes_chosen_at structural D t.property
      (fun he => ht (Subtype.ext he)) le_rfl
  intro x hx
  change x ∈ twoSectionCentralizer Lt Mt at hx
  have hxU := hMtU hx.1
  let α := U.normalizerMonoidHom ⟨x, hxU⟩
  let η : Module.End (ZMod 2) Atlas.Codes.hexacode :=
    (AddMonoidHom.toMultiplicative.symm (MulAut.congr f α).toMonoidHom).toZModLinearMap 2
  have hη (u : U) : η (f u).toAdd = (f (α u)).toAdd := by
    change (f (α (f.symm (f u)))).toAdd = _
    rw [f.symm_apply_apply]
  have hco (c : C) (hc : c ∈ pResidual 2 C) : Commute α (β c) := by
    change Commute (U.normalizerMonoidHom ⟨x, hxU⟩)
      (U.normalizerMonoidHom (inclusion hCU c))
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    change ⁅(⟨x, hxU⟩ : normalizer (U : Set G)), inclusion hCU c⁆ ∈
      U.normalizerMonoidHom.ker
    rw [normalizerMonoidHom_ker]
    exact hcoreLt (hx.2.2 c (mem_map_of_mem C.subtype hc))
  have hηcomm (g : Hexacode.fullWeightVectorStabilizer v) (w : Atlas.Codes.hexacode) :
      η (Hexacode.evenAction g.val w) = Hexacode.evenAction g.val (η w) := by
    obtain ⟨c, hc, hcg⟩ := show g ∈ (pResidual 2 C).map q by rw [himage]; trivial
    obtain ⟨u, hu⟩ := f.surjective (Multiplicative.ofAdd w)
    have hw : (f u).toAdd = w := congrArg Multiplicative.toAdd hu
    rw [← hcg, ← hw, hchart, hη, hη, hchart]
    exact congrArg (fun z : U => (f z).toAdd) (DFunLike.congr_fun (hco c hc).eq u)
  have hαt : α t = t := by
    apply Subtype.ext
    change x * (t : G) * x⁻¹ = t
    exact mul_inv_eq_of_eq_mul (mem_centralizer_singleton_iff.mp hx.1.2)
  have hηv : η v = v := by
    change η (f t).toAdd = (f t).toAdd
    rw [hη, hαt]
  have hid := Hexacode.fullWeightVectorStabilizer_commutant_eq_id v hv hP η hηcomm hηv
  apply mem_centralizer_iff.mpr
  intro u hu
  have hz := congrArg (fun m : Module.End (ZMod 2) Atlas.Codes.hexacode =>
    m (f ⟨u, hu⟩).toAdd) hid
  change η (f ⟨u, hu⟩).toAdd = (f ⟨u, hu⟩).toAdd at hz
  rw [hη] at hz
  have he := f.injective (Multiplicative.toAdd.injective hz)
  have he' : x * u * x⁻¹ = u := congrArg Subtype.val he
  exact (mul_inv_eq_iff_eq_mul.mp he').symm

end CFSG.Quasithin.Chapter12.Section07
