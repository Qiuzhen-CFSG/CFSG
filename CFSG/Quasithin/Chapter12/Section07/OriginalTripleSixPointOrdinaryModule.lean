module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointCommutator
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointComponent
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointQuotient
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointNonsplit

/-!
# The whole original module for the point residual

The original perfect point residual has the same action image on U as its
point centralizer. Hence its action on U/Vt is the literal natural SL₂(4)
action, and the whole order-64 module remains nonsplit for this residual.

Source: Aschbacher--Smith 12.7.4(2--3) and the ordinary branch of 12.7.5,
printed pp.839--840. The point, module, and all conjugation maps are unchanged.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Restriction to the actual perfect residual retains the full original
vector-stabilizer action image. -/
theorem tripleSixPointResidual_projection_surjective (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    let C := K ⊓ centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 C).map C.subtype
    Function.Surjective ((tripleSixPointCentralizerProjection D a t).comp
      (inclusion (map_subtype_le (pResidual 2 C) : Lt ≤ C))) := by
  let C := K ⊓ centralizer ({(t : G)} : Set G)
  let q := tripleSixPointCentralizerProjection D a t
  let w := (tripleSixPointCoordinates D a t).toAdd
  have hw : w ≠ 0 := by
    intro hz
    have he : tripleSixPointCoordinates D a t = 1 := hz
    exact ht ((tripleSixPointCoordinates D a).injective
      (he.trans (tripleSixPointCoordinates D a).map_one.symm))
  let e := Hexacode.fullWeightVectorStabilizerEquiv w hw
    (tripleSixPoint_full_weight D a t ht heven)
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (Hexacode.fullWeightVectorStabilizer w) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have himage : (pResidual 2 C).map q = ⊤ := by
    rw [tripleSixPointCentralizerResidual_eq_solvableResidual D a t ht heven,
      map_solvableResidual_eq q (tripleSixPointCentralizerProjection_surjective D a t),
      solvableResidual_eq_top]
  change Function.Surjective (q.comp (inclusion (map_subtype_le (pResidual 2 C))))
  intro g
  obtain ⟨r,hr,hg⟩ := show g ∈ (pResidual 2 C).map q by rw [himage]; trivial
  exact ⟨⟨r,mem_map_of_mem C.subtype hr⟩,hg⟩

/-- The original natural quotient coordinates restrict to the same actual
point residual and its own two-core quotient. -/
theorem tripleSixPointResidual_quotient_natural (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    let C := K ⊓ centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 C).map C.subtype
    ∃ (e : (Lt ⧸ pCore 2 Lt) ≃* SL2FourNatural.SL),
      Nonempty (BinaryConjugationSection Lt U (tripleSixPoint D a t)
        (SL2FourNatural.naturalRepresentation.comp
          (e.toMonoidHom.comp (QuotientGroup.mk' _)))) := by
  let C := K ⊓ centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 C).map C.subtype
  have hLC : Lt ≤ C := map_subtype_le _
  obtain ⟨eC,b,c,hc⟩ := tripleSixPoint_quotient_natural D a t ht heven
  let eA := tripleSixPointResidualQuotientEquiv D a t ht heven
  let eCA := tripleSixPointCentralizerEquiv D a t ht heven
  let e := eA.trans (eCA.symm.trans eC)
  have he (l : Lt) : e (QuotientGroup.mk' _ l) =
      eC (QuotientGroup.mk' _ (inclusion hLC l)) := by
    obtain ⟨r,hr,hl⟩ := l.property
    have hl' : (⟨r,mem_map_of_mem C.subtype hr⟩ : Lt) = l := Subtype.ext hl
    rw [←hl']
    change eC (eCA.symm (eA (QuotientGroup.mk' _
      ⟨r,mem_map_of_mem C.subtype hr⟩))) = _
    rw [tripleSixPointResidualQuotientEquiv_mk D a t ht heven ⟨r,hr⟩]
    rw [eCA.symm_apply_apply]
    rfl
  refine ⟨e,⟨{
    section_le := (tripleSixPointCentralizerResidual_commutator D a t ht heven).2
    kernel_le := c.kernel_le
    normalized := hLC.trans c.normalized
    coordinates := c.coordinates
    onto := c.onto
    kernel_eq := c.kernel_eq
    equivariant := ?_ }⟩⟩
  intro l u
  change (c.coordinates _).toAdd =
    SL2FourNatural.naturalRepresentation (e (QuotientGroup.mk' _ l)) (c.coordinates u).toAdd
  rw [he]
  exact c.equivariant (inclusion hLC l) u

/-- An invariant complement for Lt would also be invariant for C_K(t),
because both have the same action image on the unchanged whole module. -/
theorem tripleSixPointResidual_nonsplit (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (A : Subgroup G) (hAU : A ≤ U)
    (hA : ((pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
      (K ⊓ centralizer ({(t : G)} : Set G)).subtype) ≤ normalizer A)
    (hdis : Disjoint (tripleSixPoint D a t) A) :
    tripleSixPoint D a t ⊔ A ≠ U := by
  let C := K ⊓ centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 C).map C.subtype
  let S := Hexacode.fullWeightVectorStabilizer (tripleSixPointCoordinates D a t).toAdd
  let q : C →* S := tripleSixPointCentralizerProjection D a t
  have hLC : Lt ≤ C := map_subtype_le _
  apply tripleSixPoint_nonsplit D a t ht heven A hAU ?_ hdis
  intro g hg
  let c : C := ⟨g,hg⟩
  obtain ⟨l,hl⟩ := tripleSixPointResidual_projection_surjective D a t ht heven (q c)
  let r : C := inclusion hLC l
  have hr : q r = q c := hl
  have hker : q (r⁻¹ * c) = 1 := calc
    q (r⁻¹ * c) = q r⁻¹ * q c := q.map_mul _ _
    _ = q r⁻¹ * q r := congrArg (q r⁻¹ * ·) hr.symm
    _ = q (r⁻¹ * r) := (q.map_mul _ _).symm
    _ = 1 := by rw [inv_mul_cancel,map_one]
  have hcentral : ((r⁻¹ * c : C) : G) ∈ centralizer (A : Set G) := by
    apply mem_centralizer_iff.mpr
    intro u hu
    let uU : U := ⟨u,hAU hu⟩
    have hh := tripleSixPointCentralizerProjection_conjugate D a t (r⁻¹ * c) uU
    rw [hker] at hh
    simp only [Subgroup.coe_one, map_one, Module.End.one_apply] at hh
    change ((tripleSixPointCoordinates D a).symm ((tripleSixPointCoordinates D a) uU) : G) = _ at hh
    rw [(tripleSixPointCoordinates D a).symm_apply_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  have hn := (normalizer (A : Set G)).mul_mem (hA l.property)
    (Subgroup.centralizer_le_normalizer (A : Set G) hcentral)
  change (l : G) * ((l : G)⁻¹ * g) ∈ normalizer (A : Set G) at hn
  simpa only [mul_inv_cancel_left] using hn

end CFSG.Quasithin.Chapter12.Section07
