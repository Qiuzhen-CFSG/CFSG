module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointCentralizer
public import Theory.Representation.HexacodeAction.FullWeightVectorQuotient
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.BinaryConjugationSection

/-!
# The natural quotient of the original triple-six point centralizer

The literal quotient by the original scalar point is identified with the
hexacode quotient by its actual field line. Its conjugation action uses the
original point-centralizer projection. The resulting SL₂(4) marking and
binary coordinates come from that same quotient action.

Source: Aschbacher--Smith, 12.7.4(2), printed pp.839--840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Projection through the original chart gives the actual section U/Vt,
with the unchanged point-centralizer conjugation action. -/
theorem tripleSixPoint_quotient_section (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) :
    ∃ c : BinaryConjugationSection
      (K ⊓ centralizer ({(t : G)} : Set G)) U (tripleSixPoint D a t)
      ((Representation.restrictScalars (k := ZMod 2)
        (Hexacode.fullWeightVectorQuotientAction (tripleSixPointCoordinates D a t).toAdd)).comp
          (tripleSixPointCentralizerProjection D a t)),
      ∀ u : U, (c.coordinates u).toAdd =
        (Submodule.span Hexacode.F {(tripleSixPointCoordinates D a t).toAdd}).mkQ
          (tripleSixPointCoordinates D a u).toAdd := by
  let := D.elementary
  let f := tripleSixPointCoordinates D a
  let P := Submodule.span Hexacode.F {(f t).toAdd}
  let q : U →* Multiplicative (Atlas.Codes.hexacode ⧸ P) :=
    P.mkQ.toAddMonoidHom.toMultiplicative.comp f.toMonoidHom
  have hUC : U ≤ K ⊓ centralizer ({(t : G)} : Set G) := by
    refine le_inf (D.le_componentCore.trans (pCoreIn_le 2 K)) ?_
    intro u hu
    exact mem_centralizer_singleton_iff.mpr ((U.le_centralizer hu) t t.property).symm
  have hNU : K ⊓ centralizer ({(t : G)} : Set G) ≤ normalizer U :=
    inf_le_left.trans D.normalizes
  have hVU : tripleSixPoint D a t ≤ U := map_subtype_le _
  have hker : q.ker = (tripleSixPoint D a t).subgroupOf U := by
    ext u
    change Submodule.Quotient.mk (p := P) (f u).toAdd = 0 ↔
      (u : G) ∈ tripleSixPoint D a t
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hu
      exact ⟨u, hu, rfl⟩
    · rintro ⟨v, hv, he⟩
      have he' : v = u := Subtype.ext he
      exact he' ▸ hv
  let c : BinaryConjugationSection
      (K ⊓ centralizer ({(t : G)} : Set G)) U (tripleSixPoint D a t)
      ((Representation.restrictScalars (k := ZMod 2)
        (Hexacode.fullWeightVectorQuotientAction (f t).toAdd)).comp
          (tripleSixPointCentralizerProjection D a t)) := {
    section_le := hUC
    kernel_le := hVU
    normalized := hNU
    coordinates := q
    onto := by
      intro w
      obtain ⟨v, hv⟩ := P.mkQ_surjective w.toAdd
      refine ⟨f.symm (Multiplicative.ofAdd v), ?_⟩
      apply Multiplicative.toAdd.injective
      change P.mkQ (f (f.symm (Multiplicative.ofAdd v))).toAdd = w.toAdd
      rw [f.apply_symm_apply]
      exact hv
    kernel_eq := hker
    equivariant := by
      intro g u
      have he := tripleSixPointCentralizerProjection_conjugate D a t g u
      have hf : f ⟨(g : G) * (u : G) * (g : G)⁻¹,
          (mem_normalizer_iff.mp (hNU g.property) u).mp u.property⟩ =
          Multiplicative.ofAdd (Hexacode.evenAction
            (tripleSixPointCentralizerProjection D a t g).val (f u).toAdd) := by
        apply f.symm.injective
        rw [f.symm_apply_apply]
        exact Subtype.ext he.symm
      change P.mkQ (f _).toAdd =
        Hexacode.fullWeightVectorQuotientAction (f t).toAdd
          (tripleSixPointCentralizerProjection D a t g) (P.mkQ (f u).toAdd)
      rw [Hexacode.fullWeightVectorQuotientAction_mk, hf]
      rfl }
  exact ⟨c, fun _ => rfl⟩

/-- The original C_K(t)/O₂(C_K(t)) acts naturally on the literal U/Vt.
The section coordinates are the original chart followed by its actual
field-line quotient and the same natural-module coordinates. -/
theorem tripleSixPoint_quotient_natural (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    ∃ (e : ((K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) ⧸
        pCore 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)) ≃* SL2FourNatural.SL)
      (b : (Atlas.Codes.hexacode ⧸
        Submodule.span Hexacode.F {(tripleSixPointCoordinates D a t).toAdd}) ≃ₗ[ZMod 2]
          SL2FourNatural.V)
      (c : BinaryConjugationSection
        (K ⊓ centralizer ({(t : G)} : Set G)) U (tripleSixPoint D a t)
        (SL2FourNatural.naturalRepresentation.comp
          (e.toMonoidHom.comp (QuotientGroup.mk' _)))),
      ∀ u : U, (c.coordinates u).toAdd =
        b ((Submodule.span Hexacode.F {(tripleSixPointCoordinates D a t).toAdd}).mkQ
          (tripleSixPointCoordinates D a u).toAdd) := by
  let w := (tripleSixPointCoordinates D a t).toAdd
  have hw : w ≠ 0 := by
    intro h
    have hh : tripleSixPointCoordinates D a t = 1 := h
    exact ht ((tripleSixPointCoordinates D a).injective
      (hh.trans (tripleSixPointCoordinates D a).map_one.symm))
  obtain ⟨e₀, b, hb⟩ := Hexacode.fullWeightVectorQuotient_binary_natural w hw
    (tripleSixPoint_full_weight D a t ht heven)
  let π := tripleSixPointCentralizerProjection D a t
  let e := ((QuotientGroup.quotientMulEquivOfEq
    (tripleSixPointCentralizerProjection_ker_eq_core D a t ht heven).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π
        (tripleSixPointCentralizerProjection_surjective D a t))).trans e₀
  have he (g : (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)) :
      e (QuotientGroup.mk' _ g) = e₀ (π g) := rfl
  obtain ⟨c₀, hc₀⟩ := tripleSixPoint_quotient_section D a t
  let c : BinaryConjugationSection
      (K ⊓ centralizer ({(t : G)} : Set G)) U (tripleSixPoint D a t)
      (SL2FourNatural.naturalRepresentation.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' _))) := {
    section_le := c₀.section_le
    kernel_le := c₀.kernel_le
    normalized := c₀.normalized
    coordinates := b.toAddEquiv.toMultiplicative.toMonoidHom.comp c₀.coordinates
    onto := b.toAddEquiv.toMultiplicative.surjective.comp c₀.onto
    kernel_eq := by
      ext u
      change b (c₀.coordinates u).toAdd = 0 ↔ u ∈ (tripleSixPoint D a t).subgroupOf U
      rw [b.map_eq_zero_iff]
      exact c₀.coordinates_eq_one_iff u
    equivariant := by
      intro g u
      change b (c₀.coordinates _).toAdd =
        SL2FourNatural.naturalRepresentation (e (QuotientGroup.mk' _ g))
          (b (c₀.coordinates u).toAdd)
      rw [c₀.equivariant, he]
      exact hb (π g) (c₀.coordinates u).toAdd }
  refine ⟨e, b, c, ?_⟩
  intro u
  change b (c₀.coordinates u).toAdd = _
  rw [hc₀]

end CFSG.Quasithin.Chapter12.Section07
