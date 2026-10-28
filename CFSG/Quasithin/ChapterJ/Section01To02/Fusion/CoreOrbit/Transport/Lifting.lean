module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.CoreOrbit.Definitions
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.Basic
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Transvections

/-!
# Lifting an elementary quotient orbit by central commutators

For u in U minus V, J.2.3(6) says that the commutator homomorphism
S → V has full image. Therefore S moves u to every element of its V-coset.
This converts actual L-transport on U/V into conjugation of elements of U.
The full commutator equality remains an explicit earlier-source premise;
its producer is the J.2.3 special-core development.

Source: Aschbacher–Smith, J.2.3(6) and the final sentence of J.2.8,
printed pp.433,438.
-/

public section
noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
variable {G : Type*} [Group G] [Finite G]

/-- A full central commutator row realizes every displacement in V. -/
theorem conjugate_of_same_V_coset (d : LocalSetup G)
    (u : d.toTypeRuSetup.S)
    (hfull : ⁅zpowers (u : G), d.toTypeRuSetup.S⁆ = d.V)
    (v : G) (hv : (u : G)⁻¹ * v ∈ d.V) :
    ∃ t : d.toTypeRuSetup.S, (t : G) * u * (t : G)⁻¹ = v := by
  let f := ClassTwo.commutatorHom d.ru1.classTwo u
  have hmap : f.range.map d.toTypeRuSetup.S.subtype = d.V := by
    rw [ClassTwo.commutatorHom_range, RuOne.commutator_map, hfull]
  have hdisp : (u : G)⁻¹ * v ∈ f.range.map d.toTypeRuSetup.S.subtype := by
    rwa [hmap]
  obtain ⟨a, ⟨t, ht⟩, ha⟩ := hdisp
  have he : (⁅u, t⁆ : d.toTypeRuSetup.S) = a := ht
  have hc : ⁅(u : G), (t : G)⁆ = (u : G)⁻¹ * v :=
    (congrArg Subtype.val he).trans ha
  refine ⟨t⁻¹, ?_⟩
  have hz := d.ru1.central_V hv t t.property
  rw [← hc] at hz
  have hmul : (u : G) * ⁅(u : G), (t : G)⁆ = v := by rw [hc]; group
  change (t : G)⁻¹ * u * ((t : G)⁻¹)⁻¹ = v
  calc
    _ = (t : G)⁻¹ * ⁅(u : G), (t : G)⁆ * t * u := by
      rw [commutatorElement_def]
      group
    _ = ⁅(u : G), (t : G)⁆ * u := by
      simpa only [mul_assoc, inv_mul_cancel_left] using
        congrArg (fun a : G => (t : G)⁻¹ * a * u) hz.symm
    _ = (u : G) * ⁅(u : G), (t : G)⁆ := by
      rw [hc]
      exact (d.ru1.central_V hv u u.property).symm
    _ = v := hmul

/-- An actual quotient transporter, followed by an S-conjugator, gives an
actual L-conjugator. No lifting conclusion is included among the premises. -/
theorem elementaryTransport_of_quotient (d : LocalSetup G)
    (hfull : ∀ t : d.toTypeRuSetup.S, (t : G) ∉ d.V →
      ⁅zpowers (t : G), d.toTypeRuSetup.S⁆ = d.V)
    (hquot : ∀ u v : G, u ∈ d.toTypeRuSetup.U → u ∉ d.V →
      v ∈ d.toTypeRuSetup.U → v ∉ d.V →
      ∃ l : d.L, ((l : G) * u * (l : G)⁻¹)⁻¹ * v ∈ d.V) :
    ElementaryTransport d.toTypeRuSetup := by
  intro u v hu huV hv hvV
  obtain ⟨l, hl⟩ := hquot u v hu huV hv hvV
  let u' : d.toTypeRuSetup.S := ⟨l * u * (l : G)⁻¹,
    (mem_normalizer_iff.mp (d.ru1.steinberg.normalized l.property) u).mp
      (d.U_le_S hu)⟩
  have hu'V : (u' : G) ∉ d.V := by
    intro he
    exact huV ((mem_normalizer_iff.mp (d.ru1.natural.normalized l.property) u).mpr he)
  obtain ⟨t, ht⟩ := conjugate_of_same_V_coset d u' (hfull u' hu'V) v hl
  refine ⟨⟨(t : G) * l, d.L.mul_mem (pCoreIn_le 2 _ t.property) l.property⟩, ?_⟩
  change ((t : G) * l) * u * ((t : G) * l)⁻¹ = v
  simpa only [u', mul_inv_rev, mul_assoc] using ht

end CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
