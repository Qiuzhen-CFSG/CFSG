module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.Section

/-!
# Conjugating the actual central section

An ambient group isomorphism induces the canonical isomorphism on the
quotients by the two-cores. Precomposing the action and the section projection
with these inverse isomorphisms transports the source conjugation model,
including its kernel and equivariance on representatives. Images of conjugated
subgroups keep the same vector coordinates, and star images commute with the
specified quotient isomorphism.

These transports supply module data at the other endpoint. They do not
identify the swapped actor with the conjugate of the original actor; the
nonsplitting hypotheses for that swapped actor need their own justification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Remark F.9.17,
printed p.324, as used in 13.8.25, printed p.962.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]

/-- The actual isomorphism between the endpoint quotients by their two-cores. -/
noncomputable def starEquiv (e : G ≃* G) (H : Subgroup G) :
    Source.Hstar H ≃* Source.Hstar (H.map e.toMonoidHom) :=
  let f := H.equivMapOfInjective e.toMonoidHom e.injective
  QuotientGroup.congr _ _ f (pCore_map_iso 2 f)

theorem starEquiv_mk (e : G ≃* G) (H : Subgroup G) (h : H) :
    starEquiv e H (QuotientGroup.mk' (pCore 2 H) h) =
      QuotientGroup.mk' (pCore 2 (H.map e.toMonoidHom))
        ((H.equivMapOfInjective e.toMonoidHom e.injective) h) := rfl

theorem equivMap_symm_val (e : G ≃* G) (X : Subgroup G)
    (x : X.map e.toMonoidHom) :
    ((X.equivMapOfInjective e.toMonoidHom e.injective).symm x : G) = e.symm x := by
  apply e.injective
  have hh := congrArg Subtype.val
    ((X.equivMapOfInjective e.toMonoidHom e.injective).apply_symm_apply x)
  exact hh.trans (e.apply_symm_apply x).symm

theorem starEquiv_symm_mk (e : G ≃* G) (H : Subgroup G)
    (h : H.map e.toMonoidHom) :
    (starEquiv e H).symm (QuotientGroup.mk' (pCore 2 (H.map e.toMonoidHom)) h) =
      QuotientGroup.mk' (pCore 2 H)
        ((H.equivMapOfInjective e.toMonoidHom e.injective).symm h) := by
  apply (starEquiv e H).injective
  rw [MulEquiv.apply_symm_apply, starEquiv_mk, MulEquiv.apply_symm_apply]

/-- Transport the conjugation model, retaining U as the coordinate carrier. -/
noncomputable def conjugateSection {H UH Z : Subgroup G}
    {ρ : Representation (ZMod 2) (Source.Hstar H) U}
    (s : ConjugationSection H UH Z ρ) (e : G ≃* G) :
    ConjugationSection (H.map e.toMonoidHom) (UH.map e.toMonoidHom)
      (Z.map e.toMonoidHom) (ρ.comp (starEquiv e H).symm.toMonoidHom) where
  le := map_mono s.le
  normalizes := by
    rw [← map_equiv_normalizer_eq]
    exact map_mono s.normalizes
  centralizes := by
    rintro _ ⟨h, hh, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e ((mem_centralizer_iff.mp (s.centralizes hh)) z hz)
  line_le := map_mono s.line_le
  quotient := s.quotient.comp (UH.equivMapOfInjective e.toMonoidHom e.injective).symm.toMonoidHom
  surjective := s.surjective.comp (UH.equivMapOfInjective e.toMonoidHom e.injective).symm.surjective
  kernel := by
    ext x
    change (UH.equivMapOfInjective e.toMonoidHom e.injective).symm x ∈ s.quotient.ker ↔
      (x : G) ∈ Z.map e.toMonoidHom
    rw [s.kernel, mem_subgroupOf, equivMap_symm_val, mem_map_equiv]
  conjugates := by
    intro a u
    change ρ ((starEquiv e H).symm
      (QuotientGroup.mk' (pCore 2 (H.map e.toMonoidHom)) a))
      (s.quotient ((UH.equivMapOfInjective e.toMonoidHom e.injective).symm u)).toAdd = _
    rw [starEquiv_symm_mk, s.conjugates]
    apply congrArg (fun x : UH => (s.quotient x).toAdd)
    apply Subtype.ext
    simp only [MulEquiv.coe_toMonoidHom, equivMap_symm_val, map_mul, map_inv]

/-- The image of a conjugated subgroup has exactly the same coordinates. -/
theorem conjugateSection_image {H UH Z : Subgroup G}
    {ρ : Representation (ZMod 2) (Source.Hstar H) U}
    (s : ConjugationSection H UH Z ρ) (e : G ≃* G) (X : Subgroup G) :
    (conjugateSection s e).image (X.map e.toMonoidHom) = s.image X := by
  ext u
  rw [(conjugateSection s e).mem_image, s.mem_image]
  constructor
  · rintro ⟨x, hx, he⟩
    refine ⟨(UH.equivMapOfInjective e.toMonoidHom e.injective).symm x, ?_, he⟩
    rw [equivMap_symm_val]
    exact mem_map_equiv.mp hx
  · rintro ⟨x, hx, he⟩
    refine ⟨(UH.equivMapOfInjective e.toMonoidHom e.injective) x,
      mem_map_of_mem e.toMonoidHom hx, ?_⟩
    change (s.quotient ((UH.equivMapOfInjective e.toMonoidHom e.injective).symm
      ((UH.equivMapOfInjective e.toMonoidHom e.injective) x))).toAdd = u
    rwa [MulEquiv.symm_apply_apply]

/-- Star images commute with the specified endpoint isomorphism. -/
theorem starImage_map (e : G ≃* G) (H X : Subgroup G) :
    (Source.starImage H X).map (starEquiv e H).toMonoidHom =
      Source.starImage (H.map e.toMonoidHom) (X.map e.toMonoidHom) := by
  ext q
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(H.equivMapOfInjective e.toMonoidHom e.injective) x,
      mem_map_of_mem e.toMonoidHom hx, ?_⟩
    exact (starEquiv_mk e H x).symm
  · rintro ⟨y, hy, rfl⟩
    let x := (H.equivMapOfInjective e.toMonoidHom e.injective).symm y
    refine ⟨QuotientGroup.mk' (pCore 2 H) x, ⟨x, ?_, rfl⟩, ?_⟩
    · change (x : G) ∈ X
      rw [show (x : G) = e.symm y from equivMap_symm_val e H y]
      exact mem_map_equiv.mp hy
    · change starEquiv e H (QuotientGroup.mk' (pCore 2 H) x) = _
      rw [starEquiv_mk]
      simp only [x, MulEquiv.apply_symm_apply]

/-- Faithfulness is preserved for this actual transported action. -/
theorem conjugateSection_faithful {H : Subgroup G}
    {ρ : Representation (ZMod 2) (Source.Hstar H) U}
    (e : G ≃* G) (hρ : Function.Injective ρ) :
    Function.Injective (ρ.comp (starEquiv e H).symm.toMonoidHom) := by
  intro a b hab
  exact (starEquiv e H).symm.injective (hρ hab)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
