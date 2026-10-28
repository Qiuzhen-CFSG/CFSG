module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.Layers

/-! # Transport of an intrinsic core-center section
An actual multiplicative equivalence carries the two-core, its commutator,
and its center to their intrinsic counterparts. This transports the section
without changing the actor or replacing either group by a quotient image.
Source: the intrinsic local/component comparison in C.1.34 and 15.4.20.
-/

@[expose] public section
open Subgroup CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases

variable {A B : Type*} [Group A] [Group B]

/-- The intrinsic core commutator is preserved by an actual isomorphism. -/
theorem blockU_map_equiv (e : A ≃* B) : (blockU A).map e.toMonoidHom = blockU B := by
  rw [blockU, blockU, map_commutator, pCore_map_iso, map_top_of_surjective _ e.surjective]

/-- Transport a core-center section back along an isomorphism. -/
noncomputable def transportSection (e : A ≃* B) {a : ℕ} (m : CoreCenterSection B a) :
    CoreCenterSection A a := by
  let J := m.layer.comap e.toMonoidHom
  have hn : J.Normal := m.normal.comap e.toMonoidHom
  let f : J →* m.layer :=
    { toFun x := ⟨e x, x.property⟩
      map_one' := Subtype.ext e.map_one
      map_mul' x y := Subtype.ext (e.map_mul x y) }
  let eqQ : (A ⧸ pCore 2 A) ≃* (B ⧸ pCore 2 B) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  refine {
    quotientIso := eqQ.trans m.quotientIso
    layer := J
    normal := hn
    center_le := ?_
    map := m.map.comp f
    intertwining := ?_
    kernel_central := ?_ }
  · rintro x ⟨z, hz, rfl⟩
    have he : e z ∈ blockU B := by
      rw [← blockU_map_equiv e]
      exact mem_map_of_mem e.toMonoidHom z.property
    apply m.center_le
    refine ⟨⟨e z, he⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro b
    have hb : (b : B) ∈ (blockU A).map e.toMonoidHom :=
      (blockU_map_equiv e).symm ▸ b.property
    obtain ⟨x, hx, hxb⟩ := hb
    apply Subtype.ext
    have hh := congrArg (fun y : blockU A => e (y : A)) (mem_center_iff.mp hz ⟨x, hx⟩)
    simp only [coe_mul, map_mul] at hh
    change e x = (b : B) at hxb
    change (b : B) * e z = e z * (b : B)
    rwa [hxb] at hh
  · intro x y
    have he : f (sectionConjugate J hn x y) =
        sectionConjugate m.layer m.normal (e x) (f y) := by
      apply Subtype.ext
      simp [f, sectionConjugate]
    change Multiplicative.toAdd (m.map (f (sectionConjugate J hn x y))) = _
    rw [he, m.intertwining]
    rfl
  · intro x hx
    have hz := m.kernel_central (f x) hx
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    have hh := mem_center_iff.mp hz (e y)
    change e y * e (x : A) = e (x : A) * e y at hh
    simpa only [map_mul] using hh

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
