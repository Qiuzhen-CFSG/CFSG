module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.CentralProduct
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# Sylow coordinates for the exchanged natural blocks

Restrict the actual Sylow subgroup of H to its relatively subnormal first
block. Sylow conjugacy and transport of both model isomorphisms identify
that intersection with the inverse image of the matrix root group. The
prescribed exchanger simultaneously aligns the second block.

In these coordinates the residual Borel lift is exactly the two-residual
of the intrinsic Sylow normalizer. Its ambient image is `firstSylowResidual`.
The two coordinates of `pairBorelLift` lie in their respective residual
Borel lifts; conjugation therefore reduces containment of the published
ambient Borel to containment of the first lift in a subgroup containing
the exchanger. The exchanger itself belongs to C(G,R), since it normalizes
the nontrivial core R = O₂(XU).

This module does not prove that `firstSylowResidual` lies in C(G,R).
That characteristic-subgroup argument remains necessary for 15.4.20.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
C.1.7–13, printed pp.123–125, and the proof of 15.4.20, printed p.1164.
-/

@[expose] public section

open Subgroup CFSG.Quasithin.ChapterC
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel

variable {L F : Type*} [Group L] [Field F]

/-- The model projection kills precisely the intrinsic two-core. -/
theorem projection_ker (m : BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    (projection m).ker = pCore 2 L := by
  ext x
  simp [projection]

/-- Transport the actual quotient and module isomorphisms to align a specified Sylow subgroup. -/
theorem exists_sylow_aligned_model [Finite L] [Finite F] [CharP F 2]
    (m : BlockModuleModel L (Matrix.SL2.naturalAction F))
    (S : Sylow 2 L) :
    ∃ m' : BlockModuleModel L (Matrix.SL2.naturalAction F),
      (Matrix.SpecialLinearGroup.upperUnipotent F).comap (projection m') = S := by
  let P := (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2).comapOfKerIsPGroup
    (projection m) (by rw [projection_ker]; exact pCore_isPGroup)
    (by rw [MonoidHom.range_eq_top.mpr (projection_surjective m)]; exact le_top)
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L S P
  let e : L ≃* L := (MulAut.conj l).symm
  refine ⟨transportModel e m, ?_⟩
  have he : (S : Subgroup L).map (MulAut.conj l).toMonoidHom =
      (Matrix.SpecialLinearGroup.upperUnipotent F).comap (projection m) :=
    congrArg (fun Q : Sylow 2 L => (Q : Subgroup L)) hl
  ext x
  change projection m (l * x * l⁻¹) ∈ Matrix.SpecialLinearGroup.upperUnipotent F ↔ x ∈ S
  change (MulAut.conj l) x ∈ (Matrix.SpecialLinearGroup.upperUnipotent F).comap
    (projection m) ↔ x ∈ S
  rw [← he]
  simp only [mem_map_equiv, MulEquiv.symm_apply_apply]
  rfl

/-- An aligned Borel lift is the embedded two-residual of the Sylow normalizer. -/
theorem borelLift_eq_residual_normalizer
    (m : BlockModuleModel L (Matrix.SL2.naturalAction F)) (S : Subgroup L)
    (hS : (Matrix.SpecialLinearGroup.upperUnipotent F).comap (projection m) = S) :
    borelLift m = (pResidual 2 (normalizer (S : Set L))).map
      (normalizer (S : Set L)).subtype := by
  unfold borelLift residualPreimage
  have he : (BenderSuzuki.Converse.Borel F).comap (projection m) =
      normalizer (S : Set L) := by
    rw [← rankOneBorel_eq_sourceBorel,
      Matrix.SpecialLinearGroup.rankOneBorel,
      Subgroup.comap_normalizer_eq_of_surjective _ (projection_surjective m), hS]
  rw [he]

section Pair
variable {L₁ L₂ : Type*} [Group L₁] [Group L₂]
variable (m₁ : BlockModuleModel L₁ (Matrix.SL2.naturalAction F))
    (m₂ : BlockModuleModel L₂ (Matrix.SL2.naturalAction F))

/-- Each coordinate of the pair residual lies in its own residual Borel lift. -/
theorem pairBorelLift_le_prod :
    pairBorelLift m₁ m₂ ≤ (borelLift m₁).prod (borelLift m₂) := by
  let D := ((BenderSuzuki.Converse.Borel F).prod (BenderSuzuki.Converse.Borel F)).comap
    (pairProjection m₁ m₂)
  let f₁ : D →* (BenderSuzuki.Converse.Borel F).comap (projection m₁) :=
    { toFun x := ⟨x.val.1, x.property.1⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  let f₂ : D →* (BenderSuzuki.Converse.Borel F).comap (projection m₂) :=
    { toFun x := ⟨x.val.2, x.property.2⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨⟨f₁ x, map_pResidual_le 2 f₁ (mem_map_of_mem f₁ hx), rfl⟩,
    ⟨f₂ x, map_pResidual_le 2 f₂ (mem_map_of_mem f₂ hx), rfl⟩⟩
end Pair

section Transport
variable {L' : Type*} [Group L']

/-- Residual Borel lifts transport with the complete natural-module model. -/
theorem borelLift_transport [Finite L] (e : L ≃* L')
    (m : BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    borelLift (transportModel e m) = (borelLift m).map e.toMonoidHom := by
  unfold borelLift residualPreimage
  rw [map_embedded_pResidual]
  have he : (BenderSuzuki.Converse.Borel F).comap (projection (transportModel e m)) =
      ((BenderSuzuki.Converse.Borel F).comap (projection m)).map e.toMonoidHom := by
    ext x
    simp only [mem_comap, mem_map_equiv, transportModel_projection]
  rw [he]

end Transport

section Source
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}
variable {c : ContraryData κ d i j} (b : ExchangedBlock c)

/-- The normalizer, inside the first block, of its actual intersection with U. -/
def firstSylowNormalizer : Subgroup b.first :=
  normalizer (c.U.subgroupOf b.first : Set b.first)

/-- O²(N_{K₁}(U ∩ K₁)), formed intrinsically and then embedded in G. -/
def firstSylowResidual : Subgroup G :=
  ((pResidual 2 (firstSylowNormalizer b)).map (firstSylowNormalizer b).subtype).map
    b.first.subtype

/-- Relative subnormality makes the given Sylow intersection Sylow in the first block. -/
theorem exists_first_sylow :
    ∃ S : Sylow 2 b.first, (S : Subgroup b.first) = c.U.subgroupOf b.first := by
  obtain ⟨S, hS⟩ := c.sylow.exists_subgroupOf_eq_of_subnormal
    (b.first.subgroupOf c.H) b.relative_block.subnormal
  let e := subgroupOfEquivOfLe b.first_le
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (S : Subgroup _).map e.toMonoidHom = _
  rw [hS]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (y : G) ∈ c.U
    rw [← c.sylow_image]
    exact mem_map_of_mem _ hy
  · intro hx
    have hxU : (x : G) ∈ c.U := hx
    rw [← c.sylow_image] at hxU
    obtain ⟨y, hy, he⟩ := hxU
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change (⟨(x : G), b.first_le x.property⟩ : c.H) ∈ c.sylow
    have he' : y = ⟨(x : G), b.first_le x.property⟩ := Subtype.ext he
    exact he' ▸ hy

/-- Choose the source field and an actual model aligned with U ∩ K₁. -/
theorem exists_aligned_model :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ b.n ∧
      ∃ m : BlockModuleModel b.first (Matrix.SL2.naturalAction F),
        (Matrix.SpecialLinearGroup.upperUnipotent F).comap (projection m) =
          c.U.subgroupOf b.first := by
  obtain ⟨F, hF, hfin, hchar, hcard, _, ⟨m⟩⟩ := even_block_model b.model
  obtain ⟨S, hS⟩ := exists_first_sylow b
  obtain ⟨m', hm'⟩ := exists_sylow_aligned_model m S
  exact ⟨F, hF, hfin, hchar, hcard, m', hm'.trans hS⟩

/-- The prescribed exchanger aligns the second model with its intersection with the same U. -/
theorem conjugate_model_aligned {F : Type*} [Field F]
    (m : BlockModuleModel b.first (Matrix.SL2.naturalAction F))
    (hm : (Matrix.SpecialLinearGroup.upperUnipotent F).comap (projection m) =
      c.U.subgroupOf b.first) :
    (Matrix.SpecialLinearGroup.upperUnipotent F).comap
      (projection (conjugateModel b.first b.exchanger m)) =
        c.U.subgroupOf (ExchangedBlock.second b) := by
  let e := (MulAut.conj b.exchanger).subgroupMap b.first
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  change projection (conjugateModel b.first b.exchanger m) (e y) ∈
    Matrix.SpecialLinearGroup.upperUnipotent F ↔ _
  rw [conjugateModel_projection]
  change y ∈ (Matrix.SpecialLinearGroup.upperUnipotent F).comap (projection m) ↔ _
  rw [hm]
  change (y : G) ∈ c.U ↔ b.exchanger * (y : G) * b.exchanger⁻¹ ∈ c.U
  exact c.U.le_normalizer b.exchanger_mem y

/-- The ambient first Borel lift is the literal Sylow-normalizer residual. -/
theorem firstLift_eq_firstSylowResidual {F : Type*} [Field F]
    (m : BlockModuleModel b.first (Matrix.SL2.naturalAction F))
    (hm : (Matrix.SpecialLinearGroup.upperUnipotent F).comap (projection m) =
      c.U.subgroupOf b.first) :
    (borelLift m).map b.first.subtype = firstSylowResidual b := by
  rw [borelLift_eq_residual_normalizer m _ hm]
  rfl

/-- The second residual Borel lift is the actual conjugate of the first. -/
theorem conjugate_borelLift_map {F : Type*} [Field F]
    (m : BlockModuleModel b.first (Matrix.SL2.naturalAction F)) :
    (borelLift (conjugateModel b.first b.exchanger m)).map
      (ExchangedBlock.second b).subtype =
      ((borelLift m).map b.first.subtype).map (MulAut.conj b.exchanger).toMonoidHom := by
  let e : b.first ≃* ExchangedBlock.second b := (MulAut.conj b.exchanger).subgroupMap b.first
  calc
    _ = ((borelLift m).map e.toMonoidHom).map (ExchangedBlock.second b).subtype :=
      congrArg (Subgroup.map (ExchangedBlock.second b).subtype) (borelLift_transport e m)
    _ = _ := by rw [map_map, map_map]; rfl

/-- A subgroup containing the exchanger and the first lift contains the full pair Borel image. -/
theorem ambientBorel_le_of_firstLift {F : Type*} [Field F]
    (hc : ⁅b.first, ExchangedBlock.second b⁆ = ⊥)
    (m : BlockModuleModel b.first (Matrix.SL2.naturalAction F))
    (M : Subgroup G) (hr : b.exchanger ∈ M)
    (hfirst : (borelLift m).map b.first.subtype ≤ M) :
    ExchangedBlock.ambientBorel b hc m ≤ M := by
  have hsecond : (borelLift (conjugateModel b.first b.exchanger m)).map
      (ExchangedBlock.second b).subtype ≤ M := by
    rw [conjugate_borelLift_map]
    exact (map_mono hfirst).trans
      (mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer hr)).le
  rintro _ ⟨l, hl, rfl⟩
  have hl' := pairBorelLift_le_prod m (conjugateModel b.first b.exchanger m) hl
  exact M.mul_mem (hfirst (mem_map_of_mem b.first.subtype hl'.1))
    (hsecond (mem_map_of_mem (ExchangedBlock.second b).subtype hl'.2))

/-- The exchanger normalizes the nontrivial contrary core, so it belongs to C(G,R). -/
theorem exchanger_mem_characteristicNormalizerClosure :
    b.exchanger ∈ characteristicNormalizerClosure ((d.wholeX ⊔ c.U : Subgroup G).pCoreIn 2) := by
  have hne : (d.wholeX ⊔ c.U : Subgroup G).pCoreIn 2 ≠ ⊥ := by
    intro he
    have hV : d.V₁ i = ⊥ := bot_unique (he ▸ c.four_le_contrary_core)
    have hcard := c.V₁_card i
    rw [hV] at hcard
    simp at hcard
  apply normalizer_le_characteristicNormalizerClosure_self _ hne
  apply (d.wholeX ⊔ c.U : Subgroup G).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 (d.wholeX ⊔ c.U : Subgroup G)))
  exact (show c.U ≤ d.wholeX ⊔ c.U from le_sup_right) b.exchanger_mem

end Source
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel
