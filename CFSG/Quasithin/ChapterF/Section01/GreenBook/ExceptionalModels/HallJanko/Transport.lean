module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.HallJanko

/-!
# Transport of the Hall--Janko source marking

An actual ambient isomorphism carries local Sylow normalizers, their common
Borel, and the two full parabolics to their images. This gives a compatible
isomorphism of the concrete inclusion amalgams. Intrinsic core and quotient
transport then carries the four outer-case local calculations to the image.

The final construction accepts local data in the explicit permutation
extension and the two standard-pair orbit calculations needed to identify
that extension with `MulAut Carrier`. It does not discharge those premises
or strengthen parabolic recognition to compatible amalgam recognition.

Source: Aschbacher--Smith F.1.12(I)(11), printed p.263; the transport uses
`Theory.GroupTheory.Amalgam.LocalStructure`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace CFSG.Quasithin.ChapterF.GreenBook.HallJanko
open Theory.GroupTheory
open Sporadic.LeechRelated.J2

variable {G H : Type*} [Group G] [Group H]

private theorem commonBorel_map (e : G ≃* H) (L : Fin 2 → Subgroup G) (S : Subgroup G) :
    (Source.commonBorel L S).map e.toMonoidHom =
      Source.commonBorel (fun i => (L i).map e.toMonoidHom) (S.map e.toMonoidHom) := by
  simp only [Source.commonBorel, Source.borel, Subgroup.map_sup,
    Subgroup.map_inf _ _ e.toMonoidHom e.injective, Subgroup.map_equiv_normalizer_eq]

namespace Marking

variable [Finite G]

/-- Carry all local marks across the same ambient group isomorphism. -/
def map (m : Marking G) (e : G ≃* H) : Marking H where
  L i := (m.L i).map e.toMonoidHom
  S := m.S.mapSurjective (f := e.toMonoidHom) e.surjective
  borel_normalizes i := by
    change Source.commonBorel _ ((m.S : Subgroup G).map e.toMonoidHom) ≤ _
    rw [← commonBorel_map, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono (m.borel_normalizes i)
  overlap := by
    change ((m.L 0).map e.toMonoidHom ⊔ Source.commonBorel _
        ((m.S : Subgroup G).map e.toMonoidHom)) ⊓
      ((m.L 1).map e.toMonoidHom ⊔ Source.commonBorel _
        ((m.S : Subgroup G).map e.toMonoidHom)) = _
    rw [← commonBorel_map, ← Subgroup.map_sup, ← Subgroup.map_sup,
      ← Subgroup.map_inf _ _ e.toMonoidHom e.injective, m.overlap]
    simpa only [Sylow.coe_mapSurjective] using commonBorel_map e m.L m.S
  generated := by
    change (m.L 0).map e.toMonoidHom ⊔ (m.L 1).map e.toMonoidHom ⊔
      (m.S : Subgroup G).map e.toMonoidHom = ⊤
    rw [← Subgroup.map_sup, ← Subgroup.map_sup, m.generated,
      Subgroup.map_top_of_surjective _ e.surjective]

@[simp] theorem map_B (m : Marking G) (e : G ≃* H) :
    (m.map e).B = m.B.map e.toMonoidHom := (commonBorel_map e m.L m.S).symm

@[simp] theorem map_P (m : Marking G) (e : G ≃* H) (i : Fin 2) :
    (m.map e).P i = (m.P i).map e.toMonoidHom := by
  change (m.L i).map e.toMonoidHom ⊔ (m.map e).B = _
  rw [map_B, ← Subgroup.map_sup]
  rfl

@[simp] theorem map_LS (m : Marking G) (e : G ≃* H) (i : Fin 2) :
    (m.map e).LS i = (m.LS i).map e.toMonoidHom := by
  change (m.L i).map e.toMonoidHom ⊔ (m.S : Subgroup G).map e.toMonoidHom = _
  exact (Subgroup.map_sup _ _ _).symm

/-- Compatibility holds for this constructed ambient transport, including
the whole Borel; it is not asserted for arbitrary parabolic equivalences. -/
def mapAmalgamIso (m : Marking G) (e : G ≃* H) :
    RankTwoAmalgam.Iso m.amalgam (m.map e).amalgam :=
  RankTwoAmalgam.ofSubgroupsIso e (m.B_le_P 0) (m.B_le_P 1)
    ((m.map e).B_le_P 0) ((m.map e).B_le_P 1)
    (m.map_P e 0).symm (m.map_B e).symm (m.map_P e 1).symm

end Marking

private theorem quaternionDihedral_of_equiv {G H : Type*} [Group G] [Group H]
    {K : Subgroup G} {K' : Subgroup H} (e : K ≃* K')
    (h : IsQuaternionDihedralCore K) : IsQuaternionDihedralCore K' := by
  obtain ⟨B, C, ⟨eB⟩, ⟨eC⟩, hI, hcomm, hgen, hcard⟩ := h
  refine ⟨B.map e.toMonoidHom, C.map e.toMonoidHom,
    ⟨(e.subgroupMap B).symm.trans eB⟩, ⟨(e.subgroupMap C).symm.trans eC⟩,
    ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_inf _ _ e.toMonoidHom e.injective]
    exact (Nat.card_congr (e.subgroupMap (B ⊓ C)).toEquiv).symm.trans hI
  · intro b hb c hc
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hc
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e (hcomm x hx y hy)
  · rw [← Subgroup.map_sup, hgen, Subgroup.map_top_of_surjective _ e.surjective]
  · rw [← Nat.card_congr e.toEquiv, hcard]

namespace AutLocalModel

variable [Finite G]

/-- Transport both numerator groups and their own intrinsic two-cores. -/
def map (m : AutLocalModel G) (e : G ≃* H) : AutLocalModel H where
  toMarking := m.toMarking.map e
  L₁S_quotient := by
    let f : m.toMarking.LS 0 ≃* (m.toMarking.map e).LS 0 :=
      LocalCoreTransport.subgroupEquiv e (m.toMarking.map_LS e 0).symm
    exact m.L₁S_quotient.map (fun g => (LocalCoreTransport.quotientEquiv 2 f).symm.trans g)
  L₁_core := by
    exact quaternionDihedral_of_equiv
      (LocalCoreTransport.coreEquiv 2 (e.subgroupMap (m.L 0))) m.L₁_core
  L₂_quotient := m.L₂_quotient.map (fun g =>
    (LocalCoreTransport.quotientEquiv 2 (e.subgroupMap (m.L 1))).symm.trans g)
  L₂_core_card :=
    (LocalCoreTransport.core_card 2 (e.subgroupMap (m.L 1))).symm.trans m.L₂_core_card

end AutLocalModel

/-- Assemble the actual automorphism-group model after the finite extension
local calculations and both standard-pair calculations have been proved.
These remain genuine premises; this definition asserts no model existence. -/
noncomputable def ExtensionModel.toAutJ2Model_of_pair_calculations
    (m : ExtensionModel)
    (hfirst : ∀ x y : Carrier, GeneratorPair.PairProfile x y →
      ∃ g : Carrier, x = MulAut.conj g GeneratorPair.a)
    (hsecond : ∀ y : Carrier, GeneratorPair.PairProfile GeneratorPair.a y →
      ∃ c : Carrier, MulAut.conj c GeneratorPair.a = GeneratorPair.a ∧
        (y = MulAut.conj c GeneratorPair.b ∨ y = MulAut.conj c GeneratorPair.b⁻¹)) :
    AutJ2Model :=
  m.map (ExceptionalParabolics.extensionEquivAut_of_pair_calculations hfirst hsecond)

end CFSG.Quasithin.ChapterF.GreenBook.HallJanko
