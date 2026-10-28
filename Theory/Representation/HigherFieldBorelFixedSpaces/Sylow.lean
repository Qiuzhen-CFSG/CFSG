module
public import Theory.Representation.HigherFieldBorelFixedSpaces.Natural
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Natural coordinates fixed by arbitrary rank-one Borels

Sylow conjugacy transports the standard upper-triangular Borel to every
Sylow normalizer of SL₂(F). For a binary field with at least four elements,
this normalizer is two-perfect and has zero fixed space on the natural module.
The final theorem transports both facts along an actual group equivalence
and an equivariant linear coordinate map; the map need not be injective.

Source application: Aschbacher–Smith, `refs/quasithin.pdf`, proof of 3.1.9(5).
-/

public section
open Subgroup Representation Representation.BinaryOffender
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace Representation.HigherFieldBorelFixedSpaces
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem sl2_sylowNormalizer_isPPerfect (hF : 4 ≤ Nat.card F) (P : Sylow 2 SL(2,F)) :
    IsPPerfect 2 (normalizer (P : Set SL(2,F))) := by
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq SL(2,F) P (upperUnipotentSylow F 2)
  have hP : (P : Subgroup SL(2,F)).map (MulAut.conj a).toMonoidHom = upperUnipotent F :=
    congrArg Sylow.toSubgroup ha
  have hB : (normalizer (P : Set SL(2,F))).map (MulAut.conj a).toMonoidHom = rankOneBorel F := by
    calc
      _ = normalizer ((P : Subgroup SL(2,F)).map (MulAut.conj a).toMonoidHom : Set SL(2,F)) :=
        map_equiv_normalizer_eq (P : Subgroup SL(2,F)) (MulAut.conj a)
      _ = rankOneBorel F := by rw [hP]
  let e := ((normalizer (P : Set SL(2,F))).equivMapOfInjective
    (MulAut.conj a).toMonoidHom (MulAut.conj a).injective).trans (MulEquiv.subgroupCongr hB)
  exact (rankOneBorel_isPPerfect hF).of_surjective e.symm.toMonoidHom e.symm.surjective

variable [Algebra (ZMod 2) F]
theorem sl2_sylowNormalizer_fixedSpace (hF : 2 < Nat.card F) (P : Sylow 2 SL(2,F)) :
    fixedSpace (binaryNatural (F := F) 2) (normalizer (P : Set SL(2,F))) = ⊥ := by
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq SL(2,F) P (upperUnipotentSylow F 2)
  have hP : (P : Subgroup SL(2,F)).map (MulAut.conj a).toMonoidHom = upperUnipotent F :=
    congrArg Sylow.toSubgroup ha
  have hB : (normalizer (P : Set SL(2,F))).map (MulAut.conj a).toMonoidHom = rankOneBorel F := by
    calc
      _ = normalizer ((P : Subgroup SL(2,F)).map (MulAut.conj a).toMonoidHom : Set SL(2,F)) :=
        map_equiv_normalizer_eq (P : Subgroup SL(2,F)) (MulAut.conj a)
      _ = rankOneBorel F := by rw [hP]
  let e := fixedSpaceConjEquiv (binaryNatural (F := F) 2) (normalizer (P : Set SL(2,F))) a
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have he : e ⟨v,hv⟩ = 0 := by
    apply Subtype.ext
    exact (Submodule.mem_bot (R := ZMod 2)).mp
      (by
        have hh := (e ⟨v,hv⟩).property
        change _ ∈ fixedSpace (binaryNatural (F := F) 2)
          ((normalizer (P : Set SL(2,F))).map (MulAut.conj a).toMonoidHom) at hh
        simpa only [hB,sl2_borel_fixedSpace hF] using hh)
  exact congrArg Subtype.val (e.injective (he.trans e.map_zero.symm))
end Representation.HigherFieldBorelFixedSpaces

namespace Representation.HigherFieldBorelFixedSpaces
variable {F E W : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group E] [Finite E] [AddCommGroup W] [Module (ZMod 2) W]

theorem natural_sylowNormalizer
    (hF : 4 ≤ Nat.card F) (P : Sylow 2 E)
    (ρ : Representation (ZMod 2) E W) (e : E ≃* SL(2,F))
    (f : W →ₗ[ZMod 2] (Fin 2 → F))
    (hf : ∀ g v, f (ρ g v) = binaryNatural 2 (e g) (f v)) :
    IsPPerfect 2 (normalizer (P : Set E)) ∧
      ∀ v ∈ fixedSpace ρ (normalizer (P : Set E)), f v = 0 := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hB : (normalizer (P : Set E)).map e.toMonoidHom =
      normalizer (Q : Set SL(2,F)) :=
    map_equiv_normalizer_eq (P : Subgroup E) e
  let b := ((normalizer (P : Set E)).equivMapOfInjective
    e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hB)
  refine ⟨(sl2_sylowNormalizer_isPPerfect hF Q).of_surjective
    b.symm.toMonoidHom b.symm.surjective, ?_⟩
  intro v hv
  have hfv : f v ∈ fixedSpace (binaryNatural (F := F) 2) (normalizer (Q : Set SL(2,F))) := by
    intro z
    obtain ⟨g,hg,he⟩ := (show (z : SL(2,F)) ∈ (normalizer (P : Set E)).map e.toMonoidHom from
      hB.symm ▸ z.property)
    change binaryNatural 2 (z : SL(2,F)) (f v) = f v
    calc
      binaryNatural 2 (z : SL(2,F)) (f v) = binaryNatural 2 (e g) (f v) :=
        congrArg (fun t : SL(2,F) => binaryNatural 2 t (f v)) he.symm
      _ = f (ρ g v) := (hf g v).symm
      _ = f v := congrArg f (hv ⟨g,hg⟩)
  rw [sl2_sylowNormalizer_fixedSpace (by omega) Q,Submodule.mem_bot] at hfv
  exact hfv
end Representation.HigherFieldBorelFixedSpaces
