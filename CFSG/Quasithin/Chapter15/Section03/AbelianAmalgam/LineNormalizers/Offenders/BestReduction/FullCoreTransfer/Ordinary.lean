module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer.Bootstrap

/-!
# Ordinary maximum images in the same temporary centralizer

Conjugate each maximum elementary subgroup of C_H(E) into the unchanged
Sylow T_E. Normality of C_H(E) preserves its membership, and the source
maximum-family comparison makes the conjugate maximum in T_E. The actual
paired quotient and common-center transvections then give ordinary offending;
conjugacy returns the inequality to the original subgroup.

The kernel containment is used only inside T_E, never for the entire
centralizer of U. Source: Aschbacher–Smith, proof of 15.3.67, printed
pp.1153–1154 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
open Replacement.Transvections
universe u v
variable {G L : Type u} [Group G] [Finite G] [Group L]
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- Every nontrivial maximum-family image is an ordinary offender on the
actual first summand. Bestness is supplied separately by the full classifier. -/
theorem temporary_maximum_images_ordinary
    (Y T V E : Subgroup G) [IsMulCommutative V]
    [(Replacement.Transvections.localSpan T V E).Normal] [IsElementaryAbelian 2 (Replacement.Transvections.localSpan T V E)]
    (d : TemporaryData Y T V E)
    (f : temporaryLineNormalizer T V E →* L) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E)))
    (geom : FixedGeometry (localRepresentation T V E f hf hker)
      (f d.tau) (f d.conjugator) (localLineSpace T V E))
    (σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) W)
    (paired : PairedSection (Replacement.Transvections.localSpan T V E) (localLine T V E)
      (localCentralizer T V E) (localCore T V E) f hf hker σ)
    (hcompare : ∃ B ∈ Stellmacher.elementaryAbelianMaxSubgroups
      ((lineT T E).subgroupOf (temporaryLineNormalizer T V E)), B ≤ localCentralizer T V E)
    (A : Subgroup (temporaryLineNormalizer T V E))
    (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups (localCentralizer T V E))
    (hne : A.map (QuotientGroup.mk' (localCore T V E)) ≠ ⊥) :
    IsOffender σ (A.map (QuotientGroup.mk' (localCore T V E))) := by
  let H := temporaryLineNormalizer T V E
  let C := localCentralizer T V E
  let q := QuotientGroup.mk' (localCore T V E)
  let : C.Normal := localCentralizer_normal T V E
    (line_le_temporary T V E d.line_le d.span_le_sylow)
  obtain ⟨S, hS⟩ := Replacement.lineT_sylow_temporary T V E d.line_le d.sylow d.sylow_eq
  have hST : (S : Subgroup H) = (lineT T E).subgroupOf H := by
    rw [← hS]
    exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  obtain ⟨S₀, hAS₀⟩ := hA.2.1.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S₀ S
  let e := MulAut.conj g
  let X := A.map e.toMonoidHom
  have hSS : (S₀ : Subgroup H).map e.toMonoidHom = (S : Subgroup H) := by
    change ((g • S₀ : Sylow 2 H) : Subgroup H) = (S : Subgroup H)
    rw [hg]
  have hXT : X ≤ (lineT T E).subgroupOf H :=
    (map_mono hAS₀).trans (hSS.trans hST).le
  have hXC : X ≤ C := by
    exact (map_mono hA.1).trans_eq (Normal.map_conj_eq C g)
  obtain ⟨B, hB, hBC⟩ := hcompare
  have hX : X ∈ Stellmacher.elementaryAbelianMaxSubgroups
      ((lineT T E).subgroupOf H) := by
    refine ⟨hXT, hA.2.1.map e.toMonoidHom, fun D hDT hD => ?_⟩
    change Nat.card D ≤ Nat.card (A.map e.toMonoidHom)
    rw [card_map_of_injective e.injective]
    exact (hB.2.2 D hDT hD).trans (hA.2.2 B hBC hB.2.1)
  have hmap : X.map q = (A.map q).map (MulAut.conj (q g)).toMonoidHom := by
    dsimp only [X]
    rw [map_map, map_map]
    congr 1
  have hXne : X.map q ≠ ⊥ := by
    rw [hmap]
    exact fun hb => hne ((map_eq_bot_iff_of_injective _ (MulAut.conj (q g)).injective).mp hb)
  have ho := (paired.offender_and_best_subgroup (comap_mono d.span_le_sylow) hX hXC
    (temporary_action_kernel_le_core Y T V E f hker d X hXT)
    (temporary_core_quotientRank Y T V E f hf hker d geom (X ⊓ localCore T V E) inf_le_right)
    hXne).1
  refine ⟨⟨hne, hA.2.1.map q⟩, ?_⟩
  have hh := ho.2
  rw [hmap, fixedCodim_map_conj, rank_map_conj] at hh
  exact hh

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
