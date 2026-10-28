module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Ranks
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Mathlib.LinearAlgebra.Prod

/-!
# The paired quotient in the line-offender inequality

An equivariant surjection to `W × W` induces a surjection on quotients by
fixed spaces. Its dimension inequality accounts for the factor two on p.1154.
`PairedSection` anchors this map to the actual quotient of the elementary group
`U` by `E`: its kernel is exactly the binary subspace of `E`, and its equivariance
uses the faithful conjugation action on `U` and the quotient by the local core.

This proves the paired fixed-space comparison without assuming a rank tuple.
Constructing the marked map from the fixed spaces of `τ` and `τ^y`, and proving
the separate core transvection identity, remain geometric obligations. The
conclusion supplies a best offender contained in the selected image, without
asserting that this image itself satisfies all best-offender comparisons.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of 15.3.67,
printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section
open Subgroup Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders
variable {G H : Type*} [Group G] [Group H] [Finite G]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- The relative group quotient has exactly the fixed codimension in the faithful action. -/
theorem quotientRank_eq_fixedCodim (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (U : Set G)) (A : Subgroup G) :
    quotientRank U (U ⊓ centralizer (A : Set G)) =
      fixedCodim (Representation.NormalElementaryQuotient.representation U f hf hker) (A.map f) := by
  let ρ := Representation.NormalElementaryQuotient.representation U f hf hker
  have hrU : rank U = Module.finrank (ZMod 2) (Additive U) := by
    change Nat.log 2 (Nat.card (Additive U)) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, Nat.log_pow Nat.one_lt_two]
  have hrF : rank (U ⊓ centralizer (A : Set G)) =
      Module.finrank (ZMod 2) (fixedSpace ρ (A.map f)) := by
    rw [rank, ← Nat.card_congr (Representation.NormalElementaryQuotient.fixedSpaceEquiv U f hf hker A)]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, Nat.log_pow Nat.one_lt_two]
  have hq := quotientRank_add_rank U (U ⊓ centralizer (A : Set G)) inf_le_left
  have hd := fixedCodim_add_finrank ρ (A.map f)
  rw [hrU, hrF] at hq
  change _ = fixedCodim ρ (A.map f)
  omega

section Linear
variable {K X : Type*} [Group K] [AddCommGroup X] [Module (ZMod 2) X]
  [FiniteDimensional (ZMod 2) X] [FiniteDimensional (ZMod 2) W]

omit [Finite G] in
/-- A surjective equivariant map to two identical summands gives the doubled codimension bound. -/
theorem paired_fixedCodim_le (ρ : Representation (ZMod 2) G X)
    (σ : Representation (ZMod 2) K W) (q : G →* K) (A : Subgroup G)
    (π : X →ₗ[ZMod 2] W × W) (hπ : Function.Surjective π)
    (heq : ∀ a ∈ A, ∀ v, π (ρ a v) = (σ (q a) (π v).1, σ (q a) (π v).2)) :
    2 * fixedCodim σ (A.map q) ≤ fixedCodim ρ A := by
  let F := fixedSpace σ (A.map q)
  let C := fixedSpace ρ A
  let ψ : X →ₗ[ZMod 2] (W ⧸ F) × (W ⧸ F) := (F.mkQ.prodMap F.mkQ).comp π
  have hψ : Function.Surjective ψ := by
    rintro ⟨x, y⟩
    obtain ⟨v, rfl⟩ := F.mkQ_surjective x
    obtain ⟨w, rfl⟩ := F.mkQ_surjective y
    obtain ⟨u, hu⟩ := hπ (v, w)
    exact ⟨u, by change (F.mkQ (π u).1, F.mkQ (π u).2) = _; rw [hu]⟩
  have hC : C ≤ ψ.ker := by
    intro v hv
    have hfix : (π v).1 ∈ F ∧ (π v).2 ∈ F := by
      constructor
      · rintro ⟨_, a, ha, rfl⟩
        have he := heq a ha v
        rw [show ρ a v = v from hv ⟨a, ha⟩] at he
        exact (congrArg Prod.fst he).symm
      · rintro ⟨_, a, ha, rfl⟩
        have he := heq a ha v
        rw [show ρ a v = v from hv ⟨a, ha⟩] at he
        exact (congrArg Prod.snd he).symm
    exact Prod.ext ((Submodule.Quotient.mk_eq_zero F).mpr hfix.1)
      ((Submodule.Quotient.mk_eq_zero F).mpr hfix.2)
  let φ := C.liftQ ψ hC
  have hφ : Function.Surjective φ := by
    intro w
    obtain ⟨v, hv⟩ := hψ w
    exact ⟨C.mkQ v, hv⟩
  have hd := LinearMap.finrank_le_finrank_of_surjective hφ
  rw [Module.finrank_prod] at hd
  change 2 * Module.finrank (ZMod 2) (W ⧸ F) ≤ Module.finrank (ZMod 2) (X ⧸ C)
  omega
end Linear

/-- A marked quotient by the actual subgroup `E`, with the two summands
carrying the same action of `C`. The representation and projection are data,
not a numerical dimension certificate. -/
structure PairedSection (U E C Q : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    [Q.Normal] (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (U : Set G))
    (σ : Representation (ZMod 2) (G ⧸ Q) W) where
  line_le : E ≤ U
  projection : Additive U →ₗ[ZMod 2] W × W
  surjective : Function.Surjective projection
  kernel_eq : projection.ker = Representation.NormalElementaryQuotient.subspace U (E.subgroupOf U)
  equivariant : ∀ a ∈ C, ∀ v,
    projection (Representation.NormalElementaryQuotient.representation U f hf hker (f a) v) =
      (σ (QuotientGroup.mk' Q a) (projection v).1,
        σ (QuotientGroup.mk' Q a) (projection v).2)

/-- The marked quotient supplies the paired inequality used in the rank calculation. -/
theorem PairedSection.fixedCodim_bound [FiniteDimensional (ZMod 2) W]
    {U E C Q : Subgroup G} [U.Normal] [IsElementaryAbelian 2 U] [Q.Normal]
    {f : G →* H} {hf : Function.Surjective f}
    {hker : f.ker = centralizer (U : Set G)}
    {σ : Representation (ZMod 2) (G ⧸ Q) W}
    (d : PairedSection U E C Q f hf hker σ) (A : Subgroup G) (hAC : A ≤ C) :
    2 * fixedCodim σ (A.map (QuotientGroup.mk' Q)) ≤
      quotientRank U (U ⊓ centralizer (A : Set G)) := by
  let ρ := Representation.NormalElementaryQuotient.representation U f hf hker
  have hh := paired_fixedCodim_le (ρ.comp f) σ (QuotientGroup.mk' Q) A
    d.projection d.surjective (fun a ha => d.equivariant a (hAC ha))
  rw [quotientRank_eq_fixedCodim U f hf hker A]
  have hfixed : fixedSpace (ρ.comp f) A = fixedSpace ρ (A.map f) :=
    fixedSpace_comp_map ρ f A
  have hc : fixedCodim (ρ.comp f) A = fixedCodim ρ (A.map f) :=
    congrArg (fun F : Submodule (ZMod 2) (Additive U) =>
      Module.finrank (ZMod 2) (Additive U ⧸ F)) hfixed
  change 2 * fixedCodim σ (A.map (QuotientGroup.mk' Q)) ≤ fixedCodim ρ (A.map f)
  exact hh.trans_eq hc

/-- Combine the actual paired quotient with the maximum-elementary calculation.
The core-action identity remains the transvection obligation. -/
theorem PairedSection.offender_and_best_subgroup [FiniteDimensional (ZMod 2) W]
    {S U E C A Q : Subgroup G} [U.Normal] [IsElementaryAbelian 2 U] [Q.Normal]
    {f : G →* H} {hf : Function.Surjective f}
    {hker : f.ker = centralizer (U : Set G)}
    {σ : Representation (ZMod 2) (G ⧸ Q) W}
    (d : PairedSection U E C Q f hf hker σ)
    (hU : U ≤ S) (hA : A ∈ elementaryAbelianMaxSubgroups S) (hAC : A ≤ C)
    (hkerQ : A ⊓ f.ker ≤ Q)
    (hcore : quotientRank U (U ⊓ centralizer ((A ⊓ Q : Subgroup G) : Set G)) =
      2 * rank ((A ⊓ Q).map f))
    (hne : A.map (QuotientGroup.mk' Q) ≠ ⊥) :
    IsOffender σ (A.map (QuotientGroup.mk' Q)) ∧
      ∃ B ≤ A.map (QuotientGroup.mk' Q), IsBestOffender σ B := by
  have ho := (first_summand_offender S U A Q hU hA f hker hkerQ hcore σ
    (d.fixedCodim_bound A hAC) hne).1
  exact ⟨ho, ho.exists_bestOffender σ⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders
