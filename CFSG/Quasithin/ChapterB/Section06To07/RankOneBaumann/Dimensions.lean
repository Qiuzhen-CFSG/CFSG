module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.Offenders

/-!
# The exact dimensions in the natural rank-one Baumann argument

The maximum-elementary offender inequality and the absence of strong
offenders make the Thompson fixed codimension exactly the field degree.
The literal kernel of the natural quotient is the residual fixed space,
so rank-nullity gives twice that degree for the residual codimension.
No complement of that fixed space is assumed.
Source: Aschbacher–Smith B.6.10, hypothesis (d) of B.2.18, printed p.117.
-/

open Subgroup Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
open BaumannArgument
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
  [Algebra (ZMod 2) F]
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F
local notation "N" => SL2NaturalOffenders.NoStrong.natural (F := F)

public theorem thompson_fixedCodim_of_natural_quotient
    (T : Sylow 2 G) (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* D) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hUT : U ≤ T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (f : Additive U →ₗ[ZMod 2] (Fin 2 → F)) (hf : Function.Surjective f)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hker g v) = N g (f v)) :
    fixedCodim U (elementaryAbelianMaxJ (T : Subgroup G)) = Module.finrank (ZMod 2) F := by
  have hno := noStrong_of_natural_quotient U q hq hker f hf he (T : Subgroup G)
  have hj := (thompson_baumann_images_of_natural_quotient T U q hq hker hUT hJ f hf he).1
  have hex : ∃ B ∈ elementaryAbelianMaxSubgroups (T : Subgroup G), B.map q ≠ ⊥ := by
    by_contra! hn
    apply hJ
    rw [←hker]
    exact sSup_le fun B hB => (map_eq_bot_iff B).mp (hn B hB)
  obtain ⟨B,hB,hne⟩ := hex
  have hb := offender_eq_sylow_of_natural_quotient _ f hf he (T.mapSurjective hq)
    (B.map q) (map_mono hB.1)
    (Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
      U q hq hker (T : Subgroup G) B hUT hB hne).isOffender
  have hcod : fixedCodim U (elementaryAbelianMaxJ (T : Subgroup G)) = fixedCodim U B := by
    rw [fixedCodim_eq_quotient_representation U q hq hker,
      fixedCodim_eq_quotient_representation U q hq hker,hj,hb]
    rfl
  rw [hcod,maximal_rank_equality U (T : Subgroup G) B hUT hno hB,
    ←relIndex_ker,actionMap_ker,←hker,relIndex_ker,hb]
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  have hc : Nat.card (T.mapSurjective hq) = Nat.card F :=
    (Nat.card_congr ((T.mapSurjective hq).equiv
      (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2)).toEquiv).trans
        (Matrix.SpecialLinearGroup.card_upperUnipotent F)
  rw [hc]
  have hF : Nat.card F = 2 ^ Module.finrank (ZMod 2) F := by
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F))
  rw [hF,Nat.log_pow (by decide : 1<2)]

public theorem residual_fixedCodim_of_natural_kernel
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* D) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (f : Additive U →ₗ[ZMod 2] (Fin 2 → F)) (hf : Function.Surjective f)
    (hk : f.ker = BinaryOffender.fixedSpace
      (NormalElementaryQuotient.representation U q hq hker) ((pResidual 2 G).map q)) :
    fixedCodim U (pResidual 2 G) = 2 * Module.finrank (ZMod 2) F := by
  rw [fixedCodim_eq_quotient_representation U q hq hker,
    BinaryOffender.fixedCodim,←hk]
  exact (f.quotKerEquivOfSurjective hf).finrank_eq.trans
    (by simp [Module.finrank_pi_fintype,two_mul])
end CFSG.Quasithin.ChapterB.RankOneBaumann
