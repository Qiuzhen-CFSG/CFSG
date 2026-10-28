module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner.ActorCalculation.Interface
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner.ActorCalculation.InnerPlacement
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner.ActorCalculation.Alignment
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.TranslationCommutator

/-!
# Transporting the marked normalizer residual in 15.3.59

The marked four-group lies in the actual inner actors: outer actors have at
most eight fixed vectors, while marked translations have at least sixteen.
Its intrinsic displacement intersection recovers the marked line, placing
the four-group and the full normalizer H ∩ N_G(V₀) simultaneously in the
concrete point parabolic.

The embedded two-residual commutes with the literal actor projection. The
cubic action on the point radical therefore gives the actor commutator
identity, with the inner placement and parabolic alignment discharged from
the separate recognized and marked coordinates. No normalization of X is
assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.56–59, printed pp.1147–1150.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian

variable {G : Type*} [Group G] [Finite G]

/-- The embedded two-residual commutes with the literal actor projection,
with all normality relative to the defining normalizer. -/
theorem actorImage_normalizerResidual (Z V₀ : Subgroup G) :
    actorImage Z (normalizerResidual Z V₀) =
      (pResidual 2 (actorImage Z (markedNormalizer Z V₀))).map
        (actorImage Z (markedNormalizer Z V₀)).subtype := by
  have hNH : markedNormalizer Z V₀ ≤ centralizerH Z := inf_le_left
  have hRH : normalizerResidual Z V₀ ≤ centralizerH Z :=
    (map_subtype_le _).trans hNH
  have he : (normalizerResidual Z V₀).subgroupOf (centralizerH Z) =
      (pResidual 2 ((markedNormalizer Z V₀).subgroupOf (centralizerH Z))).map
        ((markedNormalizer Z V₀).subgroupOf (centralizerH Z)).subtype := by
    apply map_injective (centralizerH Z).subtype_injective
    rw [map_subgroupOf_eq_of_le hRH, map_embedded_pResidual,
      map_subgroupOf_eq_of_le hNH]
    rfl
  unfold actorImage
  rw [he, map_embedded_pResidual]

variable {T Z ZS V : Subgroup G} {t : G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- Simultaneous parabolic placement suffices for the source actor identity.
The final theorem below supplies this placement from the independent markings. -/
theorem actor_commutator_of_parabolicAlignment
    (d : RecognizedAction T Z ZS V t) (V₀ : Subgroup G) (y : G)
    (halign : ParabolicAlignment d V₀ y) :
    actorImage Z (partnerX Z ZS y) =
      ⁅actorImage Z (partnerX Z ZS y), actorImage Z (normalizerResidual Z V₀)⁆ := by
  obtain ⟨α, hX, hN⟩ := halign
  apply map_injective (f := (actorRelabel d α).toMonoidHom) (actorRelabel d α).injective
  rw [map_commutator, hX, actorImage_normalizerResidual, map_embedded_pResidual, hN]
  have hm := congrArg (fun A : Subgroup Matrix.PSL3Two.SL => A.map MulAut.conj)
    Matrix.PSL3Two.MarkedAutomorphisms.pointV_eq_commutator_residual
  rw [map_commutator] at hm
  simpa only [Matrix.PSL3Two.MarkedAutomorphisms.residual,
    map_embedded_pResidual] using hm

/-- The marked partner actor image is its commutator with the actor image of
the embedded two-residual of the literal H ∩ N_G(V₀). The recognized and marked
coordinates remain independent; both inner placement and parabolic alignment
are consequences of these inputs. -/
theorem marked_actor_commutator
    (d : RecognizedAction T Z ZS V t)
    {V₀ : Subgroup G} {y : G} (hXH : partnerX Z ZS y ≤ centralizerH Z)
    (m : MarkedAction Z ZS V₀ y t hXH)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hZV : Z ≤ V₀) (hVU : V₀ ≤ closureU Z ZS) :
    actorImage Z (partnerX Z ZS y) =
      ⁅actorImage Z (partnerX Z ZS y), actorImage Z (normalizerResidual Z V₀)⁆ :=
  actor_commutator_of_parabolicAlignment d V₀ y
    (parabolicAlignment_of_inner d m hkernel hZV hVU
      (marked_actorImage_le_inner d hXH m hkernel))

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner
