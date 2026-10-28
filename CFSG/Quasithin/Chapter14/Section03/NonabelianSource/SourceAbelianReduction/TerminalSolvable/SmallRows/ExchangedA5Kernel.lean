module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.Preparation
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelQuotientDefs
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.NumericalGeometry

/-!
# Quotients of the actual terminal component span

Once original 14.3.12 supplies the two-core kernel of the terminal action,
restriction to the relatively normal component span identifies its intrinsic
two-core quotient with its dotted image. For an arbitrary subgroup of the
point normalizer, its two-core quotient is a quotient of its dotted image;
this gives the order bound needed on the span joined with the original Sylow.
The latter group need not be normal in the point normalizer.

Source: Aschbacher--Smith 14.3.12 and the paired branch of 14.3.15,
printed pp.993--994. Recognition of the small-actor branch remains separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {V : Subgroup G} (F : InvariantFlag T V 2)

/-- Relative normality is sufficient for the exact restricted kernel. -/
theorem terminal_normal_subgroup_kernel {J : Subgroup G} (hJH : J ≤ F.H)
    (hJ : (J.subgroupOf F.H).Normal)
    (hk : F.terminalHatAction.ker = pCore 2 F.H) :
    (componentDotMap F hJH).ker = pCore 2 J := by
  have hr : ((QuotientGroup.mk' F.terminalHatAction.ker).subgroupMap
      (J.subgroupOf F.H)).ker = pCore 2 (J.subgroupOf F.H) := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk', hk]
    exact (pCore_subnormal_eq_comap 2 hJ.isSubnormal).symm
  have he := MonoidHom.ker_comp_mulEquiv
    ((QuotientGroup.mk' F.terminalHatAction.ker).subgroupMap (J.subgroupOf F.H))
    (subgroupOfEquivOfLe hJH).symm
  rw [hr] at he
  exact he.trans (pCore_map_iso 2 (subgroupOfEquivOfLe hJH))

/-- Even without relative normality, the quotient order is bounded by the
literal dotted image. The proof does not identify the two kernels. -/
theorem terminal_subgroup_core_quotient_card_le {J : Subgroup G} (hJH : J ≤ F.H)
    (hk : F.terminalHatAction.ker = pCore 2 F.H) :
    Nat.card (J ⧸ pCore 2 J) ≤ Nat.card (F.terminalDot J) := by
  let f := componentDotMap F hJH
  have hp : IsPGroup 2 f.ker := by
    have he : f.ker = (F.terminalHatAction.ker).comap (inclusion hJH) := by
      ext j
      change (componentDotMap F hJH j = 1) ↔ _
      rw [← Subtype.val_inj]
      change QuotientGroup.mk' F.terminalHatAction.ker (inclusion hJH j) = 1 ↔
        inclusion hJH j ∈ F.terminalHatAction.ker
      exact QuotientGroup.eq_one_iff _
    rw [he, hk]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hJH)
  have hle : f.ker ≤ pCore 2 J := le_sSup ⟨inferInstance, hp⟩
  let q := QuotientGroup.map f.ker (pCore 2 J) (MonoidHom.id J) hle
  have hq : Function.Surjective q := QuotientGroup.map_surjective_of_surjective
    f.ker (pCore 2 J) (MonoidHom.id J) (QuotientGroup.mk'_surjective (pCore 2 J)) hle
  have hc := Nat.card_le_card_of_surjective q hq
  rwa [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
    (componentDotMap_surjective F hJH)).toEquiv] at hc

/-- The exact normal span is used here, rather than its join with T. -/
def ComponentLift.spanCoreQuotientEquiv {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (hk : F.terminalHatAction.ker = pCore 2 F.H) :
    (conjugateSpanBy K (T : Subgroup G) ⧸
      pCore 2 (conjugateSpanBy K (T : Subgroup G))) ≃*
        F.terminalDot (conjugateSpanBy K (T : Subgroup G)) :=
  componentCoreQuotientEquivDot F
    (conjugateSpanBy_le hK.le_pointNormalizer ((F.invariant 1).trans F.H.le_normalizer))
    (terminal_normal_subgroup_kernel F _ hK.normal_span hk)

theorem ComponentLift.spanCoreQuotientEquiv_apply {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (hk : F.terminalHatAction.ker = pCore 2 F.H)
    (k : conjugateSpanBy K (T : Subgroup G)) :
    (hK.spanCoreQuotientEquiv F hk (QuotientGroup.mk' (pCore 2 _) k) : F.TerminalHdot) =
      QuotientGroup.mk' F.terminalHatAction.ker
        ⟨k, conjugateSpanBy_le hK.le_pointNormalizer
          ((F.invariant 1).trans F.H.le_normalizer) k.property⟩ := by
  rfl

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
