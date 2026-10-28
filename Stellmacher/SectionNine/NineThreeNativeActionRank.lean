module
public import Stellmacher.SectionNine.NineThreeCanonicalActionRank
public import Stellmacher.SectionFiveToSeven.SixFourNativeBaumannFixed

/-!
# Native-action wrapper for the canonical rank data

Preserve the original native-action rank-data theorem. The injective graph
embedding takes native nontriviality to the actual Section Six module; the
native Baumann bridge gives nontrivial canonical barred oneJ. The canonical
rank theorem then supplies the unchanged record, including center sixteen,
two factors, and all exact action inputs. This wrapper makes no converse
identification of native and global offenders.

Source: Stellmacher (9.3), Journal of Algebra 190 (1997), p.50,
`refs/files/stellmacher-n-group.pdf`. The canonical owner also handles the
separate quadratic-offender route when native nontriviality is unavailable.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_native_action_rank_data
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (hJnative : ¬ elementaryAbelianMaxJ T ≤
      Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G)) :
    NineThreeNativeActionRankData ctx := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.hypothesisTwo
  have hGa : (GAt Γ cp.a).map embedding = P1 := (nine_two_ambient_setup ctx).2.1
  have hZa : (ZAt Γ cp.a).map embedding = sectionSixV S P1 :=
    nine_two_center_eq_sectionSixV ctx hGa
  have hJambient : ¬ elementaryAbelianMaxJ S ≤
      Subgroup.centralizer (sectionSixV S P1 : Set H) := by
    intro hc
    apply hJnative
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    apply ctx.embedding_injective
    have hjm : embedding j ∈ elementaryAbelianMaxJ S := by
      rw [← ctx.map_S,elementaryAbelianMaxJ_map_injective embedding ctx.embedding_injective]
      exact Subgroup.mem_map_of_mem embedding hj
    have hvm : embedding v ∈ sectionSixV S P1 := hZa ▸ Subgroup.mem_map_of_mem embedding hv
    simpa only [map_mul] using Subgroup.mem_centralizer_iff.mp (hc hjm) (embedding v) hvm
  have hJ := (sixFour_native_baumann_barred_fixed h hJambient).1
  exact nine_three_canonical_action_rank_data ctx hb hlarge first second config hJ

end Stellmacher.SectionNine
