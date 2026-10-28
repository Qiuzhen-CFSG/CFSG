module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Linear
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Faithfulness
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Recognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Lift

/-!
# The initial natural section from the triple-commutator bound

The actual elementary radius head has a faithful SL₃(2) action and a
nonidentity involution whose displacement has order at most two. Binary
small-involution recognition splits this head into its intrinsic fixed and
moving subgroups, with equivariant natural coordinates on the moving part.

The quotient correspondence lifts the splitting and coordinates to the full
NaturalSectionAt contract. Normality is relative to the finite stabilizer,
and its actual surjective projection has kernel Q. The ambient triple bound
remains an explicit input for the parent source-theorem assembly to discharge.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.1)(iii), pp.882--883;
the cited representation arguments are (1.4)--(1.5), pp.842--843.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Splitting

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The complete initial natural section, conditional only on the authorized
ambient triple bound in addition to the original contrary configuration. -/
theorem naturalSectionAt_of_triple (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (p : Counterexample geometry)
    (hfour : Nat.card (radiusCommutator p.a p.a') = 4)
    (htriple : ⁅⁅V R p.a, Q R p.a⁆, Ltilde R p.a⁆ ≤ Z R p.a) :
    Nonempty (NaturalSectionAt p.a (V R p.a) (Z R p.a)) := by
  let := geometry.Z_normal p.a
  let := radiusHead_elementary source geometry hb modules p.a p.color_a
  obtain ⟨s⟩ := naturalActionSplitting_of_small_involution
    (radiusHeadAction source geometry p.a p.color_a)
    (radiusHeadAction_injective source geometry hb modules p hfour htriple)
    (radiusHead_small_involution source geometry hb modules p)
  obtain ⟨localSection⟩ := singleNaturalSection_of_head_splitting
    (localRadius p.a) (localZ p.a) (localKernel p.a)
    (pResidual 2 (stabilizer R p.a))
    (localProjection source p.a p.color_a)
    (localProjection_surjective source p.a p.color_a)
    (localProjection_kernel source p.a p.color_a)
    (fun _ hx => Z_le_VBall R p.a 2 hx)
    (elementary_radius_quotient source geometry hb modules p.a p.color_a)
    (local_triple geometry hb p.a p.color_a htriple) s
  exact ⟨{
    local_group := (geometry.V_le_Q hb p.a p.color_a).trans (fun _ hx => hx.1)
    kernel_le := Z_le_VBall R p.a 2
    projection := localProjection source p.a p.color_a
    module_section := localSection }⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Splitting
