module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointBounded
public import Theory.GroupTheory.SylowFixedNormalActorSplitting
public import Theory.Representation.NormalElementaryQuotient.SubgroupSpaceTransport
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# Excluding the hyperplane alternative on the original point span

The complementary point is fixed by the common Baumann Sylow subgroup.
Apply Sylow averaging to the preimage of the normal offender subgroup.
Normality propagates the seed splitting to the full point span W, giving
W = [W,K] C_W(K). Literal commutator and fixed-space coordinates identify
this with the sum of moved and fixed spaces for the restricted offender
action. Its quotient therefore has dimension zero, contradicting the
codimension-one clause of B.5.6(5).

SourceAssembly/PointOffender applies this exclusion after each Sylow rechoice,
retaining the multiple-overgroup guard and every corrected F.6 alternative.
Source: Aschbacher--Smith B.2.14, B.5.6(5) and 13.2.12, printed pp.78,105,882.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Stellmacher Section06.CentralizerReduction Section06.CentralizerReduction.A5Module
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- Sylow averaging on the original complementary-point span excludes the
codimension-one clause of the corrected B.5 hyperplane alternative. -/
theorem point_offender_not_hyperplane
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {J : Subgroup G} (hBJ : ChapterB.baumann (T : Subgroup G) ≤ J)
    (hJv : J ≤ Gv (markedV d.flag.flag.module))
    (x : J) (hx : (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module)
    (hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤)) :
    letI := hr.normal
    letI := hr.elementary
    let W := conjugateSpanBy (zpowers x) ⊤
    let ρ := ChapterB.InternalThompsonAction.action W
    ¬ Nonempty (ChapterB.SourceInduction.HyperplaneCase
      (ρ.comp (offenderSubgroup ρ).subtype)) := by
  let := hr.normal
  let := hr.elementary
  intro W ρ ⟨c⟩
  let f := QuotientGroup.mk' (centralizer (W : Set J))
  let N := offenderSubgroup ρ
  let : N.Normal := offenderSubgroup_normal ρ
  let K := N.comap f
  obtain ⟨P,hP⟩ := (point_baumann_sylow d hH hB hZ hs hz).restrict hBJ hJv
  have hc : x ∈ centralizer (P : Set J) := by
    intro t ht
    apply Subtype.ext
    change (t:G)*(x:G) = (x:G)*(t:G)
    rw [hx]
    exact mem_centralizer_iff.mp (complement_centralizes_baumann d hH hB hZ hs hz)
      t (hP ▸ mem_map_of_mem J.subtype ht)
  have hsplit := conjugateSpan_split_normal_actor P (zpowers x) W K rfl (zpowers_le.mpr hc)
  have hWtop : NormalElementaryQuotient.subgroupSpace W W = ⊤ := by
    ext v
    exact iff_of_true v.toMul.property Submodule.mem_top
  have hsplit' : subspaceCommutator ρ ⊤ N ⊔ fixedSpace ρ N = ⊤ := by
    apply top_unique
    have hh := congrArg (NormalElementaryQuotient.subgroupSpace W) hsplit
    rw [hWtop,NormalElementaryQuotient.subgroupSpace_sup W (commutator_le_left W K) inf_le_left] at hh
    apply hh.le.trans
    apply sup_le_sup
    · change NormalElementaryQuotient.commutatorSpace W K ≤ _
      rw [NormalElementaryQuotient.commutatorSpace_eq W f (QuotientGroup.mk'_surjective _)
        (QuotientGroup.ker_mk' _),map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
      exact le_rfl
    · have hh := NormalElementaryQuotient.subgroupSpace_fixed_of_centralizes W f
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
        (W ⊓ centralizer (K : Set J)) K (le_centralizer_iff.mp inf_le_right)
      rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hh
  have he : subspaceCommutator (ρ.comp N.subtype) ⊤ ⊤ ⊔ Representation.invariants (ρ.comp N.subtype) = ⊤ := by
    change subspaceCommutator (ρ.comp N.subtype) ⊤ ⊤ ⊔ fixedSpace ρ N = ⊤
    rw [subspaceCommutator_comp_map,←MonoidHom.range_eq_map,range_subtype]
    exact hsplit'
  have hh := c.hyperplane
  change Module.finrank (ZMod 2) (Additive W ⧸
    (subspaceCommutator (ρ.comp N.subtype) ⊤ ⊤ ⊔ Representation.invariants (ρ.comp N.subtype))) = 1 at hh
  rw [he] at hh
  have hzero : Module.finrank (ZMod 2) (Additive W ⧸ (⊤ : Submodule (ZMod 2) (Additive W))) = 0 :=
    Module.finrank_zero_of_subsingleton
  omega
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
