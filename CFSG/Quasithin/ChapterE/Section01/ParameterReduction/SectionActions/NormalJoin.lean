module
public import Theory.GroupTheory.SimpleSectionAction.PerfectLift
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.SectionActions.Component

/-!
# Normal-product transport using perfect section presentations

The YT step of E.1.11 can use a weaker factor hypothesis: test genuine simple
sections with perfect upper endpoint. Such endpoints lie in Y, because YT/Y
is a two-group. Their subnormality therefore extends through Y to G, while
both endpoints and their literal T-actions remain unchanged.

This is a source-sufficient alternative induction interface, not a claim that
intersecting arbitrary endpoints with Y preserves their stabilizer. The original
`NonabelianSectionActionBound` implies `PerfectSectionActionBound`; the latter
passes both to YT and to quotients. Every nonabelian simple composition-factor
carrier has a perfect presentation (`exists_perfect_presentation`). The source's
nonabelian chief branch uses a simple component, which is perfect, so the new
hypothesis supplies its exact core-action extension. Cyclic factors continue to
use `simpleSection_commutative_splitExtension_isEGenerated_one` independently.

Thus an induction proving E.1.11 from this weaker hypothesis retains the original
public conclusion and assumptions. This module proves the transports and their
component consumer, not the generation induction or its diagonal branches.
The companion `NormalJoin.ChiefOrbit` connects it to that branch's existing API.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.11, printed pp.212--214, especially the YT reduction on p.212 and the
simple component J with S=N_T(J) on p.213 (manuscript of 1 March 2004).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE
universe u
variable {G : Type u} [Group G]

/-- The composition-section hypothesis restricted to perfect upper endpoints.
This weaker induction hypothesis suffices for the source's simple-component
branch; it does not assert inheritance for arbitrary section stabilizers. -/
def PerfectSectionActionBound (i : ℕ) (T : Subgroup G) : Prop :=
  ∀ (L : Type u) [Group L] [Finite L] (s : ChiefFactor.SimpleSection G L),
    Group.IsPerfect s.subgroup → ¬ IsMulCommutative L → IsEGenerated i (s.extension T)

theorem NonabelianSectionActionBound.perfectSections {i : ℕ} {T : Subgroup G}
    (h : NonabelianSectionActionBound i T) : PerfectSectionActionBound i T :=
  fun L _ _ s _ hn => h L s hn

/-- Perfect sections lift through surjections with precisely the same action
extension; the preimage residual supplies the required perfect upper group. -/
theorem PerfectSectionActionBound.map_surjective [Finite G]
    {D : Type u} [Group D] {i : ℕ} {T : Subgroup G}
    (h : PerfectSectionActionBound i T) (f : G →* D) (hf : Function.Surjective f) :
    PerfectSectionActionBound i (T.map f) := by
  intro L _ _ s hp hn
  let := hp
  exact (h L (s.perfectLift f hf) inferInstance hn).map_equiv
    (MulEquiv.subgroupCongr (s.perfectLift_extension f hf T))

/-- The other E.1.11 induction step, on the literal quotient G/Y. -/
theorem PerfectSectionActionBound.quotient [Finite G] {i : ℕ} {T : Subgroup G}
    (h : PerfectSectionActionBound i T) (Y : Subgroup G) [Y.Normal] :
    PerfectSectionActionBound i (T.map (QuotientGroup.mk' Y)) :=
  h.map_surjective (QuotientGroup.mk' Y) (QuotientGroup.mk'_surjective Y)

private theorem subnormal_map_of_le_normal {H Y : Subgroup G} [Y.Normal]
    (hY : Y ≤ H) (U : Subgroup H) (hU : U.IsSubnormal)
    (hUY : U ≤ Y.subgroupOf H) : (U.map H.subtype).IsSubnormal := by
  have he : (U.comap (inclusion hY)).map Y.subtype = U.map H.subtype := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨inclusion hY y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hUY hy⟩, hy, rfl⟩
  rw [← he]
  exact (hU.comap _).trans' (inferInstance : Y.Normal).isSubnormal

/-- No endpoints are replaced: a section whose upper group lies in a normal
subgroup is embedded directly in the original ambient group. -/
theorem NonabelianSectionActionBound.section_of_upper_le_normal
    {i : ℕ} {T H Y : Subgroup G} [Y.Normal]
    (h : NonabelianSectionActionBound i T) (hT : T ≤ H) (hY : Y ≤ H)
    {L : Type u} [Group L] [Finite L] (s : ChiefFactor.SimpleSection H L)
    (hU : s.subgroup ≤ Y.subgroupOf H) (hn : ¬ IsMulCommutative L) :
    IsEGenerated i (s.extension (T.subgroupOf H)) := by
  have hs := subnormal_map_of_le_normal hY s.subgroup s.subnormal hU
  exact (h L (s.embed hs) hn).map_equiv
    (MulEquiv.subgroupCongr (s.embed_extension hs T hT))

/-- Perfect sections pass through any intermediate overgroup with solvable
quotient by the normal subgroup. This proves the normal-product induction
transport without changing either endpoint or enlarging its stabilizer. -/
theorem PerfectSectionActionBound.overgroup_of_solvable_quotient
    {i : ℕ} {T H Y : Subgroup G} [Y.Normal]
    (h : PerfectSectionActionBound i T) (hT : T ≤ H) (hY : Y ≤ H)
    [Group.IsSolvable (H ⧸ Y.subgroupOf H)] :
    PerfectSectionActionBound i (T.subgroupOf H) := by
  intro L _ _ s hp hn
  let := hp
  have hU := le_of_isPerfect_of_solvable_quotient s.subgroup (Y.subgroupOf H)
  have hs := subnormal_map_of_le_normal hY s.subgroup s.subnormal hU
  have hp' : Group.IsPerfect (s.embed hs).subgroup := Group.IsPerfect.map H.subtype
  exact (h L (s.embed hs) hp' hn).map_equiv
    (MulEquiv.subgroupCongr (s.embed_extension hs T hT))

/-- The quotient of a normal subgroup joined with a two-group is solvable. -/
theorem normalJoin_quotient_solvable [Finite G] (Y T : Subgroup G) [Y.Normal]
    (hT : IsPGroup 2 T) : Group.IsSolvable ((Y ⊔ T : Subgroup G) ⧸ Y.subgroupOf (Y ⊔ T)) := by
  have he : Y.subgroupOf (Y ⊔ T) ⊔ T.subgroupOf (Y ⊔ T) = ⊤ := by
    apply (map_injective (Y ⊔ T).subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
  let := (isPGroup_quotient_of_sup_eq_top (Y.subgroupOf (Y ⊔ T))
    (T.subgroupOf (Y ⊔ T)) hT.comap_subtype he).isNilpotent
  infer_instance

/-- The perfect-section hypothesis is preserved by YT, for the literal T in YT. -/
theorem PerfectSectionActionBound.normalJoin [Finite G] {i : ℕ} {T : Subgroup G}
    (h : PerfectSectionActionBound i T) (hT : IsPGroup 2 T)
    (Y : Subgroup G) [Y.Normal] :
    PerfectSectionActionBound i (T.subgroupOf (Y ⊔ T)) := by
  let := normalJoin_quotient_solvable Y T hT
  exact h.overgroup_of_solvable_quotient le_sup_right le_sup_left

/-- The original E.1.11 factor hypothesis supplies precisely the perfect-section
hypothesis needed for induction on YT. -/
theorem NonabelianSectionActionBound.normalJoin_perfectSections [Finite G]
    {i : ℕ} {T : Subgroup G} (h : NonabelianSectionActionBound i T)
    (hT : IsPGroup 2 T) (Y : Subgroup G) [Y.Normal] :
    PerfectSectionActionBound i (T.subgroupOf (Y ⊔ T)) :=
  h.perfectSections.normalJoin hT Y

/-- Specialization to the source's Sylow two-subgroup. -/
theorem NonabelianSectionActionBound.normalJoin_sylow [Finite G]
    {i : ℕ} (T : Sylow 2 G) (h : NonabelianSectionActionBound i (T : Subgroup G))
    (Y : Subgroup G) [Y.Normal] :
    PerfectSectionActionBound i ((T : Subgroup G).subgroupOf (Y ⊔ (T : Subgroup G))) :=
  h.normalJoin_perfectSections T.isPGroup' Y

/-- Perfect-section bounds supply the same literal core-action consumer. -/
theorem PerfectSectionActionBound.coreNormalizer [Finite G] {i : ℕ} {T : Subgroup G}
    (h : PerfectSectionActionBound i T) (hT : IsPGroup 2 T)
    (J : Subgroup G) (hJ : J.IsSubnormal) [Group.IsPerfect J]
    [IsSimpleGroup (J ⧸ pCore 2 J)] (hn : ¬ IsMulCommutative (J ⧸ pCore 2 J)) :
    IsEGenerated i (J ⊔ (T ⊓ normalizer J) : Subgroup G) := by
  let s := ChiefFactor.SimpleSection.coreSection 2 J hJ
  apply isEGenerated_join_of_pCoreJoinAction J (T ⊓ normalizer J) inf_le_right
    (hT.to_le inf_le_left) (s.center_eq_bot hn)
  have hg := h _ s (by exact inferInstanceAs (Group.IsPerfect J)) hn
  exact hg.map_equiv (MulEquiv.subgroupCongr
    (ChiefFactor.SimpleSection.coreSection_extension 2 J T hJ))

/-- The source's nonabelian chief-factor branch uses a genuine simple component,
whose perfectness discharges the restriction in the new induction hypothesis. -/
theorem PerfectSectionActionBound.simpleComponentNormalizer [Finite G]
    {i : ℕ} {T : Subgroup G} (h : PerfectSectionActionBound i T) (hT : IsPGroup 2 T)
    (J : Subgroup G) (hJ : Theory.GroupTheory.IsComponent G J) [IsSimpleGroup J] :
    IsEGenerated i (J ⊔ (T ⊓ normalizer J) : Subgroup G) := by
  let := (simpleComponentCoreEquiv J hJ).isSimpleGroup
  let : Group.IsPerfect J := hJ.2.toIsPerfect
  let : Group.IsPerfect (J ⧸ pCore 2 J) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  exact h.coreNormalizer hT J hJ.1 (Group.IsPerfect.not_isMulCommutative _)

/-- An actual induction consumer: after passing to YT and then to any normal
quotient, the original factor hypothesis supplies generation for the simple
component and the normalizer in the literal image of T. -/
theorem NonabelianSectionActionBound.normalJoin_quotient_simpleComponentNormalizer
    [Finite G] {i : ℕ} (T : Sylow 2 G)
    (h : NonabelianSectionActionBound i (T : Subgroup G))
    (Y : Subgroup G) [Y.Normal]
    (N : Subgroup (Y ⊔ (T : Subgroup G) : Subgroup G)) [N.Normal]
    (J : Subgroup ((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸ N))
    (hJ : Theory.GroupTheory.IsComponent _ J) [IsSimpleGroup J] :
    IsEGenerated i (J ⊔
      (((T : Subgroup G).subgroupOf (Y ⊔ (T : Subgroup G))).map (QuotientGroup.mk' N) ⊓
        normalizer J) : Subgroup ((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸ N)) := by
  exact ((h.normalJoin_sylow T Y).quotient N).simpleComponentNormalizer
    (T.isPGroup'.comap_subtype.map _) J hJ

end CFSG.Quasithin.ChapterE
