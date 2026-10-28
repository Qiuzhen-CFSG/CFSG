module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.NaturalKernel
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.Orientation
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.SylowNormalizer.SourceAssembly

/-!
# Constructing the marked Sylow lift from the source cover

Both natural action kernels are proved in `NaturalKernel`. The centre plane
is put in the first natural coordinate slot by an actual simultaneous change
of actor and vector coordinates. All local-cover and residual hypotheses of
the Sylow producer are then discharged. Only its three explicitly intrinsic
calculations remain: the cover centralizer bound and the graph and field
coset recognition, all in the same projective marking.
Source: Aschbacher--Smith, proof of 15.3.38, printed p.1136.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel SylowNormalizer
variable {G : Type*} [Group G] [Finite G]

/-- These are the intrinsic calculations retained by the conditional task,
not the Sylow normalizer, a section, or a fusion assertion. The source owner
must supply them for the constructed cover and the literal natural action. -/
structure SylowCalculations (d : CharacteristicTwo.LocalData G) (I L : Subgroup G)
    (r : LocalResult d I L) : Prop where
  centralizer_bound : ∀ X : Sylow 3 d.Y,
    (d.S ⊓ L) ⊓ centralizer (((X : Subgroup d.Y).map d.Y.subtype) : Set G) ≤ r.cover.borel.W₁
  graph : ∀ (a : NaturalOrthogonalAction d.M d.V) (hYSM : d.Y ⊔ d.S ≤ d.M),
    a.plane 1 = r.cover.borel.W₁ →
    ∀ c : NaturalCoordinates d.T d.M d.Y d.S (d.Y.pCoreIn 2) d.V r.cover.borel.W₁
      a d.sylow_le hYSM,
    ∀ t : d.T, c.tProjection t = .sr 0 → r.marking.Graph (t : G)
  field : ∀ (a : NaturalOrthogonalAction d.M d.V) (hYSM : d.Y ⊔ d.S ≤ d.M),
    a.plane 1 = r.cover.borel.W₁ →
    ∀ c : NaturalCoordinates d.T d.M d.Y d.S (d.Y.pCoreIn 2) d.V r.cover.borel.W₁
      a d.sylow_le hYSM,
    ∀ t : d.T, c.tProjection t = .r 2 → r.marking.Field (t : G)

/-- Constructed Sylow output, retaining the literal factor intersections. -/
structure SylowResult (d : CharacteristicTwo.LocalData G) (I L : Subgroup G)
    (r : LocalResult d I L) where
  lift : SylowThreeLift d.T d.Y d.S L r.marking
  centralizer_trivial : (d.S ⊓ L) ⊓ centralizer
    (((lift.X : Subgroup d.Y).map d.Y.subtype) : Set G) = ⊥
  normalizer_S : d.S ⊓ normalizer (((lift.X : Subgroup d.Y).map d.Y.subtype) : Set G) =
    zpowers (lift.dihedral.firstReflection : G) ⊔ zpowers (lift.dihedral.halfTurn : G)
  fixes : (lift.dihedral.firstReflection * lift.dihedral.halfTurn : G) ∈
    centralizer (r.cover.borel.W₁ : Set G)
  outside : (lift.dihedral.firstReflection * lift.dihedral.halfTurn : G) ∉ r.cover.borel.W₁
  factors : let P := (lift.X : Subgroup d.Y).map d.Y.subtype
    ∃ f : ((P ⊓ componentPart d.Yplus L : Subgroup G) ×
      (P ⊓ planeResidual d.M d.Y r.cover.borel.W₂ : Subgroup G)) ≃* P,
      ∀ z, (f z : G) = (z.1 : G) * (z.2 : G)

/-- All ambient geometry and Frattini premises are proved before constructing
the lift. The projective quotient is unchanged by the natural-plane relabelling. -/
theorem sylow_result {d : CharacteristicTwo.LocalData G} (s : SourceInputs d)
    {I L : Subgroup G} (h : Setup d I L) (r : LocalResult d I L)
    (m : SylowCalculations d I L r) : Nonempty (SylowResult d I L r) := by
  obtain ⟨i, hi⟩ := r.plane
  obtain ⟨a, ha, hS⟩ := exists_oriented_action d i
  have hplane : a.plane 1 = r.cover.borel.W₁ := ha.trans hi.symm
  have hYM : d.Y ≤ d.M := Chapter14.SourcePreliminaries.sourceResidual_le _ _
  have hSM : d.S ≤ d.M := inf_le_left.trans d.sylow_le
  have hMY : d.M ≤ normalizer (d.Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal _ _)
  have hYSM : d.Y ⊔ d.S ≤ d.M := sup_le hYM hSM
  have hV : d.V = r.cover.borel.W₁ ⊔ r.cover.borel.W₂ := by
    rcases r.cover.borel.planes with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂]
    · exact (RankTwo.natural_planes_sup d.action (by decide)).symm
    · exact (RankTwo.natural_planes_sup d.action (by decide)).symm
  obtain ⟨e⟩ := ComponentIntersection.quotient_equiv_elementaryNine_of_card r.cover.quotient_card
    (by
      change Monoid.exponent (d.Y ⧸ pCore 2 d.Y) ∣ 3
      rw [← r.cover.plus]
      exact s.earlier.quotient_exponent)
  obtain ⟨z, hz, hzdiag⟩ := r.cover.opposite_diagonal
  obtain ⟨b, hC, hN, hfix, hout, hprod⟩ := exists_lift_of_local_cover
    d.T d.M I d.Y d.Yplus d.S L (componentPart d.Yplus L)
    (planeResidual d.M d.Y r.cover.borel.W₂) d.V r.cover.borel.W₁ r.cover.borel.W₂
    a d.sylow_le hYSM inf_le_left (module_le_sylow d) hMY
    (s.earlier.sylow I h.outside) r.cover.plus r.marking r.cover.center_core
    r.cover.center_plane r.cover.overgroup_centralizer r.product r.cover.residual_core.symm
    e (natural_kernel_T s h r) (natural_kernel_YS s h r) hplane.symm hV hS
    z hz hzdiag r.cover.residual_product
    (r.cover.borel.component_core.trans r.cover.residual_core.symm)
    (r.cover.opposite_core.trans r.cover.residual_core.symm) r.cover.borel.component_centralizes
    ((planeResidual_le _ _ _).trans (inf_le_right.trans inf_le_right)) m.centralizer_bound
    (m.graph a hYSM hplane) (m.field a hYSM hplane)
  exact ⟨⟨b, hC, hN, hfix, hout, hprod⟩⟩

omit [Finite G] in
/-- The rotation preimage is literally ⟨w,S_L⟩ in G. The source Sylow
condition identifies T∩L with S∩L, so the dihedral kernel is the required one. -/
theorem SylowResult.transfer_subgroup {d : CharacteristicTwo.LocalData G} (s : SourceInputs d)
    {I L : Subgroup G} (h : Setup d I L) {r : LocalResult d I L} (b : SylowResult d I L r) :
    b.lift.dihedral.transferSubgroup.map (d.T : Subgroup G).subtype =
      zpowers (b.lift.dihedral.rotation : G) ⊔ (d.S ⊓ L) := by
  obtain ⟨P, hP⟩ := s.earlier.sylow I h.outside
  have hTI : (d.T : Subgroup G) ⊓ I = d.S := by
    rw [← hP]
    exact inf_eq_sylow_map P d.T.isPGroup' (hP ▸ (show d.S ≤ d.T from inf_le_left))
  have hTL : L ⊓ (d.T : Subgroup G) = d.S ⊓ L := by
    apply le_antisymm
    · exact le_inf ((le_inf inf_le_right (inf_le_left.trans h.component_le)).trans hTI.le) inf_le_left
    · exact le_inf inf_le_right (inf_le_left.trans inf_le_left)
  rw [b.lift.dihedral.transferSubgroup_eq, Subgroup.map_sup, MonoidHom.map_zpowers,
    subgroupOf_map_subtype, hTL]
  rfl

omit [Finite G] in
/-- The constructed subgroup has index two and an actual cyclic-four quotient
with exactly S_L as kernel. Its distinguished field involution maps to two. -/
theorem SylowResult.transfer_data {d : CharacteristicTwo.LocalData G} (s : SourceInputs d)
    {I L : Subgroup G} (h : Setup d I L) {r : LocalResult d I L} (b : SylowResult d I L r) :
    ∃ W : Subgroup d.T,
      W.map (d.T : Subgroup G).subtype = zpowers (b.lift.dihedral.rotation : G) ⊔ (d.S ⊓ L) ∧
      W.index = 2 ∧ ∃ q : W →* Multiplicative (ZMod 4),
        Function.Surjective q ∧ q.ker = (L.subgroupOf (d.T : Subgroup G)).subgroupOf W ∧
        Nonempty ((W ⧸ q.ker) ≃* Multiplicative (ZMod 4)) ∧
        ∃ fW : W, (fW : d.T) = b.lift.dihedral.halfTurn ∧
          q fW = Multiplicative.ofAdd (2 : ZMod 4) := by
  let c := b.lift.dihedral
  exact ⟨c.transferSubgroup, b.transfer_subgroup s h, c.transferSubgroup_index,
    c.cyclicQuotient, c.cyclicQuotient_surjective, c.cyclicQuotient_ker_eq,
    ⟨c.quotientEquiv⟩, c.halfTurnInTransfer, c.halfTurnInTransfer_coe, c.cyclicQuotient_halfTurn⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
