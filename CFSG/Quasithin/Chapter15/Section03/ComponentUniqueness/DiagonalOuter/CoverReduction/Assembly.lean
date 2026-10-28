module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.Sylow
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.Geometry

/-!
# Central-cover and transfer geometry in the diagonal branch

The source inputs first select the marked diagonal branch and force n=2.
The local producer identifies both centralizers and the centre plane. The
outer-order comparison identifies the natural action kernels, so compatible
plane coordinates give the genuine Sylow-three normalizer and its dihedral
section. Reapplication to the actual larger component proves I=N_G(V₁).
The representative and ordinary graph-centralizer component then supply all
ambient geometric inputs to the published transfer reduction.

The only additional inputs are the explicitly listed intrinsic cover
calculations and the precise earlier embedding and balance theorems. They
remain with the source-theorem owner: this conditional cover-reduction task
does not assert the final 15.3.38 contradiction. In particular no TI, fusion,
nonfusion, normalizer equality, or ordinary graph component is assumed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
15.3.38, printed pp.1135--1137. The cyclic quotient is the literal quotient
of the constructed rotation preimage by its specified kernel in T.
-/

@[expose] public section
open Subgroup Theory.GroupTheory CFSG.Quasithin.ChapterI.Section06To08
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open Chapter1 LocalCover LocalCover.SourceBorel GlobalGeometry
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The two intrinsic fixed-subgroup calculations used by the global geometry.
The odd core is in I, not in the unknown ambient graph centralizer. -/
structure FixedCalculations (d : CharacteristicTwo.LocalData G) (I L : Subgroup G)
    (r : LocalResult d I L) (b : SylowResult d I L r) where
  odd_core : pPrimeCore 2 ↥(I ⊓ centralizer
    ({(b.lift.dihedral.firstReflection : G) * (b.lift.dihedral.halfTurn : G)} : Set G)) ≃*
      Multiplicative (Fin 2 → ZMod 3)
  graph_residual : graphResidualIn L (b.lift.dihedral.firstReflection : G) ≃* PSL(2,r.marking.F)

/-- Output of the complete conditional geometric reduction. Its two witness
fields are constructed by `cover_reduction`, with the same matrix marking. -/
structure Reduction (d : CharacteristicTwo.LocalData G) (I L : Subgroup G) where
  coverData : LocalResult d I L
  sylow : SylowResult d I L coverData
  normalizer_eq : I = normalizer (coverData.cover.borel.W₁ : Set G)
  representative : RepresentativeGeometry coverData.cover.borel.W₁ d.ZS d.S I
  component : Subgroup (centralizer ({(sylow.lift.dihedral.firstReflection : G)} : Set G))
  isComponent : IsComponent (centralizer ({(sylow.lift.dihedral.firstReflection : G)} : Set G)) component
  normalizes : I ≤ normalizer (L : Set G)
  action : centralizer (coverData.cover.borel.W₁ : Set G) ≤ normalizer (L : Set G)
  kernel : centralizer (coverData.cover.borel.W₁ : Set G) ⊓ centralizer (L : Set G) ≤ coverData.cover.borel.W₁

/-- Assemble the requested reduction from the genuine rank-two setup and the
uniform earlier source conclusions. The five local model calculations are
explicit, and neither a Sylow lift nor any global geometry is an input. -/
theorem cover_reduction {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (embeddings : EarlierEmbeddings κ) (rankBalance : EarlierRankTwoBalance κ)
    (balance : EarlierBalance κ) {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (hZS : Nat.card d.ZS = 4)
    (hfixedSylow : ∀ i : OrthogonalPlaneIndex, IsSylowIn 2 d.S
      (centralizer (fixedPlane (d.action.plane i) d.S : Set G)))
    (hm : (PerfectCentralCovering.universalProjection Sporadic.Mathieu.M23).ker = ⊥)
    (sylowModels : ∀ r : LocalResult d I L, SylowCalculations d I L r)
    (fixedModels : ∀ (r : LocalResult d I L) (b : SylowResult d I L r),
      Nonempty (FixedCalculations d I L r b)) : Nonempty (Reduction d I L) := by
  obtain ⟨r⟩ := local_result s h
  obtain ⟨b⟩ := sylow_result s h r (sylowModels r)
  obtain ⟨m⟩ := fixedModels r b
  obtain ⟨hI, ⟨v⟩, K, hK⟩ := geometry_of_lift hG embeddings rankBalance balance s h r b.lift
    hZS hfixedSylow hm b.fixes m.odd_core m.graph_residual
  obtain ⟨ha, hk⟩ := normalizer_action_and_kernel r.cover.borel.W₁ I L hI
    (h.normalizes_component s.earlier) r.cover.overgroup_centralizer
  exact ⟨⟨r, b, hI, v, K, hK, h.normalizes_component s.earlier, ha, hk⟩⟩

/-- An actual consumer in the published transfer reduction, using the same
reflection, half-turn, representative and cyclic quotient as the construction.
The remaining hypotheses are exactly the local involution calculations and
the characteristic-two centralizer of z used by that reduction. -/
theorem Reduction.field_fusion {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (r : Reduction d I L) (hperfect : IsPPerfect 2 G)
    (F : Subgroup G) (z : G)
    (hF : IsPPerfect 2 F)
    (hsmall : ¬ 4 ∣ Nat.card (((centralizer (F : Set G)).subgroupOf
      (normalizer (L : Set G))).map L.normalizerMonoidHom))
    (hfixedF : (r.sylow.lift.dihedral.firstReflection : G) *
      (r.sylow.lift.dihedral.halfTurn : G) ∈ centralizer (F : Set G))
    (hz : generalizedFitting (centralizer ({z} : Set G)) =
      pCore 2 (centralizer ({z} : Set G)))
    (hinside : ∀ x : G, x ∈ L → orderOf x = 2 →
      IsConj x r.representative.v ∨ IsConj x z)
    (hcoset : ∀ x : G, orderOf x = 2 → x * (r.sylow.lift.dihedral.halfTurn : G)⁻¹ ∈ L →
      IsConj x (r.sylow.lift.dihedral.halfTurn : G)) :
    IsTISubgroup r.coverData.cover.borel.W₁ ∧
      IsConj (r.sylow.lift.dihedral.firstReflection : G) (r.sylow.lift.dihedral.halfTurn : G) ∧
      IsConj ((r.sylow.lift.dihedral.firstReflection : G) * (r.sylow.lift.dihedral.halfTurn : G))
        (r.sylow.lift.dihedral.halfTurn : G) := by
  obtain ⟨i, hi⟩ := r.coverData.plane
  let V := r.coverData.cover.borel.W₁
  have hV : V = d.action.plane i := hi
  let : IsElementaryAbelian 2 V := d.action.elementary_of_le (hV ▸ d.action.plane_le i)
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hV, d.action.card_plane]; decide)
  let : IsKleinFour V := ⟨hV ▸ d.action.card_plane i, IsElementaryAbelian.exponent_eq_prime⟩
  have hv : r.representative.v ∈ V := (r.representative.generator ▸ mem_zpowers _).2
  exact field_fusion_of_split_cover_geometry d.T hperfect V I L F r.representative.actor
    r.sylow.lift.dihedral r.normalizer_eq r.normalizes r.coverData.cover.overgroup_centralizer
    r.representative.v z hv r.representative.ne_one r.representative.centralizer_le
    r.representative.actor_le r.representative.transitive hF hsmall
    r.sylow.outside r.sylow.fixes hfixedF r.component r.isComponent hz hinside hcoset

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
