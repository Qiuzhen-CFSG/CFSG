module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.OrdinaryNormalizer
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.GraphComponent
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.PlaneAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.FixedLine
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.RepresentativeIdentification
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.SourceBorel.Reduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.SourceBorel.CyclicPlanes

/-!
# Global geometry from the marked local cover

The genuine rank-two setup and uniform earlier outside-family conclusions
allow the local cover reduction to be repeated in N_G(V₁). The larger
component remains outside M and is ordinary; perfectness proves that it
cannot contain the noncentral Y₊. Equality of the nested covers then proves
I=N_G(V₁).

The natural Sylow interchange and the earlier |Z_S|=4 give an order-two
fixed line in either definite plane. Its generator v admits the earlier
15.3.6(3) Sylow conclusion. Balance, verified local-family membership and
the actual A.3.12 embedding give a component envelope in C_G(v).
`RepresentativeIdentification` resolves its embedding, giving C_G(v)≤I.
The natural matrix action supplies the transitive subgroup of I.

Finally the representative geometry gives TI. Conjugation of τ to τf bounds
the odd core of C_G(τ) by E₉; the intrinsic PSL₂(4) residual centralizes that
odd core, so I.3.1(2) supplies an ordinary component.

This completes the conditional global-geometry helper. Inputs retained for
the cover-reduction owner are the earlier appendix and balance theorems,
15.3.6(3) and |Z_S|=4, the marked local-cover conclusions uniformly on
eligible outside overgroups, the Sylow lift, and the actual M₂₃ multiplier.
The noncentral Y₊ action, the action of τf on the cover's center, and the
intrinsic PSL₂(4) residual and local E₉ odd core are explicit local cover
calculations. No TI, transfer fusion, nonfusion, representative-centralizer
bound or global component is assumed. Full source 15.3.38 remains with the
cover-reduction assembly owner until all these inputs are discharged.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
proof of 15.3.38, printed pp.1136--1137; 15.3.6 and 15.3.8, p.1122;
I.3.1--2, pp.414--415; 1.2.4, p.505.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
open Chapter1 LocalCover.SourceBorel
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Both definite planes meet Z_S in a line. The interchange is constructed
from the specified Sylow subgroup and compatible natural action. -/
theorem source_fixed_line_card (d : CharacteristicTwo.LocalData G)
    (hZ : Nat.card d.ZS = 4) (i : OrthogonalPlaneIndex) :
    Nat.card (d.ZS ⊓ d.action.plane i : Subgroup G) = 2 := by
  obtain ⟨t, ht, hS, h₁, h₂⟩ := cyclic_sylow_interchange d
  have hV : d.V.map (MulAut.conj t).toMonoidHom = d.V :=
    mem_normalizer_iff_map_conj_eq.mp (d.action.normalizes (d.sylow_le ht))
  have hdis : Disjoint d.V₁ d.V₂ := RankTwo.natural_planes_disjoint d.action (by decide)
  have hp : IsPGroup 2 d.S := d.T.isPGroup'.to_le (show d.S ≤ (d.T : Subgroup G) from inf_le_left)
  have hi : i = 1 ∨ i = Multiplicative.ofAdd (1 : ZMod 2) := by
    revert i
    decide +kernel
  rcases hi with rfl | rfl
  · exact fixed_plane_intersection_card_two d.S d.V d.V₁ d.V₂ hp
      ((d.action.plane_le 1).trans (module_le_sylow d)) (d.action.plane_le 1)
      (RankTwo.planeStabilizer_normalizes_planes d.action d.T d.sylow_le 1 1)
      (d.action.card_plane 1) hZ hdis (MulAut.conj t) hS hV h₁
  · exact fixed_plane_intersection_card_two d.S d.V d.V₂ d.V₁ hp
      ((d.action.plane_le _).trans (module_le_sylow d)) (d.action.plane_le _)
      (RankTwo.planeStabilizer_normalizes_planes d.action d.T d.sylow_le 1 _)
      (d.action.card_plane _) hZ hdis.symm (MulAut.conj t) hS hV h₂

private theorem outside_quotient_sqtk {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G) (d : CharacteristicTwo.LocalData G)
    (H : Subgroup G) (hH : H ∈ d.Hplus) : IsSQTK κ (H ⧸ pCore 2 H) := by
  let R := H.pCoreIn 2
  have hHN : H ≤ normalizer (R : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hN : IsTwoLocal (normalizer (R : Set G)) :=
    ⟨R, hH.1.1, isPGroup_pCoreIn 2 H, rfl⟩
  have hsq : IsSQTK κ H := (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
    ((hG.twoLocal_sqtk hN).subgroup (H.subgroupOf (normalizer (R : Set G))))
  refine ⟨?_, hsq.isKGroup.quotient _⟩
  intro p hp ho
  let _ : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hsq.stronglyQuasithin p hp ho)

/-- Assemble the normalizer, representative, transitive actor, and ordinary
graph-centralizer component from the actual rank-two setup and marked cover.
The earlier theorems and intrinsic local calculations are explicit inputs;
the source owner must instantiate them before asserting 15.3.38. -/
theorem global_geometry_of_local_cover {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G) (earlier : EarlierEmbeddings κ)
    (rankBalance : EarlierRankTwoBalance κ) (balance : EarlierBalance κ)
    (d : CharacteristicTwo.LocalData G) (e : Earlier d)
    (I L D : Subgroup G) (h : Setup d I L) (i : OrthogonalPlaneIndex)
    (c : ProjectiveMarking L 4) (lift : SylowThreeLift d.T d.Y d.S L c)
    (hZ : (center L).map L.subtype = d.action.plane i)
    (hgen : I = L ⊔ D ⊔ d.S)
    (hY : ¬ d.Yplus ≤ centralizer (d.action.plane i : Set G))
    (hZS : Nat.card d.ZS = 4)
    (hfixedSylow : IsSylowIn 2 d.S
      (centralizer (fixedPlane (d.action.plane i) d.S : Set G)))
    (reduce : ∀ H ∈ d.Hplus, ∀ B : Subgroup G,
      B ≤ H → IsComponent H (B.subgroupOf H) → (B.subgroupOf H).Normal →
      ¬ B ≤ d.M → primeRank 3 B = 2 → ¬ d.Yplus ≤ B →
      Nat.card (center B) = 4 ∧ Nonempty ((L ⧸ center L) ≃* (B ⧸ center B)) ∧
        H = B ⊔ D ⊔ d.S)
    (hm : (PerfectCentralCovering.universalProjection Sporadic.Mathieu.M23).ker = ⊥)
    (hfixed : (lift.dihedral.firstReflection : G) * (lift.dihedral.halfTurn : G) ∈
      centralizer (d.action.plane i : Set G))
    (emodel : pPrimeCore 2 ↥(I ⊓ centralizer
      ({(lift.dihedral.firstReflection : G) * (lift.dihedral.halfTurn : G)} : Set G)) ≃*
        Multiplicative (Fin 2 → ZMod 3))
    (graphModel : graphResidualIn L (lift.dihedral.firstReflection : G) ≃* PSL(2,c.F)) :
    I = normalizer (d.action.plane i : Set G) ∧
      Nonempty (RepresentativeGeometry (d.action.plane i) d.ZS d.S I) ∧
      ∃ K : Subgroup (centralizer ({(lift.dihedral.firstReflection : G)} : Set G)),
        IsComponent (centralizer ({(lift.dihedral.firstReflection : G)} : Set G)) K := by
  let V := d.action.plane i
  let : IsElementaryAbelian 2 V := d.action.elementary_of_le (d.action.plane_le i)
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card (d.action.plane i)
    rw [d.action.card_plane]; decide)
  let : IsKleinFour V := ⟨d.action.card_plane i, IsElementaryAbelian.exponent_eq_prime⟩
  let : IsQuasisimple (L.subgroupOf I) := h.component.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe h.component_le)
  have hIL := h.normalizes_component e
  have hthree : IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus) :=
    IsPGroup.of_exponent_dvd_pow (n := 1) (by simpa only [pow_one] using e.quotient_exponent)
  have hI : I = normalizer (V : Set G) :=
    normalizer_eq_of_ordinary_cover_reduction earlier hG h.outside e.sylow
      (outside_quotient_sqtk hG d) e.exclusion e.odd (inf_le_left.trans d.sylow_le)
      e.normalizer_eq hthree e.intersection_characteristic_two
      h.component_le h.component hIL hZ (h.outside_component e)
      h.component_rank.ge hY hgen reduce
  obtain ⟨v, hv1, hv2, hline, hSv⟩ := exists_fixed_line_generator V d.ZS d.S
    inf_le_right (source_fixed_line_card d hZS i)
  have hv : v ∈ V := (hline ▸ mem_zpowers v).2
  have hSylow := representative_sylow_of_fixed_line d.V V d.ZS d.S
    (d.action.plane_le i) rfl v hline hfixedSylow
  have henv := representative_envelope_of_outside earlier rankBalance hG h.outside e.sylow
    h.component_le h.component (e.odd I h.outside) hI hIL hZ h.component_rank v hv hv2 hSylow
  have hCv : centralizer ({v} : Set G) ≤ I :=
    representative_centralizer_le_of_envelope hG I L V c hI hZ
      (LocalCover.center_eq_twoCore_in h.component_le h.component (e.odd I h.outside))
      h.component_rank v hv2 hm henv
  have hJI : planeActor d.action ≤ I := hI.symm ▸ planeActor_normalizes d.action i
  have htrans := planeActor_transitive d.action i
  refine ⟨hI, ⟨{
    v := v
    ne_one := hv1
    order := hv2
    generator := hline
    sylow_centralizes := hSv
    centralizer_le := hCv
    actor := planeActor d.action
    actor_le := hJI
    transitive := htrans }⟩, ?_⟩
  exact exists_graph_component hG balance d.T d.Y d.S L V I (planeActor d.action)
    c lift hI h.component_le hIL hZ v hv hv1 hv2 hSv hCv hJI htrans
    hfixed emodel graphModel

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
