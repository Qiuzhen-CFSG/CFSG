module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.Normalizer

/-!
# The representative and ordinary graph-centralizer component

After the uniform local source reduction proves the full normalizer equality,
the fixed line supplies v. The earlier balance and actual embedding theorems
construct its component envelope; the marked-cover and M₂₃ arguments identify
that envelope. The resulting centralizer bound and the natural plane action
give representative geometry. The graph component follows by the proved
odd-core centralization argument, rather than treating a 2-component as an
ordinary component.
Source: Aschbacher--Smith, proof of 15.3.38, printed pp.1136--1137.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open Chapter1 LocalCover LocalCover.SourceBorel GlobalGeometry
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Construct the global geometry for any of the correctly marked Sylow lifts.
The local graph residual and local odd-core models are explicit intrinsic
calculations; all normalizer and representative hypotheses are deduced. -/
theorem geometry_of_lift {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (embeddings : EarlierEmbeddings κ) (rankBalance : EarlierRankTwoBalance κ)
    (balance : EarlierBalance κ) {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) (b : SylowThreeLift d.T d.Y d.S L r.marking)
    (hZS : Nat.card d.ZS = 4)
    (hfixedSylow : ∀ i : OrthogonalPlaneIndex, IsSylowIn 2 d.S
      (centralizer (fixedPlane (d.action.plane i) d.S : Set G)))
    (hm : (PerfectCentralCovering.universalProjection Sporadic.Mathieu.M23).ker = ⊥)
    (hfixed : (b.dihedral.firstReflection : G) * (b.dihedral.halfTurn : G) ∈
      centralizer (r.cover.borel.W₁ : Set G))
    (emodel : pPrimeCore 2 ↥(I ⊓ centralizer
      ({(b.dihedral.firstReflection : G) * (b.dihedral.halfTurn : G)} : Set G)) ≃*
        Multiplicative (Fin 2 → ZMod 3))
    (graphModel : graphResidualIn L (b.dihedral.firstReflection : G) ≃* PSL(2,r.marking.F)) :
    I = normalizer (r.cover.borel.W₁ : Set G) ∧
      Nonempty (RepresentativeGeometry r.cover.borel.W₁ d.ZS d.S I) ∧
      ∃ K : Subgroup (centralizer ({(b.dihedral.firstReflection : G)} : Set G)),
        IsComponent (centralizer ({(b.dihedral.firstReflection : G)} : Set G)) K := by
  obtain ⟨i, hi⟩ := r.plane
  let V := r.cover.borel.W₁
  have hV : V = d.action.plane i := hi
  let : IsElementaryAbelian 2 V := d.action.elementary_of_le (hV ▸ d.action.plane_le i)
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hV, d.action.card_plane]; decide)
  let : IsKleinFour V := ⟨hV ▸ d.action.card_plane i, IsElementaryAbelian.exponent_eq_prime⟩
  have hI : I = normalizer (V : Set G) := normalizer_eq hG embeddings s h r
  let : IsQuasisimple (L.subgroupOf I) := h.component.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe h.component_le)
  have hIL := h.normalizes_component s.earlier
  have hZ : (center L).map L.subtype = V := r.cover.center_plane
  obtain ⟨v, hv1, hv2, hline, hSv⟩ := exists_fixed_line_generator V d.ZS d.S
    inf_le_right (by rw [hV]; exact source_fixed_line_card d hZS i)
  have hv : v ∈ V := (hline ▸ mem_zpowers v).2
  have hSylow := representative_sylow_of_fixed_line d.V V d.ZS d.S
    (hV ▸ d.action.plane_le i) rfl v hline (hV ▸ hfixedSylow i)
  have henv := representative_envelope_of_outside embeddings rankBalance hG h.outside
    s.earlier.sylow h.component_le h.component (s.earlier.odd I h.outside)
    hI hIL hZ h.component_rank v hv hv2 hSylow
  have hCv : centralizer ({v} : Set G) ≤ I :=
    representative_centralizer_le_of_envelope hG I L V r.marking hI hZ
      r.cover.center_core h.component_rank v hv2 hm henv
  have hJI : planeActor d.action ≤ I := hI.symm ▸ (hV ▸ planeActor_normalizes d.action i)
  have htrans : ∀ x y : G, x ∈ V → x ≠ 1 → y ∈ V → y ≠ 1 →
      ∃ m : planeActor d.action, (MulAut.conj (m : G)) x = y :=
    hV ▸ planeActor_transitive d.action i
  refine ⟨hI, ⟨{
    v := v, ne_one := hv1, order := hv2, generator := hline
    sylow_centralizes := hSv, centralizer_le := hCv
    actor := planeActor d.action, actor_le := hJI, transitive := htrans }⟩, ?_⟩
  exact exists_graph_component hG balance d.T d.Y d.S L V I (planeActor d.action)
    r.marking b hI h.component_le hIL hZ v hv hv1 hv2 hSv hCv hJI htrans
    hfixed emodel graphModel

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
