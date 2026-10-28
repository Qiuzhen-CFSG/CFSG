module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.RepresentativeSeed
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.NormalizerSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.RankTwoSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.FixedResidualSource
public import CFSG.Quasithin.ChapterI.Section03.SylowAutomorphisms
public import CFSG.Quasithin.ChapterI.Section03.GeneralTwoOrbit.Source

/-!
# The selected graph component in the cover reduction

The original two-layer balance and the known-simple normalizer theorem construct the graph component on the same marked lift. Only the separately constructed representative bound and mixed odd core enter the assembly.
Source: Aschbacher–Smith, 15.3.38, printed p.1137.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel GlobalGeometry
universe u
variable {G : Type u} [Group G] [Finite G]

/-- All earlier balance and graph-component inputs are discharged on the
literal selected lift. The representative-centralizer and mixed odd core
are the two independent source producers used by the final assembly. -/
theorem reduction_of_representative
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {d : CharacteristicTwo.LocalData G} (s : SourceInputs d)
    {I L : Subgroup G} (h : Setup d I L) (r : LocalResult d I L)
    (b : SylowResult d I L r) (v : G) (hv1 : v ≠ 1) (hv2 : orderOf v = 2)
    (hline : zpowers v = d.ZS ⊓ r.cover.borel.W₁)
    (hSv : d.S ≤ centralizer ({v} : Set G))
    (hCv : centralizer ({v} : Set G) ≤ I)
    (eO : pPrimeCore 2 (I ⊓ centralizer
      ({(b.lift.dihedral.firstReflection : G) * (b.lift.dihedral.halfTurn : G)} : Set G)
      : Subgroup G) ≃* Multiplicative (Fin 2 → ZMod 3)) :
    ∃ R : Reduction d I L, R.coverData = r ∧ HEq R.sylow b := by
  obtain ⟨i, hi⟩ := r.plane
  let V := r.cover.borel.W₁
  have hV : V = d.action.plane i := hi
  let : IsElementaryAbelian 2 V := d.action.elementary_of_le (hV ▸ d.action.plane_le i)
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card r.cover.borel.W₁
    rw [hi, d.action.card_plane]; decide)
  let : IsKleinFour V := ⟨by change Nat.card r.cover.borel.W₁ = 4; rw [hi, d.action.card_plane],
    IsElementaryAbelian.exponent_eq_prime⟩
  have hI := normalizer_eq_knownSimple hG s h r
  have hIL := h.normalizes_component s.earlier
  have hv : v ∈ V := (hline ▸ mem_zpowers v).2
  have hJI : planeActor d.action ≤ I := hI.symm ▸ (hi ▸ planeActor_normalizes d.action i)
  have htrans : ∀ x y : G, x ∈ V → x ≠ 1 → y ∈ V → y ≠ 1 →
      ∃ m : planeActor d.action, (MulAut.conj (m : G)) x = y :=
    hV ▸ planeActor_transitive d.action i
  obtain ⟨eGraph⟩ := graph_residual_model h r b.lift
  obtain ⟨K, hK⟩ := exists_graph_component_of_two_layer_source hG
    (fun _ _ _ _ P => ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P)
    ChapterI.GeneralTwoOrbit.Source.twoLayerCentralizerBalance
    d.T d.Y d.S L V I (planeActor d.action) r.marking b.lift hI h.component_le hIL
    r.cover.center_plane v hv hv1 hv2 hSv hCv hJI htrans b.fixes eO eGraph
  obtain ⟨ha, hk⟩ := normalizer_action_and_kernel V I L hI hIL r.cover.overgroup_centralizer
  refine ⟨{
    coverData := r
    sylow := b
    normalizer_eq := hI
    representative := {
      v := v, ne_one := hv1, order := hv2, generator := hline,
      sylow_centralizes := hSv, centralizer_le := hCv,
      actor := planeActor d.action, actor_le := hJI, transitive := htrans }
    component := K
    isComponent := hK
    normalizes := hIL
    action := ha
    kernel := hk }, rfl, HEq.rfl⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
