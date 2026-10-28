module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.Direct.Incidence
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.TerminalPairing.CoreAlgebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.TerminalPairing.Application

/-!
# The actual edge value of the binary dual pairing

The zero-fixed-space case of (1.7) has a value plane of order four. Its
seed commutator is that plane: it is nonzero, invariant under the actual
local residual, and the plane is irreducible for that residual. A geometric
EdgeSeedAt places this seed in Vcirc_c intersect V_t. The proved small
commutator bound therefore identifies the value with [Z_c,Q_t].

For D <= Q_c centralizing V_t, apply the genuine (1.7)(ii) to the
constructed CorePairing in the finite stabilizer G_c. Its value is either
trivial or this actual edge plane. The source identity V_c = Vcirc_c V_t
extends the statement to [V_c,D]. No native-incidence or pairing premise
is constructed in this module; Direct supplies them from the contained path.

Source: Meierfrankenfeld--Stellmacher (1993), (1.7)(ii), pp.847--848,
and its application in (4.3.2)(5), p.884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.Direct
open RankOnePairing TerminalPairing
open RankOnePairing.Incidence
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof

private theorem plane_card : Nat.card incidentPlane = 4 := by
  let e : incidentPlane ≃ (ZMod 2 × ZMod 2) := {
    toFun v := (v.val.toAdd 0, v.val.toAdd 1)
    invFun v := ⟨Multiplicative.ofAdd ![v.1, v.2, 0], rfl⟩
    left_inv v := by
      apply Subtype.ext
      change ![v.val.toAdd 0, v.val.toAdd 1, 0] = v.val.toAdd
      ext j
      fin_cases j
      · rfl
      · rfl
      · exact v.property.symm
    right_inv v := by cases v; rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_zmod]

private theorem value_card {A : Type*} [Group A] [Finite A]
    {e : Extension (M := A)} {i : Bool} {Z W X : Subgroup A}
    [Z.Normal] [W.Normal] (d : SourceData e i Z W X)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set A) = ⊥) :
    Nat.card (localFixed e Z i) = 4 := by
  rw [← card_coordinateImage d.natural (A := localFixed e Z i) inf_le_left,
    coordinateImage_localFixed d.natural d.localFacts.component_image d.localFacts]
  have hf := DualGeometry.model_fixed_eq_bot d d.localFacts h
  obtain ⟨k, ⟨hp, _⟩ | ⟨hp, _⟩⟩ := marked_pair d.natural.marking e.flag i
  · rw [hp, fixedSpace_conj, DualGeometry.ModelProof.fixed_point] at hf
    have hc : Nat.card (pointLine.map (vectorAction k).toMonoidHom) = 2 := by
      rw [card_map_of_injective (f := (vectorAction k).toMonoidHom) (vectorAction k).injective, line_card]
    rw [hf, card_bot] at hc
    omega
  · rw [values_eq_core, hp, core_fixed_conj,
      Matrix.PSL3Two.lineParabolicSL_pCoreIn_two_eq_R, fixed_lineCore,
      card_map_of_injective (f := (vectorAction k).toMonoidHom) (vectorAction k).injective, plane_card]

private theorem seed_value {A : Type*} [Group A] [Finite A]
    {e : Extension (M := A)} {i : Bool} {Z W X : Subgroup A}
    [Z.Normal] [W.Normal] (d : SourceData e i Z W X)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set A) = ⊥) :
    ⁅X, W⁆ = localFixed e Z i := by
  let g := DualGeometry.matrixGeometry_of_no_fixed _ _ _
    (DualGeometry.model_fixed_eq_bot d d.localFacts h)
  have hb := DualGeometry.seed_bound_of_matrixGeometry d d.localFacts g
  rcases DualGeometry.local_irreducible_of_matrixGeometry d d.localFacts g _ hb
    ((map_subtype_le _).trans (seed_commutator_normalized d d.localFacts)) with he | he
  · exact (d.commutator_nontrivial (by rw [he, card_bot])).elim
  · exact he

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : MS93.Geometry R} {p : Counterexample geometry}

/-- The actual geometric seed identifies the pairing value with its edge plane. -/
theorem pairing_value_edge (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {c t : Vertex R} (hc : color R c = false) (hct : Adjacent R c t)
    (edge : EdgeSeedAt source c t hc) (pair : edge.Pairing) :
    localFixed edge.extension ((U R c).subgroupOf (stabilizer R c)) edge.side =
      (edgeDisplacement c t).subgroupOf (stabilizer R c) := by
  let := finite_stabilizer R c
  have hv := value_card pair.data edge.fixed_bot
  have he := seed_value pair.data edge.fixed_bot
  have hle : localFixed edge.extension ((U R c).subgroupOf (stabilizer R c)) edge.side ≤
      (edgeDisplacement c t).subgroupOf (stabilizer R c) := by
    rw [← he]
    have hcore := vertexExtension_core source c hc edge.opposite edge.flag edge.weakBN
    change extensionCore edge.extension.projection = _ at hcore
    rw [hcore]
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le
      (show Q R c ≤ stabilizer R c from fun _ hx => hx.1)]
    apply le_trans (commutator_mono (le_inf ?_ ?_) le_rfl)
      (EdgeSeed.native_intersection_commutator_le_edge source hb modules initial facts p bad hc hct)
    · rintro x ⟨y, hy, rfl⟩
      exact canonicalSeed_le edge.extension edge.opposite.dual edge.side hy
    · rintro x ⟨y, hy, rfl⟩
      exact edge.seed_le_edge hy
  apply eq_of_le_of_card_ge hle
  rw [Nat.card_congr (subgroupOfEquivOfLe
    ((Initial.edge_le_natural source c t hc hct).trans
      ((U_le_Z c).trans (Z_le_stabilizer R c)))).toEquiv,
    FirstPairing.StepThree.edge_card p (by omega) initial c t hc hct, hv]

/-- The literal full-radius commutator has the same value as the moving one
when its second argument centralizes the prescribed edge radius. -/
theorem full_pairing_dichotomy (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {c t : Vertex R} (hc : color R c = false) (hct : Adjacent R c t)
    (edge : EdgeSeedAt source c t hc) (pair : edge.Pairing)
    (D : Subgroup (FreeAmalgam R)) (hDQ : D ≤ Q R c)
    (hDC : D ≤ centralizer (V R t : Set (FreeAmalgam R))) :
    ⁅V R c, D⁆ = ⊥ ∨ ⁅V R c, D⁆ = edgeDisplacement c t := by
  let S := stabilizer R c
  let := finite_stabilizer R c
  have hQG : Q R c ≤ S := fun _ hx => hx.1
  have hVG := (geometry.V_le_Q hb c hc).trans hQG
  have hCG := (Vcirc_le_V c).trans hVG
  have hDG := hDQ.trans hQG
  let D₀ := D.subgroupOf S
  let K := ⁅Vcirc R c, D⁆
  have hfull : K = ⁅V R c, D⁆ := by
    apply le_antisymm (commutator_mono (Vcirc_le_V c) le_rfl)
    have hpre : V R c ≤ commutatorPreimage (Q R c) D K := by
      rw [Initial.Consequences.radius_eq_moving_sup_edge source hc hct]
      apply sup_le
      · exact le_commutatorPreimage ((Vcirc_le_V c).trans (geometry.V_le_Q hb c hc)) le_rfl
      · apply le_commutatorPreimage
          ((Initial.Consequences.edge_radius_le_radius hc hct).trans (geometry.V_le_Q hb c hc))
        exact (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hDC)).le.trans bot_le
    have hKZ : K ≤ MS93.Z R c := ((commutator_mono le_rfl hDQ).trans
      (facts.H_eq_U c hc).le).trans (U_le_Z c)
    have hnorm : Q R c ≤ normalizer (K : Set (FreeAmalgam R)) :=
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes c hc))).trans (centralizer_le hKZ)).trans
        (Subgroup.centralizer_le_normalizer _)
    exact (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le (Q R c) D K hnorm)
  by_cases hz : ⁅V R c, D⁆ = ⊥
  · exact Or.inl hz
  right
  have hD₀ : D₀ ≤ extensionCore edge.extension.projection ⊓
      centralizer (canonicalSeed edge.extension edge.opposite.dual edge.side : Set S) := by
    apply le_inf
    · rw [show extensionCore edge.extension.projection = (Q R c).subgroupOf S from
        vertexExtension_core source c hc edge.opposite edge.flag edge.weakBN]
      exact fun _ hx => hDQ hx
    · intro x hx y hy
      exact Subtype.ext (hDC hx y (edge.seed_le_edge hy))
  have hne : ⁅generated (canonicalSeed edge.extension edge.opposite.dual edge.side), D₀⁆ ≠ ⊥ := by
    intro hzero
    have hh := congrArg (Subgroup.map S.subtype) hzero
    rw [pair.generated_eq, map_commutator, map_subgroupOf_eq_of_le hCG,
      map_subgroupOf_eq_of_le hDG, Subgroup.map_bot] at hh
    exact hz (hfull.symm.trans hh)
  have hvalue := subgroup_value pair.data edge.fixed_bot pair.natural_quotient hD₀ hne
  change ⁅generated (canonicalSeed edge.extension edge.opposite.dual edge.side), D₀⁆ =
    localFixed edge.extension ((U R c).subgroupOf S) edge.side at hvalue
  rw [pairing_value_edge source hb modules initial facts bad hc hct edge pair] at hvalue
  have hh := congrArg (Subgroup.map S.subtype) hvalue
  rw [pair.generated_eq, map_commutator, map_subgroupOf_eq_of_le hCG,
    map_subgroupOf_eq_of_le hDG, map_subgroupOf_eq_of_le
      ((Initial.edge_le_natural source c t hc hct).trans ((U_le_Z c).trans (Z_le_stabilizer R c)))] at hh
  exact hfull.symm.trans hh

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.Direct
