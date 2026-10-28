module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Centrality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Consequences
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Bounds

/-!
# The central planes and actual local conjugates in MS93 (4.3.8)

A natural subgroup intersected with a neighboring local center lies in the
edge's fixed plane. Its order-four subgroup is therefore the whole edge
displacement and the whole intersection. Apply this twice to R₀: the first
local conjugator fixes R₀ by centrality at the second predecessor, and the
second fixes it by centrality at the fourth predecessor.

The constructed witnesses retain the actual local conjugators and all four
identities. The assertion that the first image is nonmoving belongs to the
subsequent radius-four argument on p.889 and is not claimed here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.8), printed p.888.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

variable [Finite M]

theorem natural_inf_localCenter_le_edge (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (p : Counterexample geometry) (a t v : Vertex R)
    (ha : color R a = false) (hat : Adjacent R a t) (hvt : Adjacent R v t) :
    U R a ⊓ localCenter v ≤ edgeDisplacement a t := by
  have hf := edge_fixed_natural_eq_commutator hb modules a t ha hat
    (edge_le_Z p hb control edge a t ha hat)
    (edge_card p (by omega) initial a t ha hat)
  change U R a ⊓ Z R t = edgeDisplacement a t at hf
  rw [← hf]
  apply le_inf inf_le_left
  rw [EdgeTransfer.edge_Z_eq_fixed hb modules a t ha hat]
  refine le_inf (inf_le_left.trans (U_le_Z a)) ?_
  rw [localCenter_eq]
  exact (inf_le_right.trans inf_le_right).trans
    (centralizer_le (show Q R t ≤ stabilizer R v from
      fun _ hx => hx.2 v (adjacent_symm R hvt)))

theorem central_plane_eq_edge (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (p : Counterexample geometry) (a t v : Vertex R)
    (ha : color R a = false) (hat : Adjacent R a t) (hvt : Adjacent R v t)
    (A : Subgroup (FreeAmalgam R)) (hAU : A ≤ U R a) (hAC : A ≤ localCenter v)
    (hcard : Nat.card A = 4) :
    A = edgeDisplacement a t ∧ A = U R a ⊓ localCenter v := by
  have hA := le_inf hAU hAC
  have hI := natural_inf_localCenter_le_edge source hb modules initial control edge p a t v ha hat hvt
  let := finite_stabilizer R a
  let : Finite (edgeDisplacement a t) := Finite.of_injective
    (inclusion ((EdgeTransfer.edge_commutator_le_natural hb modules a t ha hat).trans
      ((U_le_Z a).trans (Z_le_stabilizer R a)))) (inclusion_injective _)
  have heq : A = edgeDisplacement a t := eq_of_le_of_card_ge (hA.trans hI)
    (by rw [hcard, edge_card p (by omega) initial a t ha hat])
  exact ⟨heq, le_antisymm hA (hI.trans heq.ge)⟩

/-- The conjugator and central-plane assertions proved before the radius-four
commutation argument. Nonmovement of the first image is a later deduction. -/
structure CentralOrbitWitnesses (p : Counterexample geometry) (d t₃ t₅ : Vertex R) where
  mu : Vertex R
  lam : Vertex R
  first_conjugator : FreeAmalgam R
  second_conjugator : FreeAmalgam R
  first_local : first_conjugator ∈ stabilizer R p.c
  second_local : second_conjugator ∈ stabilizer R d
  first_image : act R first_conjugator p.a' = mu
  second_image : act R second_conjugator mu = lam
  first_adjacent : Adjacent R mu t₃
  second_adjacent : Adjacent R lam t₅
  first_displacement : radiusCommutator p.a p.a' = edgeDisplacement mu t₃
  second_displacement : radiusCommutator p.a p.a' = edgeDisplacement lam t₅
  first_intersection : radiusCommutator p.a p.a' = U R mu ⊓ localCenter d
  second_intersection : radiusCommutator p.a p.a' = U R lam ⊓ localCenter d

/-- Local conjugation preserves the central plane, and its order four
identifies both edge displacements and both intersections at d. -/
theorem central_orbit_witnesses (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (backward : BackwardFacts geometry)
    (p : Counterexample geometry) (d t₃ t₅ : Vertex R)
    (hd : Before p.a p.a' d 4) (h₃ : Before p.a p.a' t₃ 3)
    (h₅ : Before p.a p.a' t₅ 5) : Nonempty (CentralOrbitWitnesses p d t₃ t₅) := by
  obtain ⟨g, hg, h, hh, hμ₃, hlam₅⟩ := local_orbit_choices p d t₃ t₅ hd h₃ h₅
  obtain ⟨hi⟩ := initial p
  have hc := radius_central_at_two source hb control edge p
  have hdc := radius_central_at_four (by omega) backward p d hd
  have hμ : radiusCommutator p.a p.a' ≤ U R (act R g p.a') := by
    rw [U_act, ← map_eq_of_le_localCenter _ p.c hc g hg]
    exact map_mono (Initial.radius_le_natural p source)
  have hlam : radiusCommutator p.a p.a' ≤ U R (act R h (act R g p.a')) := by
    rw [U_act, ← map_eq_of_le_localCenter _ d hdc h hh]
    exact map_mono hμ
  have hμcolor : color R (act R g p.a') = false := by
    rw [action_preserves_color, p.end_color]
  have hlamcolor : color R (act R h (act R g p.a')) = false := by
    rw [action_preserves_color, hμcolor]
  have hd₃ := hd.adjacent (geometry := geometry) h₃
  have hd₅ := adjacent_symm R (h₅.adjacent (geometry := geometry) hd)
  have hfirst := central_plane_eq_edge source hb modules initial control edge p
    (act R g p.a') t₃ d hμcolor hμ₃ hd₃ _ hμ hdc hi.radius_card
  have hsecond := central_plane_eq_edge source hb modules initial control edge p
    (act R h (act R g p.a')) t₅ d hlamcolor hlam₅ hd₅ _ hlam hdc hi.radius_card
  exact ⟨{
    mu := act R g p.a'
    lam := act R h (act R g p.a')
    first_conjugator := g
    second_conjugator := h
    first_local := hg
    second_local := hh
    first_image := rfl
    second_image := rfl
    first_adjacent := hμ₃
    second_adjacent := hlam₅
    first_displacement := hfirst.1
    second_displacement := hsecond.1
    first_intersection := hfirst.2
    second_intersection := hsecond.2
  }⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour
