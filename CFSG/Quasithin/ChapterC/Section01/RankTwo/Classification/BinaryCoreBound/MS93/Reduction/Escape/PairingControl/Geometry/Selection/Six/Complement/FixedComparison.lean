module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.Complement.FixedComparison.FullRadius
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.Complement.FixedComparison.DualFixed

/-!
# The opposite fixed-image comparison on the six-step path

For a moving neighbor d through t, step (3) identifies [Z_d,Q_t] with the
central edge plane. This plane lies in B, so the image of Z_d in V/B is
fixed by Q_t. Compatible opposite coordinates identify that fixed image
with the annihilator of [U,Q_t]. Equal edge planes therefore give the
same dual line, and the nonfixed predecessor image covers the starting
image modulo B.

The full-radius and coordinate-action bridges are proved in the imported
extensions. The path corollary keeps first = 1, middle = 2, choice.t = 3
and p.c = 4. Predecessor movement and equality of the middle edge planes
remain explicit: Complement.Displacement discharges them from the initial
radius bound. No later escape theorem is used here.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the 'By (2)' inference in (4.3.2)(5), printed p.884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.Complement
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    {geometry : MS93.Geometry R} {p : Counterexample geometry}

/-- The neighboring Z-layer is fixed modulo the central B by its incident
edge kernel, with the common displacement identified by step (3). -/
theorem moving_Z_edge_fixed (source : LocalSource L R) (hb : 2 < geometry.b R)
    (facts : ContraryLocalFacts geometry) {a t d : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hd : d ∈ movingNeighbors geometry a) :
    ⁅Z R d, Q R t⁆ ≤ B R a (geometry.Z_normal a) := by
  change edgeDisplacement d t ≤ _
  rw [facts.edge_eq a t d ha hat hdt hd]
  exact ((Initial.edge_le_natural source a t ha hat).trans (U_le_Z a)).trans
    (EdgeTransfer.Z_le_B hb a ha)

/-- For two moving neighbors, equal actual central edge planes imply the
source fixed cover. Both the full-radius bridge and the dual action are used. -/
theorem moving_fixed_cover (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {a t₁ t₂ d e : Vertex R} (ha : color R a = false)
    (hat₁ : Adjacent R a t₁) (hdt₁ : Adjacent R d t₁)
    (hat₂ : Adjacent R a t₂) (het₂ : Adjacent R e t₂)
    (hd : d ∈ movingNeighbors geometry a) (he : e ∈ movingNeighbors geometry a)
    (hedges : edgeDisplacement a t₁ = edgeDisplacement a t₂) :
    Z R d ≤ Z R e ⊔ B R a (geometry.Z_normal a) := by
  obtain ⟨q, hqa, _⟩ := FirstPairing.contrary_at p bad a ha
  obtain ⟨iq⟩ := initial q
  have s : NaturalSectionAt a (V R a) (Z R a) := by
    simpa only [hqa] using iq.natural_section
  obtain ⟨o⟩ := facts.opposite a ha
  let dual := FixedComparison.fullRadiusDual source hb ha s o
  let S := stabilizer R a
  have hVG : V R a ≤ S := (geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)
  have hUG : U R a ≤ S := (U_le_Z a).trans (Z_le_stabilizer R a)
  have hBG : B R a (geometry.Z_normal a) ≤ S := map_subtype_le _
  have hXG : Z R d ≤ S := (moving_Z_le_V hd).trans hVG
  have hYG : Z R e ≤ S := (moving_Z_le_V he).trans hVG
  have hQG (t : Vertex R) (hat : Adjacent R a t) : Q R t ≤ S :=
    fun _ hx => hx.2 a (adjacent_symm R hat)
  have hEG (t : Vertex R) (hat : Adjacent R a t) : edgeDisplacement a t ≤ S :=
    (Initial.edge_le_natural source a t ha hat).trans hUG
  have hdisplacement (t : Vertex R) (hat : Adjacent R a t) :
      ⁅(U R a).subgroupOf S, (Q R t).subgroupOf S⁆ =
        (edgeDisplacement a t).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hUG,
      map_subgroupOf_eq_of_le (hQG t hat), map_subgroupOf_eq_of_le (hEG t hat)]
    exact (Initial.edge_eq_natural_commutator source hb modules a t ha hat).symm
  have hx : ⁅(Z R d).subgroupOf S, (Q R t₁).subgroupOf S⁆ ≤
      (B R a (geometry.Z_normal a)).subgroupOf S := by
    apply (map_le_iff_le_comap).mp
    rw [map_commutator, map_subgroupOf_eq_of_le hXG,
      map_subgroupOf_eq_of_le (hQG t₁ hat₁)]
    exact moving_Z_edge_fixed source hb facts ha hat₁ hdt₁ hd
  have hy : ⁅(Z R e).subgroupOf S, (Q R t₂).subgroupOf S⁆ ≤
      (B R a (geometry.Z_normal a)).subgroupOf S := by
    apply (map_le_iff_le_comap).mp
    rw [map_commutator, map_subgroupOf_eq_of_le hYG,
      map_subgroupOf_eq_of_le (hQG t₂ hat₂)]
    exact moving_Z_edge_fixed source hb facts ha hat₂ het₂ he
  have h := FixedComparison.cover_of_equal_displacements o.naturalU dual
    ((Q R t₁).subgroupOf S) ((Q R t₂).subgroupOf S)
    ((Z R d).subgroupOf S) ((Z R e).subgroupOf S)
    (comap_mono (moving_Z_le_V hd)) (comap_mono (moving_Z_le_V he)) hx hy
    (by rw [hdisplacement t₁ hat₁, hdisplacement t₂ hat₂, hedges])
    (by
      rw [hdisplacement t₁ hat₁,
        Nat.card_congr (subgroupOfEquivOfLe (hEG t₁ hat₁)).toEquiv]
      exact FirstPairing.StepThree.edge_card p (by omega) initial a t₁ ha hat₁)
    (by
      intro h
      apply he.2
      intro y hy
      exact h (show (⟨y, hYG hy⟩ : S) ∈ (Z R e).subgroupOf S from hy))
  have hh := map_mono (f := S.subtype) h
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hXG,
    map_subgroupOf_eq_of_le hYG, map_subgroupOf_eq_of_le hBG] at hh
  exact hh

/-- The 'By (2)' comparison in the complementary b = 6 branch, retaining
the actual path vertices at positions one, two, three and four. -/
theorem fixed_cover_of_movement_and_equal_edges (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (choice : CentralizerChoice p) (path : Selection.SixPath p)
    (hmove : p.c ∈ movingNeighbors geometry path.middle)
    (hedges : edgeDisplacement path.middle choice.t =
      edgeDisplacement path.middle path.first) :
    Z R p.a ≤ Z R p.c ⊔ B R path.middle (geometry.Z_normal path.middle) :=
  moving_fixed_cover source (by rw [path.six]; decide) modules initial facts bad
    path.middle_color (adjacent_symm R path.first_middle_adjacent)
    path.start_first_adjacent (path.middle_choice_adjacent choice)
    (adjacent_symm R (SixPath.choice_predecessor_adjacent choice))
    (path.start_moving source modules) hmove hedges.symm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.Complement
