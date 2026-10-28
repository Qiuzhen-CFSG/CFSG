module

public import Theory.SpecificGroups.AlternatingSix.CentralInvolutionCentralizer
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceNonrootCentralizer

/-!
# Excluding A₆ for the original central symplectic pair

The original V lies in the center of the ambient unipotent subgroup U.
A nonroot involution z in V has centralizer U, hence its centralizer in
the literal opposite pair is U intersected with that pair. V remains
central in this intersection. If the pair were A₆, the center of this
involution centralizer would have order two, contradicting |V| > 2.

Thus the A₆ alternative listed in Aschbacher–Smith E.2.7, printed p.220,
is impossible under the stronger central placement already available to
this source consumer. Neither an abstract A₅ selection nor new Borel
markings are needed for this alternative.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate
open DiagramAutomorphisms EvenBorelTorus ChapterB

private theorem central_placement_subgroupOf
    {G : Type*} [Group G] (U V I : Subgroup G)
    (hc : V ≤ (center U).map U.subtype) :
    V.subgroupOf I ≤ (center (U.subgroupOf I)).map (U.subgroupOf I).subtype := by
  intro v hv
  obtain ⟨u,hu,heu⟩ := hc hv
  change (u : G) = (v : G) at heu
  have hvU : (v : G) ∈ U := heu ▸ u.property
  refine ⟨⟨v,hvU⟩, ?_,rfl⟩
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  apply Subtype.ext
  have h := congrArg (fun w : U => (w : G))
    (mem_center_iff.mp hu ⟨((x : U.subgroupOf I) : I),x.property⟩)
  change ((x : U.subgroupOf I) : I).val * (v : G) =
    (v : G) * ((x : U.subgroupOf I) : I).val
  simpa only [Subgroup.coe_mul,heu] using h

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The literal opposite pair of a central subgroup of order greater than
two, escaping both root axes, cannot be A₆. -/
theorem source_pair_not_alternating_six {n : ℕ}
    (hF : Nat.card F = 2^n) (V : Subgroup (Sp F))
    (hc : V ≤ (center (unipotent (F := F))).map (unipotent (F := F)).subtype)
    (hl : ¬V ≤ RootSubgroup.group 0) (hs : ¬V ≤ RootSubgroup.group 4)
    (hr : 2 < Nat.card V) :
    ¬Nonempty (oppositePair V ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  obtain ⟨z,_,hz,hC,_⟩ := source_pair_has_marked_nonroot_centralizer hF V hc hl hs
  have h := AlternatingSix.central_subgroup_card_le_two e
    ((unipotent (F := F)).subgroupOf (oppositePair V))
    (V.subgroupOf (oppositePair V)) z hz hC
    (central_placement_subgroupOf _ _ _ hc)
  have hcard : Nat.card (V.subgroupOf (oppositePair V)) = Nat.card V :=
    Nat.card_congr (subgroupOfEquivOfLe (show V ≤ oppositePair V from le_sup_left)).toEquiv
  rw [hcard] at h
  omega

/-- The actual moving actor discharges the center and root-axis premises
of the A₆ exclusion. -/
theorem source_moving_pair_not_alternating_six {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1<n)
    (a : ActorReduction.stabilizer (F := F)) (ha : ¬PreservesDiagram a.val)
    (V : Subgroup (Sp F)) [IsElementaryAbelian 2 V] (hVU : V≤unipotent)
    (hV : V.map a.val.toMonoidHom = V) (hr : 2<Nat.card V) :
    ¬Nonempty (oppositePair V ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  obtain ⟨hc,_,_,z,_,hz,hC,_⟩ :=
    source_moving_pair_with_marked_nonroot_centralizer hF hn a ha V hVU hV hr
  have h := AlternatingSix.central_subgroup_card_le_two e
    ((unipotent (F := F)).subgroupOf (oppositePair V))
    (V.subgroupOf (oppositePair V)) z hz hC
    (central_placement_subgroupOf _ _ _ hc)
  have hcard : Nat.card (V.subgroupOf (oppositePair V)) = Nat.card V :=
    Nat.card_congr (subgroupOfEquivOfLe (show V ≤ oppositePair V from le_sup_left)).toEquiv
  rw [hcard] at h
  omega

/-- The original core-free minimal-parabolic source excludes A₆ for its
aligned opposite pair, with no extra center or actor assumptions. -/
theorem source_original_pair_not_alternating_six
    {G : Type*} [Group G] [Finite G] {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hJ : minimalParabolicCore T hP=⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (e : Sp F≃*L)
    (hmark : (T : Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen : L⊔(T : Subgroup G)=⊤)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V≤T)
    (hVM : V≤(minimalParabolicMax T hP).pCoreIn 2)
    (hVN : (T : Subgroup G)≤normalizer (V : Set G)) (hr : 2<Nat.card V) :
    ¬Nonempty (oppositePair (V.comap (L.subtype.comp e.toMonoidHom)) ≃*
      alternatingGroup (Fin 6)) := by
  let f := L.subtype.comp e.toMonoidHom
  let W := V.comap f
  have hf : Function.Injective f := L.subtype_injective.comp e.injective
  obtain ⟨_,hmap,hc,_,_⟩ := Structure.SymplecticFour.source_geometry
    hF hn T hP hJ L e hmark hgen V hVT hVM hVN hr
  have hcard : Nat.card W=Nat.card V := by
    rw [←hmap,card_map_of_injective hf]
  obtain ⟨t,ht⟩ := Structure.SymplecticFour.exists_moving_sylow_actor
    hF hn T hP L e hmark hgen
  let a : ActorReduction.stabilizer (F := F) :=
    ⟨extensionAction L e t,Structure.SymplecticFour.sylow_actor T L e hmark t⟩
  have hWa : W.map a.val.toMonoidHom=W := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      change f (a.val x)∈V
      rw [show f (a.val x)=t.val*f x*t.val⁻¹ from extensionAction_apply L e t x]
      exact (mem_normalizer_iff.mp (hVN t.property) (f x)).mp hx
    · rw [card_map_of_injective a.val.injective]
  have hq : 2<Nat.card F := by
    rw [hF]
    exact (by norm_num : 2=2^1) ▸ Nat.pow_lt_pow_right (by decide) hn
  have hne : W≠⊥ := by
    intro he
    have hh : Nat.card W=1 := by rw [he]; simp
    omega
  obtain ⟨hl,hs⟩ := not_root_axes_of_moving_actor hq a ht W hWa hne
  exact source_pair_not_alternating_six hF W hc hl hs (hcard.symm ▸ hr)

end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
