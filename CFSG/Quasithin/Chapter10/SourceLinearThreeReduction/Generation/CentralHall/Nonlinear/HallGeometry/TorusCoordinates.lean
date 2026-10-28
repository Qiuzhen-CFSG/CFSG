module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.InvariantHall
public import Theory.SpecificGroups.SL2.PairSylowTorus

/-!
# Coordinates for the original invariant odd Hall subgroup

The literal Borel embeds, modulo its two-part, in the two diagonal unit
groups of the specified binary SL₂ pair. Consequently every odd subgroup
of that Borel admits two multiplicative coordinates with trivial common
kernel. Apply this to the invariant Hall subgroup constructed from the
original H-star data: it is abelian, contains the original Hall actor's
orbit intersection, and is normalized by the whole actor.

This is the common torus setup in Aschbacher--Smith, 10.2.3, printed p.745.
The field-factor elimination and the norm-one constraints in the orthogonal
row remain separate mathematical obligations.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
include D

theorem source_sl2_odd_borel_embedding
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (C : Subgroup G) (hC : C ≤ sourceOrbitBorel T L) (ho : Odd (Nat.card C)) :
    ∃ d : C →* Fˣ × Fˣ, Function.Injective d := by
  let R := localOrbit T L
  obtain ⟨S,hS⟩ := source_orbit_sylow_intersection D
  obtain ⟨a,_⟩ := marked_sl2_pair_quotient D e hn
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hq : Function.Surjective q := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker ≤ (S : Subgroup R) := by
    intro x hx
    apply pCore_isPGroup.le_sylow_of_normal S
    exact (QuotientGroup.eq_one_iff x).mp (a.map_eq_one_iff.mp hx)
  have hCN : C ≤ sourceOrbitSylowNormalizer T L := hC.trans
    (map_subtype_le (pResidual 2 (sourceOrbitSylowNormalizer T L)))
  have hCR : C ≤ R := hCN.trans inf_le_left
  have hCS : C.subgroupOf R ≤ normalizer (S : Set R) := by
    rw [←source_orbit_sylow_normalizer_eq S hS]
    exact fun x hx => hCN hx
  have hoR : Odd (Nat.card (C.subgroupOf R)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hCR).toEquiv]
  obtain ⟨d,hd⟩ := Matrix.SpecialLinearGroup.exists_odd_subgroup_pair_sylowNormalizer_embedding
    q hq S hk (C.subgroupOf R) hCS hoR
  let b := (subgroupOfEquivOfLe hCR).symm
  exact ⟨d.comp b.toMonoidHom,hd.comp b.injective⟩

theorem exists_hall_invariant_source_borel_coordinates {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    ∃ C : Subgroup G, C ≤ sourceOrbitBorel T L ∧
      IsHallSubgroup Subgroup.OddHall.oddPrimes (C.subgroupOf (sourceOrbitBorel T L)) ∧
      B.map H.subtype ≤ normalizer (C : Set G) ∧
      B.map H.subtype ⊓ localOrbit T L ≤ C ∧
      IsMulCommutative C ∧ ∃ d : C →* Fˣ × Fˣ, Function.Injective d := by
  obtain ⟨C,hC,hHall,hBC,hplus⟩ := exists_hall_invariant_source_borel D c e
  have ho : Odd (Nat.card C) := by
    have h := Subgroup.OddHall.odd_hall_odd hHall
    rwa [Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv] at h
  obtain ⟨d,hd⟩ := source_sl2_odd_borel_embedding D e c.nonnormal C hC ho
  refine ⟨C,hC,hHall,hBC,hplus,?_,d,hd⟩
  apply isMulCommutative_iff.mpr
  intro x y
  apply hd
  simp only [map_mul,mul_comm]

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
