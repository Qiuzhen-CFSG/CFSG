module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ComponentSylowMark
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SylowMarkSource
public import Theory.SpecificGroups.PSL3Even.SplitPrimeSylowActor
public import Theory.SpecificGroups.SymplecticFour.SplitPrimeSylowActor

/-!
# Actual split-torus actors in the original component

The original component Sylow is the literal intersection of the selected
ambient Sylow with L. The concrete linear and symplectic torus constructions
supply each odd split-prime actor in L and prove that it normalizes that
intersection while moving its derived subgroup. For the exceptional PSL₃(4)
central cover, the original source setup proves the center is a two-group;
odd lifting supplies a cubic whose fixed subgroup in the component Sylow is
exactly the embedded component center.

Every actor is constructed from the actual model. No actor-existence,
normalizer-action, or fixed-subgroup conclusion is an additional hypothesis.
The preceding crossing placement and the subsequent cubic Frattini argument
remain separate parts of the source proof.
Source: Aschbacher–Smith, The Classification of Quasithin Groups, proof of
2.5.7, printed p.556.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
variable {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

omit [Finite G] in
private theorem ambient_prime_actor {Y : Subgroup G}
    (P : Sylow 2 L) (hP : (P : Subgroup L)=Y.subgroupOf L)
    (X : Subgroup L) {p : ℕ} (hcard : Nat.card X=p)
    (hN : X ≤ normalizer (P : Set L))
    (hm : ¬X ≤ centralizer ((⁅(P : Subgroup L),(P : Subgroup L)⁆ : Subgroup L) : Set L)) :
    Nat.card (X.map L.subtype)=p ∧
      X.map L.subtype ≤ normalizer ((Y ⊓ L : Subgroup G) : Set G) ∧
      ¬ X.map L.subtype ≤ centralizer ((⁅Y ⊓ L,Y ⊓ L⁆ : Subgroup G) : Set G) := by
  have hPM : (P : Subgroup L).map L.subtype=Y⊓L := by
    rw [hP,subgroupOf_map_subtype]
  refine ⟨(card_map_of_injective L.subtype_injective).trans hcard,?_,?_⟩
  · rw [←hPM]
    exact (map_mono hN).trans ((P : Subgroup L).le_normalizer_map L.subtype)
  · rw [←hPM]
    exact map_noncentral_commutator_of_injective L.subtype L.subtype_injective P X hm

/-- The original simple linear component has a split-prime actor on its actual Sylow.
The actor has no nonidentity fixed element in that Sylow. -/
theorem MathieuSourceSetup.linear_simple_prime_torus_actor
    (c : MathieuSourceSetup H L M S z)
    (F : Type*) [Field F] [Finite F] {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n)
    (e : L ≃* PSL(3,F)) {p : ℕ} [Fact p.Prime] (ho : Odd p) (hd : p ∣ 2^n-1) :
    ∃ X : Subgroup G, X ≤ L ∧ Nat.card X=p ∧
      X ≤ normalizer ((((S : Subgroup H).map H.subtype)⊓L) : Set G) ∧
      ¬ X ≤ centralizer ((⁅((S : Subgroup H).map H.subtype)⊓L,
        ((S : Subgroup H).map H.subtype)⊓L⁆ : Subgroup G) : Set G) ∧
      (((S : Subgroup H).map H.subtype)⊓L) ⊓ centralizer (X : Set G)=⊥ := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨P,hP⟩ := MathieuSourceSetup.exists_relative_component_sylow c
  have hk : e.toMonoidHom.ker=⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  have h2 : IsPGroup 2 e.toMonoidHom.ker := by rw [hk]; exact IsPGroup.of_bot
  obtain ⟨X,hcard,hN,hm,hfix⟩ :=
    Matrix.PSL3Even.UnipotentGeometry.SplitPrimeActor.prime_actor_on_cover F
      e.toMonoidHom e.surjective h2 (by rw [hk]; exact bot_le)
      (by omega : 0<n) hF ho hd P
  obtain ⟨hcard',hN',hm'⟩ := ambient_prime_actor P hP X hcard hN hm
  refine ⟨X.map L.subtype,map_subtype_le _,hcard',hN',hm',?_⟩
  have hPM : (P : Subgroup L).map L.subtype=((S : Subgroup H).map H.subtype)⊓L := by
    rw [hP,subgroupOf_map_subtype]
  rw [←hPM,map_inf_centralizer_of_injective L.subtype L.subtype_injective,hfix,hk,Subgroup.map_bot]

/-- The source PSL₃(4) central cover has an actual cubic normalizing its component
Sylow and moving its derived subgroup. Its fixed subgroup is exactly the central kernel. -/
theorem MathieuSourceSetup.linear_four_cubic_torus_actor
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (e : L ⧸ center L ≃* Matrix.PSL3Four.PSL) :
    ∃ X : Subgroup G, X ≤ L ∧ Nat.card X=3 ∧
      X ≤ normalizer ((((S : Subgroup H).map H.subtype)⊓L) : Set G) ∧
      ¬ X ≤ centralizer ((⁅((S : Subgroup H).map H.subtype)⊓L,
        ((S : Subgroup H).map H.subtype)⊓L⁆ : Subgroup G) : Set G) ∧
      (((S : Subgroup H).map H.subtype)⊓L) ⊓ centralizer (X : Set G)=
        (center L).map L.subtype := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨P,hP⟩ := MathieuSourceSetup.exists_relative_component_sylow c
  let α := Matrix.PSL3Four.ElementaryParabolic.centerProjection e
  have hk : α.ker=center L := Matrix.PSL3Four.ElementaryParabolic.centerProjection_ker e
  have h2 : IsPGroup 2 α.ker := by
    rw [hk,MathieuSourceSetup.center_eq_twoCore c hG localC129Input_knownSimple hempty]
    exact pCore_isPGroup
  obtain ⟨X,hcard,hN,hm,hfix⟩ :=
    Matrix.PSL3Even.UnipotentGeometry.SplitPrimeActor.prime_actor_on_cover Matrix.PSL3Four.F
      α (Matrix.PSL3Four.ElementaryParabolic.centerProjection_surjective e)
      h2 hk.le (by decide : 0<2) (by simpa using Matrix.PSL3Four.card_F)
      (by decide : Odd 3) (by decide : 3 ∣ 2^2-1) P
  obtain ⟨hcard',hN',hm'⟩ := ambient_prime_actor P hP X hcard hN hm
  refine ⟨X.map L.subtype,map_subtype_le _,hcard',hN',hm',?_⟩
  have hPM : (P : Subgroup L).map L.subtype=((S : Subgroup H).map H.subtype)⊓L := by
    rw [hP,subgroupOf_map_subtype]
  rw [←hPM,map_inf_centralizer_of_injective L.subtype L.subtype_injective,hfix,hk]

/-- Every odd split prime supplies the required actor in the actual derived
symplectic component; the genuine nonbinary equivalence identifies its full matrix group. -/
theorem MathieuSourceSetup.derived_symplectic_prime_torus_actor
    (c : MathieuSourceSetup H L M S z)
    (F : Type*) [Field F] [Finite F] {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n)
    (e : L ≃* commutator (Theory.SpecificGroups.SymplecticFour.Sp F))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hd : p ∣ 2^n-1) :
    ∃ X : Subgroup G, X ≤ L ∧ Nat.card X=p ∧
      X ≤ normalizer ((((S : Subgroup H).map H.subtype)⊓L) : Set G) ∧
      ¬ X ≤ centralizer ((⁅((S : Subgroup H).map H.subtype)⊓L,
        ((S : Subgroup H).map H.subtype)⊓L⁆ : Subgroup G) : Set G) := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨P,hP⟩ := MathieuSourceSetup.exists_relative_component_sylow c
  let f := (e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn)).toMonoidHom
  have hf : Function.Bijective f :=
    (e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn)).bijective
  have hk : f.ker=⊥ := (MonoidHom.ker_eq_bot_iff _).mpr hf.injective
  have h2 : IsPGroup 2 f.ker := by rw [hk]; exact IsPGroup.of_bot
  obtain ⟨X,hcard,hN,hm⟩ :=
    Theory.SpecificGroups.SymplecticFour.SplitPrimeActor.prime_actor_on_cover
      f hf.surjective h2 (by rw [hk]; exact bot_le)
      (by omega : 1≤n) hF ho hd P
  obtain ⟨hcard',hN',hm'⟩ := ambient_prime_actor P hP X hcard hN hm
  exact ⟨X.map L.subtype,map_subtype_le _,hcard',hN',hm'⟩
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
