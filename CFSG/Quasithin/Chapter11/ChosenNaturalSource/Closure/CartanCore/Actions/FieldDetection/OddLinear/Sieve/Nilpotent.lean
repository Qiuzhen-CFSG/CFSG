module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.Noncentral
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.NilpotentScalar


/-!
# The primary scalar reduction on the original Cartan geometry

The existing full A.3.6 sieve leaves a nilpotent-Fitting component image
in G₁/O₂(G₁). Its genuine Cartan actor is transported through the actual
component quotient equivalence, preserving order and coprimality. The
primary detection and scalar-action theorems show that any failure of
11.5.6(3) yields a moved primary Frattini plane of prime p>5. Its actor
fixes the SL₂(5) Fitting quotient and has order dividing both p−1 and |X|.

All common A.3.6 clauses, the original three-rank bound, extraspecial
factors and arbitrary homocyclic exponents are retained. This reduces the
remaining case; it does not exclude the ambient scalar actor or prove
11.5.6(3). That exclusion and the CartanCore assembly remain with
qt-d-1222-natural-closure-cartan. The parent qt-d-1222-natural-closure
retains discharge of the preceding original flag and Cartan geometry.
Source: Aschbacher--Smith A.3.6, pp.43--45, A.3.15, pp.50--51, and
11.5.6(3), pp.780--781.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CartanActions.FieldDetection.OddLinear
open CFSG.Quasithin.Chapter1.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- The literal component quotient maps isomorphically to its image in G₁/O₂(G₁). -/
def componentImageQuotientEquiv {I : Subgroup G} (hI : Source.ComponentIn E.Y I) :
    (I ⧸ pCore 2 I) ≃*
      (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁)) :=
  let eI : I.subgroupOf E.G₁ ≃* I := subgroupOfEquivOfLe (hI.1.trans E.Y_le_G₁)
  (QuotientGroup.congr _ _ eI (pCore_map_iso 2 eI)).symm.trans
    (cComponentTwoCoreQuotientEquiv (E.component_in_point_normalizer hI))


/-- Every remaining moved original component supplies a genuine nonidentity primary scalar actor. -/
theorem moved_component_primary_scalar_case (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (c : LocalGeometry.Coordinates D E.input.field)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hr : primeRank 3 E.Y ≤ 1) (hodd : Odd E.input.field.degree)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hmoved : ¬ ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2) :
    let B := (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))
    A36Nilpotent B ∧ A36Common B ∧ primeRank 3 B ≤ 1 ∧
      ∃ x : normalizer (I : Set G), (x : G) ∈ E.X ∧
        let a := MulAut.congr (E.componentImageQuotientEquiv hI) (coreQuotientAction I x)
        Nat.Coprime (orderOf a) (Nat.card B) ∧
          quotientAut (fittingSubgroup B) a = 1 ∧
          ∃ p : ℕ, p.Prime ∧ 5 < p ∧ p ∣ Nat.card (fittingSubgroup B) ∧
            (LocalModels.OddExtraspecialThree p (pCore p B) ∨
              LocalModels.HomocyclicTwo p (pCore p B)) ∧
            IsElementaryAbelian p (pCore p B ⧸ frattini (pCore p B)) ∧
            Nat.card (pCore p B ⧸ frattini (pCore p B)) = p ^ 2 ∧
            primaryFrattiniAut p B a ≠ 1 ∧
            orderOf (primaryFrattiniAut p B a) ∣ Nat.card E.X ∧
            orderOf (primaryFrattiniAut p B a) ∣ p - 1 := by
  let B := (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))
  have hsource : A36Nilpotent B ∧ A36Common B ∧ primeRank 3 B ≤ 1 :=
    E.moved_component_nilpotent_fitting_case hp hT hX c
      hcart hXR hCX hz hNG hr hodd hI hmoved
  rcases hsource with ⟨hn,hcommon,hrB⟩
  let := pCore_isNilpotent (p := 2) (G := E.G₁)
  let : Group.IsPerfect B := ((E.component_in_point_normalizer hI).map_quotient _).perfect
  have hmover : ∃ x : normalizer (I : Set G), (x : G) ∈ E.X ∧
      coreQuotientAction I x ≠ 1 :=
    E.exists_component_quotient_mover hp hX hcart.odd hI hmoved
  rcases hmover with ⟨x,hx,hne⟩
  let eQ := E.componentImageQuotientEquiv hI
  let a := MulAut.congr eQ (coreQuotientAction I x)
  have hd : orderOf a ∣ Nat.card E.X := by
    apply ((orderOf_map_dvd (MulAut.congr eQ).toMonoidHom _).trans
      (orderOf_map_dvd (coreQuotientAction I) x)).trans
    rw [← Subgroup.orderOf_coe x]
    exact E.X.orderOf_dvd_natCard hx
  have hcop := E.cartan_coprime_of_local_action hp hX hcart.odd
    (fun _ hprime hdiv => (c.cartan_primeRank hcart hprime hdiv).ge) hCX hz
  have haB : Nat.Coprime (orderOf a) (Nat.card B) := by
    rw [← Nat.card_congr eQ.toEquiv]
    exact (E.cartan_coprime_component_of_split_marking (c.cartanTorusEquiv hcart)
      hcop hI).of_dvd hd (pCore 2 I).card_quotient_dvd_card
  have hane : a ≠ 1 := fun he => hne
    ((MulAut.congr eQ).injective (he.trans (map_one _).symm))
  obtain ⟨p,hpprime,hp5,hpF,hshape,hel,hcard,hm⟩ :=
    exists_moved_nilpotent_primary_plane hn a haB hane
  let : Fact p.Prime := ⟨hpprime⟩
  exact ⟨hn,hcommon,hrB,x,hx,haB,nilpotent_quotient_actor_eq_one hn hcommon a haB,
    p,hpprime,hp5,hpF,hshape,hel,hcard,hm,
    (orderOf_map_dvd (primaryFrattiniAut p B) a).trans hd,
    nilpotent_primary_actor_order_dvd hn hcommon a haB hpF⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
