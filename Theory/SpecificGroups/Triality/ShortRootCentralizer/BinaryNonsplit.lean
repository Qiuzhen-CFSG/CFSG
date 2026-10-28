module
public import Theory.SpecificGroups.Triality.ShortRootCentralizer.Plane
public import Theory.SpecificGroups.Triality.ShortRootCentralizer.Binary
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The nonsplitting long-root plane in the binary short centralizer

The cubic trace pairing has a nonzero kernel in its first variable. Choose
a nonzero vector there; nondegeneracy in the other variable realizes both
long-root directions as commutators of elements centralizing the pinned
short root. Thus the full long-root plane lies in the derived subgroup of
the radical intersection. This intersection is normal and a two-group in
the full native short centralizer, so the plane lies in the derived subgroup
of that centralizer's two-core.

This is the binary nonsplitting input in Aschbacher--Smith F.4.42, printed
p.295 (refs/quasithin.pdf). The original endpoint application is
Chapter14/Section02/EightLargeParabolic/ShortCentralizer. All coordinate
identities use the literal D4 root and commutator conventions.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace Triality.Standard.ShortRootCentralizer
open Parabolics RadicalCoordinates RadicalCoordinates.Centers RadicalCoordinates.LeviCommutators
open Parabolics.CentralRootSquare Parabolics.CentralRootSquare.ElementaryImage
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "hp2" => binaryParameters_prime 1 Nat.zero_lt_one

private theorem pairing_kernel_nonzero (t : ExtensionField P) :
    ∃ a : ExtensionField P, a ≠ 0 ∧ armsPairing P a t = 0 := by
  by_contra h
  push Not at h
  have hzero (a : ExtensionField P) (ha : armsPairing P a t = 0) : a = 0 :=
    by_contra fun hn => h a hn ha
  have hi : Function.Injective (fun a => armsPairing P a t) := by
    intro a b he
    change armsPairing P a t = armsPairing P b t at he
    have hz : a+b=0 := hzero _ (by rw [armsPairing_add_left,he,CharTwo.add_self_eq_zero])
    exact (eq_neg_of_add_eq_zero_left hz).trans (CharTwo.neg_eq b)
  have hc := Nat.card_le_card_of_injective _ hi
  rw [card_extensionField,card_fixedField] at hc
  norm_num [Parameters.q,binaryParameters] at hc

private theorem higher_val (Q : Parameters) (hp : Q.prime = 2) (t : ExtensionField Q) :
    (coordinates Q hp (![0,0,t],0)).val = short Q hp 2 t := by
  rw [coordinates_val,rootElement_factorization]
  simp [extendOrbit]

private theorem first_higher_commutator (Q : Parameters) (hp : Q.prime = 2)
    (a b c : ExtensionField Q) :
    ⁅(coordinates Q hp (![a,b,0],0)).val,short Q hp 2 c⁆ =
      long Q hp 1 (armsPairing Q a c) * long Q hp 2 (armsPairing Q b c) := by
  let k := coordinates Q hp (![0,0,c],0)
  have hk : firstLayer Q hp k = 0 := by rw [firstLayer_coordinates]; rfl
  have he := congrArg Subtype.val
    (commutator_of_firstLayer_zero Q hp (coordinates Q hp (![a,b,0],0)) k hk)
  have hh := (map_commutatorElement (radical Q .central).subtype
    (coordinates Q hp (![a,b,0],0)) k).symm.trans he
  change ⁅(coordinates Q hp (![a,b,0],0)).val,k.val⁆ = _ at hh
  rw [show k.val = short Q hp 2 c from higher_val Q hp c] at hh
  have hh' : ⁅(coordinates Q hp (![a,b,0],0)).val,short Q hp 2 c⁆ =
      (coordinates Q hp (0,![armsPairing Q a c,armsPairing Q b c])).val := by
    simpa only [firstLayer,thirdLayer,Equiv.symm_apply_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,k] using hh
  exact hh'.trans (planeHom_val Q hp (Multiplicative.ofAdd
    ![armsPairing Q a c,armsPairing Q b c]))

/-- The positive-radical intersection with the marked short centralizer. -/
def shortRadical (Q : Parameters) (hp : Q.prime = 2) (t : ExtensionField Q) :
    Subgroup (Carrier Q) := radical Q .central ⊓ centralizer ({short Q hp 2 t} : Set (Carrier Q))

private theorem first_mem_shortRadical (t a b : ExtensionField P)
    (ha : armsPairing P a t = 0) (hb : armsPairing P b t = 0) :
    (coordinates P hp2 (![a,b,0],0)).val ∈ shortRadical P hp2 t := by
  refine ⟨(coordinates P hp2 _).property,mem_centralizer_singleton_iff.mpr ?_⟩
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [first_higher_commutator,ha,hb,long_zero,long_zero,one_mul]

private theorem higher_mem_shortRadical (t c : ExtensionField P) :
    short P hp2 2 c ∈ shortRadical P hp2 t := by
  refine ⟨(higher_val P hp2 c) ▸ (coordinates P hp2 (![0,0,c],0)).property,?_⟩
  apply mem_centralizer_singleton_iff.mpr
  rw [←short_add,←short_add,add_comm]

/-- Both long-root directions occur as commutators inside the short-root
centralizer's radical. In particular its long-root plane cannot split off. -/
theorem plane_le_shortRadical_commutator (t : ExtensionField P) :
    plane P ≤ ⁅shortRadical P hp2 t,shortRadical P hp2 t⁆ := by
  obtain ⟨a,ha,hat⟩ := pairing_kernel_nonzero t
  intro x hx
  obtain ⟨d,e,rfl⟩ := (plane_mem_iff P hp2 x).mp hx
  obtain ⟨c,hc⟩ := armsPairing_surjective_right P hp2 a ha d
  obtain ⟨k,hk⟩ := armsPairing_surjective_right P hp2 a ha e
  have hd : long P hp2 1 d ∈ ⁅shortRadical P hp2 t,shortRadical P hp2 t⁆ := by
    have hh := commutator_mem_commutator
      (first_mem_shortRadical t a 0 hat (armsPairing_zero_left P t))
      (higher_mem_shortRadical t c)
    rw [first_higher_commutator,hc,armsPairing_zero_left] at hh
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,long_zero,mul_one] using hh
  have he : long P hp2 2 e ∈ ⁅shortRadical P hp2 t,shortRadical P hp2 t⁆ := by
    have hh := commutator_mem_commutator
      (first_mem_shortRadical t 0 a (armsPairing_zero_left P t) hat)
      (higher_mem_shortRadical t k)
    rw [first_higher_commutator,hk,armsPairing_zero_left] at hh
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,long_zero,one_mul] using hh
  exact mul_mem hd he

private theorem shortRadical_le_core (t : ExtensionField P) (ht : t ≠ 0) :
    shortRadical P hp2 t ≤
      (centralizer ({short P hp2 2 t} : Set (Carrier P))).pCoreIn 2 := by
  let C := centralizer ({short P hp2 2 t} : Set (Carrier P))
  let Q := (radical P .central).subgroupOf C
  have hn : C ≤ normalizer (radical P .central : Set (Carrier P)) :=
    (centralizer_le_central_two t ht).trans
      ((normal_subgroupOf_iff_le_normalizer (radical_le_parabolic P .central)).mp
        (radical_normal P .central))
  have hnormal : Q.Normal := normal_subgroupOf_of_le_normalizer hn
  have hp : IsPGroup 2 Q := (radical_isPGroup P hp2 .central).comap_subtype
  have hle : Q ≤ pCore 2 C := le_sSup ⟨hnormal,hp⟩
  intro x hx
  exact ⟨⟨x,hx.2⟩,hle hx.1,rfl⟩

/-- The native long-root plane lies in the derived subgroup of the full
short centralizer's two-core, the nonsplitting input of F.4.42. -/
theorem plane_le_shortCentralizer_core_commutator (t : ExtensionField P) (ht : t ≠ 0) :
    let C := centralizer ({short P hp2 2 t} : Set (Carrier P))
    (plane P).subgroupOf C ≤ ⁅pCore 2 C,pCore 2 C⁆ := by
  dsimp only
  let C := centralizer ({short P hp2 2 t} : Set (Carrier P))
  apply (map_le_map_iff_of_injective C.subtype_injective).mp
  rw [map_commutator,map_subgroupOf_eq_of_le (plane_le_centralizer P hp2 t)]
  exact (plane_le_shortRadical_commutator t).trans
    (commutator_mono (shortRadical_le_core t ht) (shortRadical_le_core t ht))

end Triality.Standard.ShortRootCentralizer
