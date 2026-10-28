module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Normalization.Normality
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# The genuine Sylow intersections in the marked enlargement

Restricting a local Sylow to the relatively normal enlargement gives a Sylow
of its actual marked A₈, hence an intersection of order 64. The marked
transposition is outside A₈ and normalizes that intersection, so adjoining it
gives a subgroup of order 128 in the actual marked S₈ extension.

These statements supply the Sylow factors used to construct the local model.
They assert neither that the two factors generate P nor that P splits.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 16.3.11
and the completion of Theorem 16.3.7, printed pp.1181–1182 / PDF pp.1198–1199.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.ThompsonObstruction
variable {G : Type*} [Group G]
variable {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- Restrict the supplied marking to the actual enlargement. -/
noncomputable def MarkedEnlargement.enlargementEquivAlternating
    (d : MarkedEnlargement z t L) :
    enlargement t L ≃* alternatingGroup (Fin 8) :=
  (subgroupOfEquivOfLe (le_sup_left : enlargement t L ≤
    enlargement t L ⊔ zpowers z)).symm.trans
      ((d.equiv.subgroupMap _).trans (MulEquiv.subgroupCongr d.enlargement_image))

/-- The marked enlargement has the actual order of A₈. -/
theorem MarkedEnlargement.enlargement_card (d : MarkedEnlargement z t L) :
    Nat.card (enlargement t L) = 20160 := by
  rw [Nat.card_congr d.enlargementEquivAlternating.toEquiv,
    nat_card_alternatingGroup]
  norm_num

/-- The marked transposition is outside the actual A₈ enlargement. -/
theorem MarkedEnlargement.z_not_mem_enlargement (d : MarkedEnlargement z t L) :
    z ∉ enlargement t L := by
  intro hz
  let b : ↥(enlargement t L ⊔ zpowers z) :=
    ⟨z, (le_sup_right : zpowers z ≤ enlargement t L ⊔ zpowers z) (mem_zpowers z)⟩
  have hm : d.equiv b ∈ ((enlargement t L).subgroupOf
      (enlargement t L ⊔ zpowers z)).map d.equiv.toMonoidHom :=
    mem_map_of_mem _ hz
  rw [d.enlargement_image, show d.equiv b = Equiv.swap 0 1 from d.involution_image] at hm
  rw [Equiv.Perm.mem_alternatingGroup,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 8) ≠ 1)] at hm
  norm_num at hm

variable [Finite G]

/-- Normal Sylow restriction computes the intersection with the marked A₈. -/
theorem Selected.enlargement_intersection_card (s : Selected T z t L) :
    Nat.card ↥(localSylow s.P ⊓ enlargement t L) = 64 := by
  let C := involutionCentralizer t
  let K := enlargement t L
  let H := localSylow s.P
  let R := H ⊓ K
  have hKC : K ≤ C := s.marked.component.1
  let : (K.subgroupOf C).Normal :=
    s.marked.enlargement_normal s.counterexample.involution
  obtain ⟨RS, hRS⟩ := s.P.exists_subgroupOf_eq_of_normal (K.subgroupOf C)
  have hEcard : Nat.card (K.subgroupOf C) = 20160 :=
    (Nat.card_congr (subgroupOfEquivOfLe hKC).toEquiv).trans s.marked.enlargement_card
  have hRmap : (RS : Subgroup (K.subgroupOf C)).map
      (C.subtype.comp (K.subgroupOf C).subtype) = R := by
    rw [hRS, ← map_map, subgroupOf_map_subtype]
    rw [map_inf _ _ C.subtype C.subtype_injective, map_subgroupOf_eq_of_le hKC]
    rfl
  calc
    Nat.card R = Nat.card ((RS : Subgroup (K.subgroupOf C)).map
        (C.subtype.comp (K.subgroupOf C).subtype)) := by rw [hRmap]
    _ = Nat.card RS := card_map_of_injective
      (fun _ _ h => Subtype.ext (Subtype.ext h))
    _ = 2 ^ (Nat.card (K.subgroupOf C)).factorization 2 := RS.card_eq_multiplicity
    _ = 64 := by
      rw [hEcard, show 20160 = 2 ^ 6 * 315 by rfl,
        Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
      norm_num [Nat.prime_two.factorization,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)]

/-- The marked transposition normalizes the actual Sylow intersection. -/
theorem Selected.z_normalizes_enlargement_intersection (s : Selected T z t L) :
    z ∈ normalizer (localSylow s.P ⊓ enlargement t L : Subgroup G) := by
  have hN : involutionCentralizer t ≤ normalizer (enlargement t L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer s.marked.component.1).mp
      (s.marked.enlargement_normal s.counterexample.involution)
  apply mem_normalizer_iff_map_conj_eq.mpr
  calc
    _ = (localSylow s.P).map (MulAut.conj z).toMonoidHom ⊓
        (enlargement t L).map (MulAut.conj z).toMonoidHom :=
      Subgroup.map_inf _ _ _ (MulAut.conj z).injective
    _ = localSylow s.P ⊓ enlargement t L := congrArg₂ (· ⊓ ·)
      (mem_normalizer_iff_map_conj_eq.mp (le_normalizer s.z_mem_localSylow))
      (mem_normalizer_iff_map_conj_eq.mp (hN (map_subtype_le _ s.z_mem_localSylow)))

/-- Adjoining the supplied outside transposition doubles the Sylow intersection. -/
theorem Selected.wreath_factor_card (s : Selected T z t L) :
    Nat.card ↥((localSylow s.P ⊓ enlargement t L) ⊔ zpowers z) = 128 := by
  rw [card_sup_zpowers_of_normalizing_involution (localSylow s.P ⊓ enlargement t L)
    z (by rw [← s.counterexample.localSetup.involution]; exact pow_orderOf_eq_one z)
    (fun h => s.marked.z_not_mem_enlargement h.2)
    s.z_normalizes_enlargement_intersection, s.enlargement_intersection_card]

omit [Finite G] in
/-- The prospective wreath factor is an actual subgroup of the chosen local Sylow. -/
theorem Selected.wreath_factor_le_localSylow (s : Selected T z t L) :
    (localSylow s.P ⊓ enlargement t L) ⊔ zpowers z ≤ localSylow s.P :=
  sup_le inf_le_left (zpowers_le.mpr s.z_mem_localSylow)

omit [Finite G] in
/-- The same subgroup lies in the actual marked S₈ extension. -/
theorem Selected.wreath_factor_le_extension (s : Selected T z t L) :
    (localSylow s.P ⊓ enlargement t L) ⊔ zpowers z ≤
      enlargement t L ⊔ zpowers z :=
  sup_le (inf_le_right.trans le_sup_left) le_sup_right

end CFSG.Quasithin.Chapter16.ThompsonObstruction
