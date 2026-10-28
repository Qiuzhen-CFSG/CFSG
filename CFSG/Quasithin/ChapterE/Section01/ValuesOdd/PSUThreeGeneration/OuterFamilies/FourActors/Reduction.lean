module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.Obstruction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.ModelInputs
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Reduction
public import Theory.GroupTheory.FourActorSylowPosition
public import Theory.SpecificGroups.SU3.FourActorInvolutionConjugacy

/-!
# Positioned outer four-group actors and local containment

The projective unitary model has one involution class. We therefore conjugate
an actual family member so that its inner involution lies in the center of the
fixed ambient Sylow subgroup. This conjugates the entire actor and preserves
both cardinalities, using normality of the socle.

For a subgroup centralizing this involution, the odd E-case already has
quotient rank one. In the component E-case the involution lies in the local
solvable radical, so the order-four actor again has image of rank at most one.
Applied to C_G(z)^∞T, this proves E₀, the intrinsic Sylow equality and the
rank bound. Solvable E-generation and a minimal supplement then recover all
of C_G(z). We reuse the general four-group rank and solvable-supplement lemmas
from the inner-family reduction; neither lemma requires this actor to be inner.

The actual outer component action and the generation contradiction after
centralizer containment remain explicit inputs. In particular no arbitrary
centralizer is asserted to be an E-member. Both E-cases and the local tau in
the component case are retained, as is the solvable alternative needed at p=3.

Source: Aschbacher--Smith, E.1.1--2, E.1.5 and E.1.14(7), printed pp.209--214;
A.3.21(a), printed p.55. E.1.14(7) refers to Aschbacher,
*GF(2)-representations of finite groups* (1982), Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The arbitrary stored Hermitian form is normalized through its actual
projective equivalence; involution conjugacy then transports back. -/
theorem involutions_isConj_of_model (L : Subgroup G) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hmodel : ClassicalGroup.IsPSU L 3 p)
    (a b : L) (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  obtain ⟨F, _, _, J, hJ, hcard, hc, ⟨e⟩⟩ := exists_identity_model hp hmodel
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  have hconj := Matrix.SU3.projective_involutions_isConj
    (fun h => ho.not_two_dvd_nat (h ▸ dvd_rfl)) hcard J hJ hc (e a) (e b)
    ((e.orderOf_eq a).trans ha) ((e.orderOf_eq b).trans hb)
  simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using e.symm.toMonoidHom.map_isConj hconj

/-- A conjugate of the original family member has a Sylow-central inner
involution. Its order and literal inner-intersection order are unchanged. -/
theorem exists_positioned_four_actor (L : Subgroup G) [L.Normal] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hmodel : ClassicalGroup.IsPSU L 3 p)
    {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    {A : Subgroup G} (hA : A ∈ d.family)
    (hfour : Nat.card A = 4) (hinter : Nat.card (A ⊓ L : Subgroup G) = 2) :
    ∃ B ∈ d.family, B ≤ (T : Subgroup G) ∧ B ≠ ⊥ ∧
      Nat.card B = 4 ∧ Nat.card (B ⊓ L : Subgroup G) = 2 ∧
      ∃ z : G, orderOf z = 2 ∧ z ∈ L ∧ z ∈ B ∧
        (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
  let := d.elementary.1 A hA
  obtain ⟨g, z, hz, hzL, hzB, hBT, hTz⟩ :=
    exists_conjugate_actor_with_sylow_central_involution L T
      (involutions_isConj_of_model L hp ho hmodel) A hinter
  let f := (MulAut.conj g).toMonoidHom
  let B := A.map f
  have hcardB : Nat.card B = 4 :=
    (card_map_of_injective (MulAut.conj g).injective).trans hfour
  have hmapL : L.map f = L := Normal.conj_smul_eq_self g L
  have hmapinf : (A ⊓ L).map f = B ⊓ L := by
    rw [map_inf _ _ f (MulAut.conj g).injective, hmapL]
  have hcardBL : Nat.card (B ⊓ L : Subgroup G) = 2 := by
    rw [← hmapinf, card_map_of_injective (MulAut.conj g).injective, hinter]
  have hBne : B ≠ ⊥ := by
    intro h
    have hh := (eq_bot_iff_card B).mp h
    omega
  exact ⟨B, d.elementary.2 g A hA, hBT, hBne, hcardB, hcardBL, z, hz, hzL, hzB, hTz⟩

/-- Discharge E.1.5 for either local E-case while retaining the supplied,
actual intrinsic Sylow intersection. -/
theorem four_centralizing_member_le {T : Sylow 2 G}
    (d : LargeFamilyObstruction T) {A K : Subgroup G}
    (hA : A ∈ d.family) (hAT : A ≤ (T : Subgroup G)) (hfour : Nat.card A = 4)
    (hAK : A ≤ K) (htau : tau (T : Subgroup G) A ≤ K)
    (hsyl : ∃ S : Sylow 2 K, (S : Subgroup K) = (T : Subgroup G).subgroupOf K)
    {z : G} (hzA : z ∈ A) (hz : z ≠ 1) (hKz : K ≤ centralizer ({z} : Set G))
    (hcase : ECaseOdd A K ∨ ECaseComponent (T : Subgroup G) A K) :
    K ≤ d.overgroup := by
  have hmember : IsEMember (T : Subgroup G) A K :=
    ⟨d.elementary.1 A hA, hAT, hAK, le_inf (tau_le _ _) htau, hsyl, hcase⟩
  apply d.members_le A hA hAT K
  rcases hcase with hodd | hcomp
  · refine ⟨hmember, Or.inl ⟨hodd, ?_⟩⟩
    obtain ⟨q, _, _, _, _, _, hr⟩ := hodd
    exact hr.le
  · let w : K := ⟨z, hAK hzA⟩
    have hwC : w ∈ center K := by
      rw [mem_center_iff]
      intro k
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (hKz k.property))
    let : Group.IsSolvable (center K) := Group.isSolvable_of_comm
      (fun a b => Subtype.ext (mem_center_iff.mp b.property a))
    have hwR : w ∈ solvableRadical K :=
      le_solvableRadical (center K) inferInstance inferInstance hwC
    exact isEMemberAt_one_of_four_radical_element hmember hcomp hfour w hzA
      (fun h => hz (congrArg Subtype.val h)) hwR

/-- The local structure of the residual supplement traps the whole
centralizer. The remaining solvable quotient needs no model hypothesis. -/
theorem centralizer_le_of_local_structure {T : Sylow 2 G}
    (d : LargeFamilyObstruction T) {A : Subgroup G}
    (hA : A ∈ d.family) (hAT : A ≤ (T : Subgroup G)) (hfour : Nat.card A = 4)
    {z : G} (hzA : z ∈ A) (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hlocal : Group.IsSolvable (centralizer ({z} : Set G)) ∨
      ECaseOdd A (centralizerResidualOvergroup T z) ∨
      ECaseComponent (T : Subgroup G) A (centralizerResidualOvergroup T z)) :
    centralizer ({z} : Set G) ≤ d.overgroup := by
  rcases hlocal with hsol | hcase
  · let := hsol
    exact solvable_sylow_overgroup_le d _ hTz
  · have hTK : (T : Subgroup G) ≤ centralizerResidualOvergroup T z := le_sup_right
    have hKz : centralizerResidualOvergroup T z ≤ centralizer ({z} : Set G) :=
      sup_le (map_subtype_le _) hTz
    have hKM := four_centralizing_member_le d hA hAT hfour (hAT.trans hTK)
      ((tau_le _ _).trans hTK) ⟨T.subtype hTK, rfl⟩ hzA hz hKz hcase
    exact sylow_overgroup_le_of_solvable_quotient d (centralizer ({z} : Set G)) hTz
      (solvableResidual _) (le_sup_left.trans hKM)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors
