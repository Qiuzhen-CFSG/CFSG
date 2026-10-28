module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.LocalAction
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.Omega
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.Transport
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# Extending the component torus action to the Bender space

The commuting omega factor is pointwise fixed by the component. Factoring
an element of V into its two commuting omega factors therefore identifies
its torus fixed subgroup with U_C and its displacement with [U_L,X]. Coprime
action gives the required direct decomposition without making U_C and U_L
disjoint. Intersecting V with L recovers U_L, so pointwise coverage of the
component omega normalizer gives equality of the actual normalizer images.

The final theorem is conditional assembly. The intrinsic torus existence and
`OmegaNormalizerAction` are still model obligations, not source hypotheses.
They must be discharged before asserting the requested LocalAction exists.

Source: Aschbacher–Smith, Proposition 16.5.1, first and third paragraphs,
printed p.1194, combined manuscript of 1 March 2004.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction
open Subgroup
open scoped IsMulCommutative commutatorElement
variable {G : Type*} [Group G]

private theorem omega_factors_commute (T : Sylow 2 G) (L : Subgroup G) :
    omegaOneAmbient (commutingSylow T L) ≤
      centralizer (omegaOneAmbient (componentSylow T L) : Set G) :=
  ((omegaOneAmbient_le _).trans inf_le_right).trans
    (centralizer_le ((omegaOneAmbient_le _).trans inf_le_right))

private theorem commuting_omega_fixed {T : Sylow 2 G} {L X : Subgroup G} (hX : X ≤ L) :
    omegaOneAmbient (commutingSylow T L) ≤ centralizer (X : Set G) :=
  ((omegaOneAmbient_le _).trans inf_le_right).trans (centralizer_le hX)

/-- The fixed subgroup calculation extends from the component to V. -/
theorem ComponentTorus.fixed_eq {T : Sylow 2 G} {L : Subgroup G} {n : ℕ}
    (d : ComponentTorus T L n) :
    benderSpace T L ⊓ centralizer (d.actor : Set G) =
      omegaOneAmbient (commutingSylow T L) := by
  let := d.elementary
  apply le_antisymm
  · intro v hv
    obtain ⟨c, hc, u, hu, rfl⟩ := exists_mul_of_commuting (omega_factors_commute T L) hv.1
    have hcX := commuting_omega_fixed (d.actor_le.trans inf_le_left) hc
    have huX : u ∈ centralizer (d.actor : Set G) := by
      simpa only [inv_mul_cancel_left] using
        (centralizer (d.actor : Set G)).mul_mem
          ((centralizer (d.actor : Set G)).inv_mem hcX) hv.2
    have huC : u ∈ omegaOneAmbient (commutingSylow T L) :=
      (omegaOneAmbient_le_iff _ _).mp le_rfl u
        ⟨((omegaOneAmbient_le _).trans inf_le_left) hu, d.fixed_le ⟨hu, huX⟩⟩
        (elemPow_eq_one_of_isElementaryAbelian
          (A := omegaOneAmbient (componentSylow T L)) _ hu)
    exact (omegaOneAmbient (commutingSylow T L)).mul_mem hc huC
  · exact le_inf le_sup_left (commuting_omega_fixed (d.actor_le.trans inf_le_left))

/-- The commuting factor contributes no displacement, even if it meets U_L. -/
theorem ComponentTorus.moved_eq {T : Sylow 2 G} {L : Subgroup G} {n : ℕ}
    (d : ComponentTorus T L n) :
    ⁅benderSpace T L, d.actor⁆ = ⁅omegaOneAmbient (componentSylow T L), d.actor⁆ := by
  apply le_antisymm
  · apply commutator_le.mpr
    intro v hv x hx
    obtain ⟨c, hc, u, hu, rfl⟩ := exists_mul_of_commuting (omega_factors_commute T L) hv
    have hcK := ((omegaOneAmbient_le _).trans inf_le_right) hc
    have hxL := (d.actor_le hx).1
    have huL := ((omegaOneAmbient_le _).trans inf_le_right) hu
    have hcx : Commute c x := (hcK x hxL).symm
    have hcu : Commute c ⁅u, x⁆ :=
      (hcK _ (L.mul_mem (L.mul_mem (L.mul_mem huL hxL) (L.inv_mem huL))
        (L.inv_mem hxL))).symm
    rw [commutatorElement_mul_left_eq_conj_mul, hcx.commutator_eq, mul_one,
      hcu.eq, mul_inv_cancel_right]
    exact commutator_mem_commutator hu hx
  · exact commutator_mono le_sup_right le_rfl

/-- The intrinsic component omega is recovered by intersection with L. -/
theorem space_inf_component {T : Sylow 2 G} {L : Subgroup G}
    [IsElementaryAbelian 2 (omegaOneAmbient (commutingSylow T L))] :
    benderSpace T L ⊓ L = omegaOneAmbient (componentSylow T L) := by
  apply le_antisymm
  · intro v hv
    obtain ⟨c, hc, u, hu, rfl⟩ := exists_mul_of_commuting (omega_factors_commute T L) hv.1
    have hcL : c ∈ L := by
      simpa only [mul_inv_cancel_right] using
        L.mul_mem hv.2 (L.inv_mem (((omegaOneAmbient_le _).trans inf_le_right) hu))
    have hcU : c ∈ omegaOneAmbient (componentSylow T L) :=
      (omegaOneAmbient_le_iff _ _).mp le_rfl c
        ⟨((omegaOneAmbient_le _).trans inf_le_left) hc, hcL⟩
        (elemPow_eq_one_of_isElementaryAbelian
          (A := omegaOneAmbient (commutingSylow T L)) _ hc)
    exact (omegaOneAmbient (componentSylow T L)).mul_mem hcU hu
  · exact le_inf le_sup_right ((omegaOneAmbient_le _).trans inf_le_right)

/-- Pointwise agreement on U_L gives equality of the actual normalizer images. -/
theorem ComponentTorus.image_eq {T : Sylow 2 G} {L : Subgroup G} {n : ℕ}
    (d : ComponentTorus T L n)
    [IsElementaryAbelian 2 (omegaOneAmbient (commutingSylow T L))]
    (hnorm : OmegaNormalizerAction T L d.actor) :
    inducedActor (benderSpace T L) d.actor = inducedActor (benderSpace T L) L := by
  apply le_antisymm
  · exact map_mono (comap_mono (d.actor_le.trans inf_le_left))
  · rintro a ⟨l, hl, rfl⟩
    have hlU : (l : G) ∈ normalizer (omegaOneAmbient (componentSylow T L) : Set G) := by
      rw [← space_inf_component (T := T) (L := L)]
      exact inf_normalizer_le_normalizer_inf ⟨l.property, L.le_normalizer hl⟩
    obtain ⟨x, hx⟩ := hnorm l hl hlU
    let xN : normalizer (benderSpace T L : Set G) :=
      ⟨x, actor_normalizes_space d.actor_le x.property⟩
    refine ⟨xN, x.property, ?_⟩
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change MulAut.conj (x : G) (v : G) = MulAut.conj (l : G) (v : G)
    obtain ⟨c, hc, u, hu, he⟩ := exists_mul_of_commuting (omega_factors_commute T L) v.property
    have hcK := ((omegaOneAmbient_le _).trans inf_le_right) hc
    have hfix (y : G) (hy : y ∈ L) : MulAut.conj y c = c := by
      change y * c * y⁻¹ = c
      rw [hcK y hy, mul_inv_cancel_right]
    rw [← he, map_mul, map_mul, hfix _ (d.actor_le x.property).1, hfix (l : G) (show (l : G) ∈ L from hl), hx u hu]

variable [Finite G]

/-- Coprime action splits V over its fixed subgroup. -/
theorem ComponentTorus.decomposition {T : Sylow 2 G} {L : Subgroup G} {n : ℕ}
    (d : ComponentTorus T L n) (hn : 2 ≤ n)
    [IsElementaryAbelian 2 (omegaOneAmbient (commutingSylow T L))] :
    Disjoint (omegaOneAmbient (commutingSylow T L)) ⁅benderSpace T L, d.actor⁆ ∧
      omegaOneAmbient (commutingSylow T L) ⊔ ⁅benderSpace T L, d.actor⁆ =
        benderSpace T L := by
  let := d.elementary
  let := space_elementary_of_factors (T := T) (L := L)
  let V := benderSpace T L
  have hcop : Nat.Coprime (Nat.card d.actor) (Nat.card V) := by
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hk, d.actor_card]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_two_right]
    have he : Even (2 ^ n) := even_two.pow_of_ne_zero (by omega)
    exact (Nat.odd_sub' (Nat.one_le_pow n 2 (by decide))).mpr (by simpa using he)
  have hnorm := actor_normalizes_space d.actor_le
  let : Normalizes d.actor V := ⟨hnorm⟩
  have hsolv : Group.IsSolvable V := Group.isSolvable_of_comm fun x y => mul_comm x y
  constructor
  · have hc := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := d.actor) hsolv hcop inferInstance
    have hfix : (FixedPoints.subgroup d.actor V).map V.subtype =
        V ⊓ centralizer (d.actor : Set G) := by
      change (fixedPointSubgroup d.actor V).map V.subtype = _
      rw [fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn V d.actor hnorm]
      exact map_subgroupOf_eq_of_le inf_le_left
    rw [← d.fixed_eq, ← hfix,
      ← commutatorAction_subgroup_conj_map_eq_commutator V d.actor hnorm]
    exact disjoint_map V.subtype_injective hc.disjoint
  · rw [← d.fixed_eq, sup_comm]
    exact (eq_commutator_sup_centralizer_of_solvable_coprime V d.actor hnorm hsolv hcop).symm

/-- Conditional assembly from the outstanding intrinsic torus and normalizer
calculations. The source existence theorem must construct both inputs. -/
theorem localAction_of_componentTorus {T : Sylow 2 G} {z g : G} {L R : Subgroup G} {n : ℕ}
    (h : IntersectionSetup T z L g R)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hlift : InvolutionLifting L)
    (hdelta : omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L)
    (hfaith : Disjoint R (centralizer (L : Set G))) (hn : 2 ≤ n)
    (d : ComponentTorus T L n) (hnorm : OmegaNormalizerAction T L d.actor) :
    Nonempty (LocalAction T L R n) := by
  let := d.elementary
  let hUC := commuting_omega_elementary h hR htransport hlift hdelta hfaith
  obtain ⟨hd, hs⟩ := d.decomposition hn
  exact ⟨{
    actor := d.actor
    actor_le := d.actor_le
    actor_cyclic := d.actor_cyclic
    actor_card := d.actor_card
    commuting_elementary := hUC
    component_elementary := d.elementary
    fixed_eq := d.fixed_eq
    disjoint := hd
    span := hs
    moved_card := d.moved_eq.symm ▸ d.moved_card
    regular := d.moved_eq.symm ▸ d.regular
    image_eq := d.image_eq hnorm
    omega_le := omega_le_space h hlift hdelta }⟩

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction
