module

public import CFSG.Quasithin.Chapter12.Section08.Preliminary.SmallFrattiniForms
public import CFSG.Quasithin.Chapter12.Section08.Actions.Comparison

/-!
# Small-Frattini forms on the literal Section 12.8 carriers

The equality Φ(U) = V₁ identifies the Frattini quotient with the actual image
Ũ in G₁/V₁. We transport the square and commutator maps through that
identification, retaining the H-conjugation action. When Z(U) is elementary
abelian, the square map also descends to Û = U/Z(U), and the two maps agree
along the literal surjection Ũ → Û.

Source: Aschbacher–Smith, Lemma 12.8.8(1–2), printed pp.851–852. The two-group,
Frattini equality and elementary-center hypotheses remain explicit here;
their earlier-source discharge belongs to the section assembly.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {V : Subgroup G} {n : ℕ} [IsMulCommutative V]

omit [Finite G] [IsMulCommutative V] in
theorem frattini_card_two_of_point (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) :
    Nat.card (frattini F.U) = 2 := by
  have hpoint : F.Vi 1 ≤ F.U :=
    (F.le_seed 1).trans (le_conjugateSpanBy V F.H)
  rw [hphi]
  calc
    Nat.card ((F.Vi 1).subgroupOf F.U) = Nat.card (F.Vi 1) :=
      Nat.card_congr (subgroupOfEquivOfLe hpoint).toEquiv
    _ = 2 := by simpa using F.card 1 hn

omit [IsMulCommutative V] in
/-- The extraspecial factor retains the marked point as its embedded Frattini subgroup. -/
theorem exists_extraspecial_factor_of_point (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hnoncomm : ¬ IsMulCommutative F.U) :
    ∃ E : Subgroup F.U, IsExtraspecial 2 E ∧ E ⊔ center F.U = ⊤ ∧
      (frattini E).map E.subtype = (F.Vi 1).subgroupOf F.U := by
  obtain ⟨E, hE, hspan, hfrattini⟩ :=
    htwo.exists_extraspecial_factor_of_frattini_card_two
      (F.frattini_card_two_of_point hn hphi) hnoncomm
  exact ⟨E, hE, hspan, hfrattini.trans hphi⟩

/-- The actual Frattini quotient identified with the actual tilded image. -/
noncomputable def frattiniTildeEquiv (F : InvariantFlag T V n)
    (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) :
    F.U ⧸ frattini F.U ≃* F.tilde F.U :=
  (QuotientGroup.quotientMulEquivOfEq hphi).trans F.utildeEquiv

omit [Finite G] in
@[simp] theorem frattiniTildeEquiv_apply_mk (F : InvariantFlag T V n)
    (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) (u : F.U) :
    F.frattiniTildeEquiv hphi (QuotientGroup.mk' (frattini F.U) u) =
      F.tildeMap F.U F.U_le_H u := by
  change F.utildeEquiv (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U) u) = _
  exact F.utildeEquiv_apply_mk u

omit [Finite G] in
theorem tildeMap_uAction (F : InvariantFlag T V n) (h : F.H) (u : F.U) :
    F.localTildeAction F.H le_rfl h (F.tildeMap F.U F.U_le_H u) =
      F.tildeMap F.U F.U_le_H (F.uAction h u) := by
  exact F.tildeAction_apply_map F.H F.U le_rfl F.U_le_H
    (le_normalizer_conjugateSpanBy V F.H) h u

omit [Finite G] in
theorem frattiniTildeEquiv_equivariant (F : InvariantFlag T V n)
    (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (h : F.H) (x : F.U ⧸ frattini F.U) :
    F.frattiniTildeEquiv hphi (quotientAut (frattini F.U) (F.uAction h) x) =
      F.localTildeAction F.H le_rfl h (F.frattiniTildeEquiv hphi x) := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (frattini F.U) x
  rw [quotientAut_apply_mk, frattiniTildeEquiv_apply_mk,
    frattiniTildeEquiv_apply_mk, tildeMap_uAction]

noncomputable def tildeSquare (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) :
    F.tilde F.U → frattini F.U :=
  fun x => SmallFrattini.quotientSquare htwo (F.frattini_card_two_of_point hn hphi)
    ((F.frattiniTildeEquiv hphi).symm x)

noncomputable def tildePolar (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) :
    F.tilde F.U → F.tilde F.U → frattini F.U :=
  fun x y => SmallFrattini.quotientPolar htwo (F.frattini_card_two_of_point hn hphi)
    ((F.frattiniTildeEquiv hphi).symm x) ((F.frattiniTildeEquiv hphi).symm y)

@[simp] theorem tildeSquare_apply_map (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (u : F.U) :
    (F.tildeSquare hn htwo hphi (F.tildeMap F.U F.U_le_H u) : F.U) = u ^ 2 := by
  rw [← F.frattiniTildeEquiv_apply_mk hphi u]
  simp only [tildeSquare, MulEquiv.symm_apply_apply,
    SmallFrattini.quotientSquare_apply_mk]

theorem tildePolar_apply_map (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (u v : F.U) :
    (F.tildePolar hn htwo hphi (F.tildeMap F.U F.U_le_H u)
      (F.tildeMap F.U F.U_le_H v) : F.U) = ⁅u, v⁆ := by
  rw [← F.frattiniTildeEquiv_apply_mk hphi u, ← F.frattiniTildeEquiv_apply_mk hphi v]
  simp only [tildePolar, MulEquiv.symm_apply_apply,
    SmallFrattini.quotientPolar_apply_mk]

theorem tildeSquare_mul (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (x y : F.tilde F.U) :
    F.tildeSquare hn htwo hphi (x * y) = F.tildeSquare hn htwo hphi x *
      F.tildeSquare hn htwo hphi y * F.tildePolar hn htwo hphi x y := by
  change SmallFrattini.quotientSquare _ _ ((F.frattiniTildeEquiv hphi).symm (x * y)) = _
  rw [map_mul]
  exact SmallFrattini.quotientSquare_mul htwo (F.frattini_card_two_of_point hn hphi) _ _

theorem tildePolar_mul_left (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (x y z : F.tilde F.U) :
    F.tildePolar hn htwo hphi (x * y) z =
      F.tildePolar hn htwo hphi x z * F.tildePolar hn htwo hphi y z := by
  change SmallFrattini.quotientPolar _ _ ((F.frattiniTildeEquiv hphi).symm (x * y)) _ = _
  rw [map_mul]
  exact SmallFrattini.quotientPolar_mul_left htwo (F.frattini_card_two_of_point hn hphi) _ _ _

theorem tildePolar_mul_right (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (x y z : F.tilde F.U) :
    F.tildePolar hn htwo hphi x (y * z) =
      F.tildePolar hn htwo hphi x y * F.tildePolar hn htwo hphi x z := by
  change SmallFrattini.quotientPolar _ _ _ ((F.frattiniTildeEquiv hphi).symm (y * z)) = _
  rw [map_mul]
  exact SmallFrattini.quotientPolar_mul_right htwo (F.frattini_card_two_of_point hn hphi) _ _ _

theorem tildePolar_symm (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (x y : F.tilde F.U) :
    F.tildePolar hn htwo hphi x y = F.tildePolar hn htwo hphi y x :=
  SmallFrattini.quotientPolar_symm htwo (F.frattini_card_two_of_point hn hphi) _ _

theorem tildePolar_self (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (x : F.tilde F.U) : F.tildePolar hn htwo hphi x x = 1 :=
  SmallFrattini.quotientPolar_self htwo (F.frattini_card_two_of_point hn hphi) _

theorem tildeSquare_invariant (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (h : F.H) (x : F.tilde F.U) :
    F.tildeSquare hn htwo hphi (F.localTildeAction F.H le_rfl h x) =
      F.tildeSquare hn htwo hphi x := by
  obtain ⟨a, rfl⟩ := (F.frattiniTildeEquiv hphi).surjective x
  rw [← F.frattiniTildeEquiv_equivariant hphi h a]
  simp only [tildeSquare, MulEquiv.symm_apply_apply]
  exact SmallFrattini.quotientSquare_invariant htwo
    (F.frattini_card_two_of_point hn hphi) (F.uAction h) a

theorem tildePolar_invariant (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (h : F.H) (x y : F.tilde F.U) :
    F.tildePolar hn htwo hphi (F.localTildeAction F.H le_rfl h x)
      (F.localTildeAction F.H le_rfl h y) = F.tildePolar hn htwo hphi x y := by
  obtain ⟨a, rfl⟩ := (F.frattiniTildeEquiv hphi).surjective x
  obtain ⟨b, rfl⟩ := (F.frattiniTildeEquiv hphi).surjective y
  rw [← F.frattiniTildeEquiv_equivariant hphi h a,
    ← F.frattiniTildeEquiv_equivariant hphi h b]
  simp only [tildePolar, MulEquiv.symm_apply_apply]
  exact SmallFrattini.quotientPolar_invariant htwo
    (F.frattini_card_two_of_point hn hphi) (F.uAction h) a b

theorem tildePolar_nonzero (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hnoncomm : ¬ IsMulCommutative F.U) :
    ∃ x y, F.tildePolar hn htwo hphi x y ≠ 1 := by
  obtain ⟨a, b, hab⟩ := SmallNonabelianTwoGroup.frattiniPolar_nonzero htwo
    (F.frattini_card_two_of_point hn hphi) hnoncomm
  change SmallFrattini.quotientPolar htwo (F.frattini_card_two_of_point hn hphi) a b ≠ 1 at hab
  refine ⟨F.frattiniTildeEquiv hphi a, F.frattiniTildeEquiv hphi b, ?_⟩
  simpa only [tildePolar, MulEquiv.symm_apply_apply] using hab

noncomputable def uhatSquare (F : InvariantFlag T V n) (htwo : IsPGroup 2 F.U)
    (hcenterPhi : frattini (center F.U) = ⊥) : F.Uhat → frattini F.U :=
  SmallFrattini.centralSquare htwo hcenterPhi

noncomputable def uhatPolar (F : InvariantFlag T V n) (htwo : IsPGroup 2 F.U)
    (hcenterPhi : frattini (center F.U) = ⊥) : F.Uhat → F.Uhat → frattini F.U :=
  SmallFrattini.centralPolar htwo hcenterPhi

omit [IsMulCommutative V] in
@[simp] theorem uhatSquare_apply_mk (F : InvariantFlag T V n) (htwo : IsPGroup 2 F.U)
    (hcenterPhi : frattini (center F.U) = ⊥) (u : F.U) :
    (F.uhatSquare htwo hcenterPhi (QuotientGroup.mk' (center F.U) u) : F.U) =
      u ^ 2 := SmallFrattini.centralSquare_apply_mk htwo hcenterPhi u

omit [IsMulCommutative V] in
theorem uhatPolar_apply_mk (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hcenterPhi : frattini (center F.U) = ⊥) (u v : F.U) :
    (F.uhatPolar htwo hcenterPhi (QuotientGroup.mk' (center F.U) u)
      (QuotientGroup.mk' (center F.U) v) : F.U) = ⁅u, v⁆ :=
  SmallFrattini.centralPolar_apply_mk htwo (F.frattini_card_two_of_point hn hphi)
    hcenterPhi u v

omit [IsMulCommutative V] in
theorem uhatSquare_invariant (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hcenterPhi : frattini (center F.U) = ⊥) (h : F.H) (x : F.Uhat) :
    F.uhatSquare htwo hcenterPhi (F.uhatAction h x) =
      F.uhatSquare htwo hcenterPhi x :=
  SmallFrattini.centralSquare_invariant htwo (F.frattini_card_two_of_point hn hphi)
    hcenterPhi (F.uAction h) x

omit [IsMulCommutative V] in
theorem uhatPolar_invariant (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hcenterPhi : frattini (center F.U) = ⊥) (h : F.H) (x y : F.Uhat) :
    F.uhatPolar htwo hcenterPhi (F.uhatAction h x) (F.uhatAction h y) =
      F.uhatPolar htwo hcenterPhi x y :=
  SmallFrattini.centralPolar_invariant htwo (F.frattini_card_two_of_point hn hphi)
    hcenterPhi (F.uAction h) x y

theorem uhatSquare_tildeToUhat (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hcenterPhi : frattini (center F.U) = ⊥) (x : F.tilde F.U) :
    F.uhatSquare htwo hcenterPhi (F.tildeToUhat hn x) = F.tildeSquare hn htwo hphi x := by
  obtain ⟨u, rfl⟩ := F.tildeMap_surjective F.U F.U_le_H x
  apply Subtype.ext
  rw [tildeToUhat_apply_map, uhatSquare_apply_mk, tildeSquare_apply_map]

theorem uhatPolar_tildeToUhat (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hcenterPhi : frattini (center F.U) = ⊥) (x y : F.tilde F.U) :
    F.uhatPolar htwo hcenterPhi (F.tildeToUhat hn x) (F.tildeToUhat hn y) =
      F.tildePolar hn htwo hphi x y := by
  obtain ⟨u, rfl⟩ := F.tildeMap_surjective F.U F.U_le_H x
  obtain ⟨v, rfl⟩ := F.tildeMap_surjective F.U F.U_le_H y
  apply Subtype.ext
  rw [tildeToUhat_apply_map, tildeToUhat_apply_map,
    uhatPolar_apply_mk (hn := hn) (hphi := hphi), tildePolar_apply_map]

/-- The commutator form on Û requires no elementary-center hypothesis. -/
noncomputable def uhatCommutator (F : InvariantFlag T V n) (htwo : IsPGroup 2 F.U) :
    F.Uhat → F.Uhat → frattini F.U := SmallFrattini.centralCommutator htwo

omit [IsMulCommutative V] in
@[simp] theorem uhatCommutator_apply_mk (F : InvariantFlag T V n)
    (htwo : IsPGroup 2 F.U) (u v : F.U) :
    (F.uhatCommutator htwo (QuotientGroup.mk' (center F.U) u)
      (QuotientGroup.mk' (center F.U) v) : F.U) = ⁅u, v⁆ :=
  SmallFrattini.centralCommutator_apply_mk htwo u v

omit [IsMulCommutative V] in
theorem uhatCommutator_mul_left (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (x y z : F.Uhat) :
    F.uhatCommutator htwo (x * y) z =
      F.uhatCommutator htwo x z * F.uhatCommutator htwo y z :=
  SmallFrattini.centralCommutator_mul_left htwo (F.frattini_card_two_of_point hn hphi) x y z

omit [IsMulCommutative V] in
theorem uhatCommutator_mul_right (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (x y z : F.Uhat) :
    F.uhatCommutator htwo x (y * z) =
      F.uhatCommutator htwo x y * F.uhatCommutator htwo x z :=
  SmallFrattini.centralCommutator_mul_right htwo (F.frattini_card_two_of_point hn hphi) x y z

omit [IsMulCommutative V] in
theorem uhatCommutator_symm (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (x y : F.Uhat) : F.uhatCommutator htwo x y = F.uhatCommutator htwo y x :=
  SmallFrattini.centralCommutator_symm htwo (F.frattini_card_two_of_point hn hphi) x y

omit [IsMulCommutative V] in
theorem uhatCommutator_self (F : InvariantFlag T V n) (htwo : IsPGroup 2 F.U)
    (x : F.Uhat) : F.uhatCommutator htwo x x = 1 :=
  SmallFrattini.centralCommutator_self htwo x

omit [IsMulCommutative V] in
theorem uhatCommutator_nondegenerate (F : InvariantFlag T V n) (htwo : IsPGroup 2 F.U)
    (x : F.Uhat) (hx : ∀ y, F.uhatCommutator htwo x y = 1) : x = 1 :=
  SmallFrattini.centralCommutator_nondegenerate htwo x hx

omit [IsMulCommutative V] in
theorem uhatCommutator_invariant (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (h : F.H) (x y : F.Uhat) :
    F.uhatCommutator htwo (F.uhatAction h x) (F.uhatAction h y) =
      F.uhatCommutator htwo x y :=
  SmallFrattini.centralCommutator_invariant htwo (F.frattini_card_two_of_point hn hphi)
    (F.uAction h) x y

theorem uhatCommutator_tildeToUhat (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (x y : F.tilde F.U) :
    F.uhatCommutator htwo (F.tildeToUhat hn x) (F.tildeToUhat hn y) =
      F.tildePolar hn htwo hphi x y := by
  obtain ⟨u, rfl⟩ := F.tildeMap_surjective F.U F.U_le_H x
  obtain ⟨v, rfl⟩ := F.tildeMap_surjective F.U F.U_le_H y
  apply Subtype.ext
  rw [tildeToUhat_apply_map, tildeToUhat_apply_map,
    uhatCommutator_apply_mk, tildePolar_apply_map]

theorem uhatCommutator_nonzero (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hnoncomm : ¬ IsMulCommutative F.U) :
    ∃ x y, F.uhatCommutator htwo x y ≠ 1 := by
  obtain ⟨x, y, hxy⟩ := F.tildePolar_nonzero hn htwo hphi hnoncomm
  refine ⟨F.tildeToUhat hn x, F.tildeToUhat hn y, ?_⟩
  rwa [uhatCommutator_tildeToUhat]

theorem tildePolar_radical_iff (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (x : F.tilde F.U) :
    (∀ y, F.tildePolar hn htwo hphi x y = 1) ↔ F.tildeToUhat hn x = 1 := by
  constructor
  · intro hx
    apply F.uhatCommutator_nondegenerate htwo
    intro z
    obtain ⟨y, rfl⟩ := F.tildeToUhat_surjective hn z
    rw [uhatCommutator_tildeToUhat]
    exact hx y
  · intro hx y
    obtain ⟨u, rfl⟩ := F.tildeMap_surjective F.U F.U_le_H x
    obtain ⟨v, rfl⟩ := F.tildeMap_surjective F.U F.U_le_H y
    rw [tildeToUhat_apply_map] at hx
    have hu : u ∈ center F.U := (QuotientGroup.eq_one_iff u).mp hx
    apply Subtype.ext
    rw [tildePolar_apply_map]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hu v).symm

theorem tildePolar_radical_eq_ker (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) :
    {x : F.tilde F.U | ∀ y, F.tildePolar hn htwo hphi x y = 1} =
      ((F.tildeToUhat hn).ker : Set (F.tilde F.U)) := by
  ext x
  exact F.tildePolar_radical_iff hn htwo hphi x

theorem tildePolar_radical_eq_tildeCenter (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) :
    {x : F.tilde F.U | ∀ y, F.tildePolar hn htwo hphi x y = 1} =
      ((F.tilde F.ZU).subgroupOf (F.tilde F.U) : Set (F.tilde F.U)) := by
  rw [F.tildePolar_radical_eq_ker hn htwo hphi, F.tildeToUhat_ker hn]

omit [IsMulCommutative V] in
theorem uhatPolar_eq_uhatCommutator (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hcenterPhi : frattini (center F.U) = ⊥) (x y : F.Uhat) :
    F.uhatPolar htwo hcenterPhi x y = F.uhatCommutator htwo x y :=
  SmallFrattini.centralPolar_eq_centralCommutator htwo
    (F.frattini_card_two_of_point hn hphi) hcenterPhi x y

omit [Finite G] in
/-- The actual quotient projection transfers the earlier tilded action kernel bound. -/
theorem localTildeAction_ker_le_uhatAction_ker (F : InvariantFlag T V n) (hn : 1 ≤ n) :
    (F.localTildeAction F.H le_rfl).ker ≤ F.uhatAction.ker := by
  intro h hh
  rw [MonoidHom.mem_ker] at hh ⊢
  ext z
  obtain ⟨x, rfl⟩ := F.tildeToUhat_surjective hn z
  have he : F.localTildeAction F.H le_rfl h x = x :=
    congrArg (fun e : MulAut (F.tilde F.U) => e x) hh
  exact (F.tildeToUhat_equivariant hn h x).symm.trans (congrArg (F.tildeToUhat hn) he)

omit [Finite G] in
theorem pCore_le_uhatAction_ker_of_tilde_kernel (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (hkernel : (F.localTildeAction F.H le_rfl).ker = pCore 2 F.H) :
    pCore 2 F.H ≤ F.uhatAction.ker :=
  hkernel.symm.le.trans (F.localTildeAction_ker_le_uhatAction_ker hn)

/-- The literal H/O₂(H) action, once the earlier-source kernel bound is supplied. -/
def tildeStarAction (F : InvariantFlag T V n)
    (hcore : pCore 2 F.H ≤ (F.localTildeAction F.H le_rfl).ker) :
    HStar F.H →* MulAut (F.tilde F.U) :=
  QuotientGroup.lift (pCore 2 F.H) (F.localTildeAction F.H le_rfl) hcore

def uhatStarAction (F : InvariantFlag T V n)
    (hcore : pCore 2 F.H ≤ F.uhatAction.ker) : HStar F.H →* MulAut F.Uhat :=
  QuotientGroup.lift (pCore 2 F.H) F.uhatAction hcore

theorem tildeSquare_star_invariant (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hcore : pCore 2 F.H ≤ (F.localTildeAction F.H le_rfl).ker)
    (h : HStar F.H) (x : F.tilde F.U) :
    F.tildeSquare hn htwo hphi (F.tildeStarAction hcore h x) =
      F.tildeSquare hn htwo hphi x := by
  induction h using QuotientGroup.induction_on with
  | H h => exact F.tildeSquare_invariant hn htwo hphi h x

theorem tildePolar_star_invariant (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hcore : pCore 2 F.H ≤ (F.localTildeAction F.H le_rfl).ker)
    (h : HStar F.H) (x y : F.tilde F.U) :
    F.tildePolar hn htwo hphi (F.tildeStarAction hcore h x)
      (F.tildeStarAction hcore h y) = F.tildePolar hn htwo hphi x y := by
  induction h using QuotientGroup.induction_on with
  | H h => exact F.tildePolar_invariant hn htwo hphi h x y

omit [IsMulCommutative V] in
theorem uhatSquare_star_invariant (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hcenterPhi : frattini (center F.U) = ⊥)
    (hcore : pCore 2 F.H ≤ F.uhatAction.ker) (h : HStar F.H) (x : F.Uhat) :
    F.uhatSquare htwo hcenterPhi (F.uhatStarAction hcore h x) =
      F.uhatSquare htwo hcenterPhi x := by
  induction h using QuotientGroup.induction_on with
  | H h => exact F.uhatSquare_invariant hn htwo hphi hcenterPhi h x

omit [IsMulCommutative V] in
theorem uhatPolar_star_invariant (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hcenterPhi : frattini (center F.U) = ⊥)
    (hcore : pCore 2 F.H ≤ F.uhatAction.ker) (h : HStar F.H) (x y : F.Uhat) :
    F.uhatPolar htwo hcenterPhi (F.uhatStarAction hcore h x)
      (F.uhatStarAction hcore h y) = F.uhatPolar htwo hcenterPhi x y := by
  induction h using QuotientGroup.induction_on with
  | H h => exact F.uhatPolar_invariant hn htwo hphi hcenterPhi h x y

omit [IsMulCommutative V] in
theorem uhatCommutator_star_invariant (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hcore : pCore 2 F.H ≤ F.uhatAction.ker) (h : HStar F.H) (x y : F.Uhat) :
    F.uhatCommutator htwo (F.uhatStarAction hcore h x)
      (F.uhatStarAction hcore h y) = F.uhatCommutator htwo x y := by
  induction h using QuotientGroup.induction_on with
  | H h => exact F.uhatCommutator_invariant hn htwo hphi h x y

omit [Finite G] in
theorem tildeToUhat_star_equivariant (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (hcoreTilde : pCore 2 F.H ≤ (F.localTildeAction F.H le_rfl).ker)
    (hcoreUhat : pCore 2 F.H ≤ F.uhatAction.ker)
    (h : HStar F.H) (x : F.tilde F.U) :
    F.tildeToUhat hn (F.tildeStarAction hcoreTilde h x) =
      F.uhatStarAction hcoreUhat h (F.tildeToUhat hn x) := by
  induction h using QuotientGroup.induction_on with
  | H h => exact F.tildeToUhat_equivariant hn h x

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
