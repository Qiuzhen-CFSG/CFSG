module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.AbelianSection.ModelInput
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.AbelianSection.Complement
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.AbelianSection.CentralLine
public import Theory.Frattini.CentralElementarySupplement
public import Theory.GroupTheory.PGroup.HomocyclicOmegaFrattini

/-!
# The Frattini subgroup of the abelian HS covering core

For the source coprime decomposition `Q = D × Z(K)`, adjoining the central
involution does not change the embedded Frattini subgroup. The original
covering map identifies `D` with the model two-core. Its marked `C₄³`
coordinates identify Frattini with first omega and give `E ≃ C₂³`.
The model omega marking retains the exact image of `E` in HS; the earlier
centralizer inputs then place `E` inside the actual centralizer core.

Since `E ≤ D`, the two factors still have disjoint images in `M/E`. The
proved order eight supplies the missing premise of
`frattiniRepresentation_finrank`, yielding dimension four for the literal
embedded `Qbar`. The final theorem applies all these results to `D = [Q,Y]`.
The decomposition and the published model/centralizer inputs remain explicit
for the abelian-section assembly owner to discharge.

Source: Aschbacher–Smith I.2.2(5), final HS paragraph, printed p.412 / PDF p.423.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.AbelianSection
open Sporadic.LeechRelated.HS.BlockNormalizer

private theorem coordinates_frattini_eq_omega :
    frattini (Multiplicative (Fin 3 → ZMod 4)) =
      omega (Multiplicative (Fin 3 → ZMod 4)) (p := 2) 1 := by
  change frattini (StandardHomocyclicCover (Fin 3) (2^2)) = _
  rw [← HomocyclicOmegaFrattini.powerMap_ker (Fin 3) 2 2 (by decide)]
  ext x
  change (⟨x ^ (2^(2-1)), _⟩ : omega (StandardHomocyclicCover (Fin 3) (2^2))
    (p := 2) 1) = 1 ↔ x ∈ omega (Multiplicative (Fin 3 → ZMod 4)) (p := 2) 1
  rw [Subtype.ext_iff]
  change x ^ 2 = 1 ↔ x ∈ omega (Multiplicative (Fin 3 → ZMod 4)) (p := 2) 1
  rw [OmegaAction.omega_eq_pow_ker]
  rfl

private noncomputable def coordinatesFrattiniEquiv :
    frattini (Multiplicative (Fin 3 → ZMod 4)) ≃* Multiplicative (Fin 3 → ZMod 2) :=
  (MulEquiv.subgroupCongr coordinates_frattini_eq_omega).trans
    ((HomocyclicOmegaFrattini.standardEquiv (Fin 3) 2 2 (by decide)).symm.trans
      (standardHomocyclicCoverFrattiniQuotientEquiv (Fin 3) 2 2 (by decide)))

variable {K : Type*} [Group K] [Finite K]

/-- Adjoining the central involution preserves Frattini in the common ambient M. -/
theorem E_eq_complement_frattini
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (D : Subgroup (M e))
    (hsplit : Q e = D ⊔ centralFactor e) :
    E e = (frattini D).map D.subtype := by
  let : IsElementaryAbelian 2 (center K) :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := hZ ▸ Group.exponent_dvd_nat_card }
  exact frattini_map_eq_of_central_elementary_supplement (Q e) D (centralFactor e)
    pCore_isPGroup (IsElementaryAbelian.subgroupOf (center_le_M e))
    ((centralFactor_le_center e).trans (center_le_centralizer _))
    (hsplit.trans (sup_comm _ _))

/-- The Frattini subgroup of Q lies in its displacement factor. -/
theorem E_le_complement
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (D : Subgroup (M e))
    (hsplit : Q e = D ⊔ centralFactor e) : E e ≤ D := by
  rw [E_eq_complement_frattini e hZ D hsplit]
  exact map_subtype_le _

/-- The embedded Frattini subgroup misses the original central kernel. -/
theorem E_disjoint_centralFactor_of_complement
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (D : Subgroup (M e))
    (hsplit : Q e = D ⊔ centralFactor e) (hd : Disjoint D (centralFactor e)) :
    Disjoint (E e) (centralFactor e) :=
  hd.mono_left (E_le_complement e hZ D hsplit)

/-- Transport the Frattini subgroup through the marked complement and C₄³ coordinates. -/
theorem E_nonempty_mulEquiv_of_complement
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (m : ModelInput) (D : Subgroup (M e))
    (hsplit : Q e = D ⊔ centralFactor e) (hd : Disjoint D (centralFactor e)) :
    Nonempty (E e ≃* Multiplicative (Fin 3 → ZMod 2)) := by
  let d := (complementModelEquiv e hZ D hsplit hd).trans m.coordinates
  exact ⟨(MulEquiv.subgroupCongr (E_eq_complement_frattini e hZ D hsplit)).trans
    (((frattini D).equivMapOfInjective D.subtype Subtype.val_injective).symm.trans
      ((d.subgroupMap (frattini D)).trans
        ((MulEquiv.subgroupCongr (frattini_map_equiv d)).trans coordinatesFrattiniEquiv)))⟩

/-- The actual embedded Frattini subgroup has order eight. -/
theorem E_card_of_complement
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (m : ModelInput) (D : Subgroup (M e))
    (hsplit : Q e = D ⊔ centralFactor e) (hd : Disjoint D (centralFactor e)) :
    Nat.card (E e) = 8 := by
  obtain ⟨d⟩ := E_nonempty_mulEquiv_of_complement e hZ m D hsplit hd
  rw [Nat.card_congr d.toEquiv]
  simp [Nat.card_eq_fintype_card]

private theorem model_frattini_eq_omega (m : ModelInput) :
    frattini (pCore 2 baseNormalizer) = omega (pCore 2 baseNormalizer) (p := 2) 1 := by
  apply (map_injective (f := m.coordinates.toMonoidHom) m.coordinates.injective)
  rw [frattini_map_equiv, m.coordinates.map_omega, coordinates_frattini_eq_omega]

/-- The image uses the literal localMap and original inclusion into the HS carrier. -/
theorem E_model_image_of_complement
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (m : ModelInput) (D : Subgroup (M e))
    (hsplit : Q e = D ⊔ centralFactor e) (hd : Disjoint D (centralFactor e)) :
    ((E e).map (localMap e)).map baseNormalizer.subtype = baseElementary := by
  let d := complementModelEquiv e hZ D hsplit hd
  have heq : (localMap e).comp D.subtype =
      (pCore 2 baseNormalizer).subtype.comp d.toMonoidHom := by
    ext x
    rfl
  have hlocal : (E e).map (localMap e) =
      (frattini (pCore 2 baseNormalizer)).map (pCore 2 baseNormalizer).subtype := by
    rw [E_eq_complement_frattini e hZ D hsplit, map_map, heq, ← map_map,
      frattini_map_equiv]
  rw [hlocal, model_frattini_eq_omega m]
  exact m.omega_image

/-- Pull the marked elementary eight back into the original centralizer core. -/
theorem E_le_centralizerCore_of_complement
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K) (c : CentralizerInput e u)
    (m : ModelInput) (D : Subgroup (M e))
    (hsplit : Q e = D ⊔ centralFactor e) (hd : Disjoint D (centralFactor e)) :
    E e ≤ (centralizerCore u).subgroupOf (M e) := by
  intro x hx
  change (x : K) ∈ centralizerCore u
  rw [centralizerCore_eq_model_preimage e hZ u c.center_le c.residual_image]
  apply m.elementary_le_core
  change (localMap e x : Sporadic.LeechRelated.HS.Carrier) ∈ baseElementary
  rw [← E_model_image_of_complement e hZ m D hsplit hd]
  exact mem_map_of_mem _ (mem_map_of_mem _ hx)

omit [Finite K] in
/-- Quotienting by a subgroup of D preserves disjointness of the two factor images. -/
theorem quotient_complement_disjoint_centralFactor
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (D : Subgroup (M e)) (hED : E e ≤ D) (hd : Disjoint D (centralFactor e)) :
    Disjoint (D.map (QuotientGroup.mk' (E e)))
      ((centralFactor e).map (QuotientGroup.mk' (E e))) := by
  apply disjoint_def.mpr
  rintro x ⟨d, hdD, rfl⟩ ⟨z, hzZ, hzd⟩
  have hzD : z ∈ D := by
    have he : z * d⁻¹ ∈ E e := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (E e) (z * d⁻¹) = 1
      rw [map_mul, map_inv, hzd, mul_inv_cancel]
    have hh := D.mul_mem (hED he) hdD
    simpa using hh
  have hz : z = 1 := disjoint_def.mp hd hzD hzZ
  rw [hz, map_one] at hzd
  exact hzd.symm

/-- Discharge the order-eight premise of the canonical Frattini module dimension theorem. -/
theorem frattiniRepresentation_finrank_of_complement
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (m : ModelInput) (D : Subgroup (M e))
    (hsplit : Q e = D ⊔ centralFactor e) (hd : Disjoint D (centralFactor e)) :
    Module.finrank (ZMod 2) (Additive (Qbar e)) = 4 :=
  frattiniRepresentation_finrank e hZ (E_card_of_complement e hZ m D hsplit hd)

/-- All Frattini conclusions for the source displacement factor, with the
coprime decomposition left to its existing producer. -/
theorem frattini_structure_of_coprime_decomposition
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K) (c : CentralizerInput e u)
    (m : ModelInput) (Y : Sylow 7 (M e))
    (hsplit : Q e = ⁅Q e, (Y : Subgroup (M e))⁆ ⊔ centralFactor e)
    (hd : Disjoint ⁅Q e, (Y : Subgroup (M e))⁆ (centralFactor e)) :
    E e ≤ ⁅Q e, (Y : Subgroup (M e))⁆ ∧
      Nonempty (E e ≃* Multiplicative (Fin 3 → ZMod 2)) ∧
      Nat.card (E e) = 8 ∧
      E e ≤ (centralizerCore u).subgroupOf (M e) ∧
      Disjoint (E e) (centralFactor e) ∧
      ((E e).map (localMap e)).map baseNormalizer.subtype = baseElementary ∧
      Disjoint (⁅Q e, (Y : Subgroup (M e))⁆.map (QuotientGroup.mk' (E e)))
        ((centralFactor e).map (QuotientGroup.mk' (E e))) ∧
      Module.finrank (ZMod 2) (Additive (Qbar e)) = 4 := by
  have hED := E_le_complement e hZ _ hsplit
  exact ⟨hED, E_nonempty_mulEquiv_of_complement e hZ m _ hsplit hd,
    E_card_of_complement e hZ m _ hsplit hd,
    E_le_centralizerCore_of_complement e hZ u c m _ hsplit hd,
    E_disjoint_centralFactor_of_complement e hZ _ hsplit hd,
    E_model_image_of_complement e hZ m _ hsplit hd,
    quotient_complement_disjoint_centralFactor e _ hED hd,
    frattiniRepresentation_finrank_of_complement e hZ m _ hsplit hd⟩

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.AbelianSection
