module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraphAmalgam
public import Theory.SpecificGroups.SymplecticFour.Sylow

/-!
# Sylow orders in the native unitary graph centralizer

The fixed-field isomorphism Sp₄(Fix σ) × C₂ identifies an actual Sylow
subgroup of the full graph centralizer. Its order is 2q⁴. The fixed whole
Borel has the same Sylow order, by the native symplectic unipotent Sylow
and its restriction to that Borel. The original central graph factor is
retained. These counts feed the original-source Sylow placement through
the whole fixed amalgam; they do not give Sylow placement in C_G(f).

Source: Aschbacher–Smith F.4.37(1–3) and the comparison before F.4.38,
printed pp.293–294 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph
open UnitaryFourOuter

private theorem card_C2 : Nat.card C2 = 2 := by
  rw [Nat.card_congr (Multiplicative.toAdd : C2 ≃ ZMod 2),
    Nat.card_eq_fintype_card, ZMod.card]

private def productSylow {X : Type*} [Group X] [Finite X]
    (P : Sylow 2 X) : Sylow 2 (X × C2) := by
  have hp : IsPGroup 2 (P × (⊤ : Subgroup C2)) := by
    obtain ⟨a,ha⟩ := P.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := a+1)
    rw [Nat.card_prod,ha,card_top,card_C2,pow_succ]
  exact (hp.of_equiv (prodEquiv (P : Subgroup X) ⊤).symm).toSylow (by
    rw [index_prod,index_top,mul_one]
    exact P.not_dvd_index)

private theorem productSylow_card {X : Type*} [Group X] [Finite X]
    (P : Sylow 2 X) : Nat.card (productSylow P) = Nat.card P * 2 := by
  change Nat.card ((P : Subgroup X).prod (⊤ : Subgroup C2)) = _
  rw [Nat.card_congr (prodEquiv (P : Subgroup X) ⊤).toEquiv,
    Nat.card_prod,card_top,card_C2]

variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "K" => FixedBy.subfield F σ

/-- The native graph centralizer has a specified Sylow of order twice q⁴. -/
def graphCentralizerSylow {m : ℕ} (hF : Nat.card K = 2^m) (hm : 1 ≤ m) :
    Sylow 2 (centralizer ({sigma F σ hσ} : Set (Extension F σ hσ))) :=
  (productSylow (SymplecticFour.unipotentSylow hF hm)).mapSurjective
    (f := (centralizerEquiv F σ hσ).toMonoidHom) (centralizerEquiv F σ hσ).surjective

theorem graphCentralizerSylow_card {m : ℕ} (hF : Nat.card K = 2^m) (hm : 1 ≤ m) :
    Nat.card (graphCentralizerSylow F σ hσ hF hm) = 2*(2^m)^4 := by
  change Nat.card ((productSylow (SymplecticFour.unipotentSylow hF hm) :
    Subgroup (SymplecticFour.Sp K × C2)).map (centralizerEquiv F σ hσ).toMonoidHom) = _
  rw [card_map_of_injective (centralizerEquiv F σ hσ).injective,productSylow_card]
  change Nat.card (SymplecticFour.unipotent (F := K)) * 2 = _
  rw [SymplecticFour.card_unipotent,hF,mul_comm]

omit [CharP F 2] in
private theorem fixed_overgroup_sylow_card {m : ℕ} (hF : Nat.card K = 2^m) (hm : 1 ≤ m)
    (D : Subgroup (SymplecticFour.Sp K)) (hD : SymplecticFour.unipotent ≤ D)
    (P : Sylow 2 (D × C2)) : Nat.card P = 2*(2^m)^4 := by
  let U := (SymplecticFour.unipotentSylow hF hm).subtype hD
  rw [Nat.card_congr (P.equiv (productSylow U)).toEquiv,productSylow_card]
  have hu : Nat.card U = (2^m)^4 := by
    change Nat.card ((SymplecticFour.unipotent (F := K)).subgroupOf D) = _
    rw [Nat.card_congr (subgroupOfEquivOfLe hD).toEquiv,
      SymplecticFour.card_unipotent,hF]
  rw [hu,mul_comm]

omit [CharP F 2] in
/-- The fixed whole overlap has the same two-part as the full native graph
centralizer. This retains the central graph factor. -/
theorem fixedBorel_sylow_card {m : ℕ} (hF : Nat.card K = 2^m) (hm : 1 ≤ m)
    (P : Sylow 2 ((SymplecticFour.borel (F := K)) × C2)) :
    Nat.card P = 2*(2^m)^4 :=
  fixed_overgroup_sylow_card F σ hF hm _ SymplecticFour.unipotent_le_borel P

omit [CharP F 2] in
/-- The fixed point endpoint has the same Sylow order as the fixed overlap. -/
theorem fixedPoint_sylow_card {m : ℕ} (hF : Nat.card K = 2^m) (hm : 1 ≤ m)
    (P : Sylow 2 ((SymplecticFour.pointParabolic (F := K)) × C2)) :
    Nat.card P = 2*(2^m)^4 :=
  fixed_overgroup_sylow_card F σ hF hm _
    (SymplecticFour.unipotent_le_borel.trans inf_le_left) P

omit [CharP F 2] in
/-- The fixed plane endpoint has the same Sylow order as the fixed overlap. -/
theorem fixedPlane_sylow_card {m : ℕ} (hF : Nat.card K = 2^m) (hm : 1 ≤ m)
    (P : Sylow 2 ((SymplecticFour.planeParabolic (F := K)) × C2)) :
    Nat.card P = 2*(2^m)^4 :=
  fixed_overgroup_sylow_card F σ hF hm _
    (SymplecticFour.unipotent_le_borel.trans inf_le_right) P

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph
