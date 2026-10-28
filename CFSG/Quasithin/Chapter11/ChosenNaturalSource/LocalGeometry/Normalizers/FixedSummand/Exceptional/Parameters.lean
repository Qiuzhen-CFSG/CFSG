module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair.Quotient
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.ScalarGeometry.Coordinates
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Parameters of the exceptional point-radical action

The quotient of the original flag line by its central kernel is the marked
field line. The corrected center identity therefore gives
|Z₁| = q |Z_C| without assuming that this kernel is trivial. The exceptional
Goldschmidt–O'Nan dimensions force |Z₁|=8 and |Z_C|=2, hence q=4.
These calculations use the original subgroups and quotient action and feed
the exceptional residual and block arguments in `Exceptional.Residual`.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
the final paragraph of 11.1.5, printed p.766.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.GoldschmidtONan
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
variable {G : Type*} [Group G] [Finite G]

/-- The fixed subspace retains the cardinality of the original ambient fixed center. -/
def fixedSubspaceEquiv (R L : Subgroup G) :
    fixedSubspace R L ≃ radicalFixedCenter R L where
  toFun z := ⟨z.val.toMul.val, z.property⟩
  invFun z := ⟨Additive.ofMul ⟨z.val, z.property.1⟩, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField} {c : Coordinates D F}

private def lineHom (f : InvariantFlag c) : f.Vi 0 →* Multiplicative (f.space 0) where
  toFun v := Multiplicative.ofAdd (lineProjection f (Additive.ofMul v))
  map_one' := congrArg Multiplicative.ofAdd (map_zero (lineProjection f))
  map_mul' v w := congrArg Multiplicative.ofAdd
    (map_add (lineProjection f) (Additive.ofMul v) (Additive.ofMul w))

private theorem lineHom_surjective (f : InvariantFlag c) :
    Function.Surjective (lineHom f) := by
  intro w
  obtain ⟨v, hv⟩ := lineProjection_surjective f w.toAdd
  exact ⟨v.toMul, congrArg Multiplicative.ofAdd hv⟩

private theorem lineHom_ker_map (f : InvariantFlag c) :
    (lineHom f).ker.map (f.Vi 0).subtype = f.Vi 0 ⊓ centralizer (L : Set G) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w.property, ?_⟩
    apply (c.projection_eq_one_iff (inclusion (D.centralQuotientPreimage_le _) w)).mp
    apply Multiplicative.toAdd.injective
    exact congrArg (fun z : Multiplicative (f.space 0) => z.toAdd.val) hw
  · rintro ⟨hv, hc⟩
    refine ⟨⟨v, hv⟩, ?_, rfl⟩
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd
      ((c.projection_eq_one_iff (inclusion (D.centralQuotientPreimage_le _) ⟨v, hv⟩)).mpr hc)

private theorem flagLine_card (f : InvariantFlag c) :
    Nat.card (f.Vi 0) = Nat.card (f.Vi 0 ⊓ centralizer (L : Set G) : Subgroup G) * 2 ^ F.degree := by
  let : Finite (f.space 0) := Finite.of_surjective (lineProjection f) (lineProjection_surjective f)
  have hk : Nat.card (lineHom f).ker =
      Nat.card (f.Vi 0 ⊓ centralizer (L : Set G) : Subgroup G) := by
    rw [← lineHom_ker_map]
    exact (card_map_of_injective (f.Vi 0).subtype_injective).symm
  have hs : Nat.card (Multiplicative (f.space 0)) = 2 ^ F.degree := by
    change Nat.card (f.space 0) = _
    rw [Module.natCard_eq_pow_finrank (K := F.Carrier), f.dimension 0]
    change Nat.card F.Carrier ^ 1 = _
    rw [pow_one, F.card_eq]
  have hh := (lineHom f).ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr (lineHom_surjective f), card_top, hk, hs] at hh
  exact hh.symm

/-- The corrected center identity identifies its quotient by the fixed
center with the actual marked field line, including nonsplit central kernels. -/
theorem omegaCenter_card_eq_field_mul_fixed (f : InvariantFlag c)
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L) :
    Nat.card (radicalOmegaCenter (f.Ri 0)) =
      2 ^ F.degree * Nat.card (radicalFixedCenter (f.Ri 0) L) := by
  have hU : f.Vi 0 ≤ radicalOmegaCenter (f.Ri 0) := hcenter ▸ le_sup_left
  have hi : f.Vi 0 ⊓ centralizer (L : Set G) =
      f.Vi 0 ⊓ radicalFixedCenter (f.Ri 0) L := by
    apply le_antisymm
    · exact le_inf inf_le_left (le_inf (inf_le_left.trans hU) inf_le_right)
    · exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
  have hn : radicalFixedCenter (f.Ri 0) L ≤ normalizer (f.Vi 0 : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro z hz v hv
    exact congrArg Subtype.val (mul_comm (⟨v, hU hv⟩ : radicalOmegaCenter (f.Ri 0))
      ⟨z, hz.1⟩)
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes (f.Vi 0)
    (radicalFixedCenter (f.Ri 0) L) hn
  rw [flagLine_card f, hi, ← hcenter, mul_assoc] at hc
  exact (Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := (f.Vi 0 ⊓
    radicalFixedCenter (f.Ri 0) L : Subgroup G))) hc).symm

/-- On the literal exceptional quotient, the source field is F4, the
omega center has order eight, and its original fixed summand has order two.
This supplies the numerical reduction used by both exceptional block branches. -/
theorem chosen_exceptional_parameters
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) (X : Subgroup G)
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X)) :
    S.field.degree = 2 ∧ Nat.card (radicalOmegaCenter (f.Ri 0)) = 8 ∧
      Nat.card (radicalFixedCenter (f.Ri 0) L) = 2 := by
  have hZ : Nat.card (radicalOmegaCenter (f.Ri 0)) = 8 := by
    change Nat.card (Additive (radicalOmegaCenter (f.Ri 0))) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, he.2.1]
    decide
  have hC : Nat.card (radicalFixedCenter (f.Ri 0) L) = 2 := by
    rw [← Nat.card_congr (fixedSubspaceEquiv (f.Ri 0) L), ← hfixed,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, he.1]
    decide
  have hh := omegaCenter_card_eq_field_mul_fixed f hcenter
  rw [hZ, hC] at hh
  have hp : 2 ^ S.field.degree = 2 ^ 2 := by omega
  exact ⟨(Nat.pow_right_injective (by decide : 1 < 2)) hp, hZ, hC⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
