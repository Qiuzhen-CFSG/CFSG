module

public import Theory.SpecificGroups.SymplecticFour.SimpleQuotients
public import Theory.GroupTheory.Covering
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The actual odd-prime symplectic quotient cover

The carrier is the full matrix group Sp₄(F), and its projective group is the
literal quotient by its center. Transvection generation and the ternary
four-transvection identity prove perfectness for every finite field of order
at least three. The faithful primitive projective action proves simplicity.
Thus the literal quotient map is a finite quasisimple `Covering`.

A central element acts as a scalar, and preservation of a hyperbolic pair
forces its square to be one. In odd characteristic the center is therefore
{I, −I}, giving an actual multiplicative equivalence of the quotient kernel
with C₂. This is the lower bound in the multiplier calculation; it does not
establish the universal property.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.2(2),
printed p.33, and I.1.1–I.1.4, printed pp.407–408; GLS3 §6.1, Table 6.1.2.
The ordinary odd-prime symplectic row is absent from the displayed I.1.4 list.

The large-field perfectness, scalar-square argument and field transport adapt
Gerald Höhn's ATLAS, revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`,
`Atlas/LinearGroups/Symplectic/{PerfectLarge,Center,
FieldTransport}.lean`. Covered by the ATLAS Research and Attribution License
1.0; see `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`. Changes:
specialize to four-space, use the module-compatible `Matrix.PSp4Three` API,
include the ternary case, and package the quotient and its C₂ kernel.
-/

public section

noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime
open Matrix Matrix.PSp4Three Theory.GroupTheory
open scoped commutatorElement
universe u
abbrev Sp (F : Type u) [Field F] := ↥(Matrix.symplecticGroup (Fin 2) F)
abbrev PSp (F : Type u) [Field F] := Sp F ⧸ Subgroup.center (Sp F)
variable {F : Type u} [Field F]

private theorem perfect_large [Finite F] (hq : 3 < Nat.card F) : Group.IsPerfect (Sp F) := by
  classical
  let := Fintype.ofFinite F
  have hcard : ({0, 1, -1} : Finset F).card < (Finset.univ : Finset F).card := by
    have h := Finset.card_le_three (a := (0 : F)) (b := 1) (c := -1)
    simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card] using lt_of_le_of_lt h hq
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  have hc₂ : c ^ 2 ≠ 1 := fun h => (sq_eq_one_iff.mp h).elim hc.2.1 hc.2.2
  apply perfect_of_transvections
  intro v a
  by_cases hv : v = 0
  · subst v; simp
  obtain ⟨g, _, hg⟩ := exists_generated_send hv (smul_ne_zero hc.1 hv)
  let b := a / (c ^ 2 - 1)
  have hb : (c ^ 2 - 1) * b = a := mul_div_cancel₀ a (sub_ne_zero.mpr hc₂)
  have he : ⁅g, transvection v b⁆ = transvection v a := by
    rw [commutatorElement_def, transvection_conjugate, hg, transvection_scale,
      transvection_inverse, ← transvection_add]
    congr 1
    calc
      c ^ 2 * b + -b = (c ^ 2 - 1) * b := by ring
      _ = a := hb
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem perfect [Finite F] (hq : 2 < Nat.card F) : Group.IsPerfect (Sp F) := by
  by_cases h3 : Nat.card F = 3
  · let := Fintype.ofFinite F
    have h3' : Fintype.card F = 3 := by simpa only [Nat.card_eq_fintype_card] using h3
    let : CharP F 3 := charP_of_card_eq_prime h3'
    apply perfect_of_ternary_scalars (by decide : 2 ≤ 2)
    let e := ZMod.ringEquiv F h3'
    intro a
    obtain ⟨a, rfl⟩ := e.surjective a
    fin_cases a
    · exact Or.inl (map_zero e)
    · exact Or.inr (Or.inl (map_one e))
    · exact Or.inr (Or.inr (by change e (-1) = -1; simp))
  · exact perfect_large (by omega)

theorem projective_simple [Finite F] (hq : 2 < Nat.card F) : IsSimpleGroup (PSp F) := by
  let := SimpleQuotients.projective_preprimitive (F := F)
  let := projective_nontrivial (F := F) (n := 2) (by decide)
  let := perfect hq
  let : Group.IsPerfect (PSp F) := inferInstance
  exact iwasawa.isSimpleGroup (Group.IsPerfect.commutator_eq_top (G := PSp F)) inferInstance

theorem quasisimple [Finite F] (hq : 2 < Nat.card F) : IsQuasisimple (Sp F) where
  toIsPerfect := perfect hq
  simple := projective_simple hq

theorem projective_quasisimple [Finite F] (hq : 2 < Nat.card F) : IsQuasisimple (PSp F) := by
  let := perfect hq
  let := projective_simple hq
  exact { toIsPerfect := inferInstance
          simple := ((QuotientGroup.quotientMulEquivOfEq
            (Group.IsPerfect.center_quotient_center_eq_bot (Sp F))).trans
              (QuotientGroup.quotientBot)).isSimpleGroup }

def negIdentity (F : Type u) [Field F] : Sp F :=
  ⟨-1, SymplecticGroup.neg_mem (one_mem _)⟩

@[simp] theorem negIdentity_smul (x : Vector 2 F) : negIdentity F • x = -x := by
  change (-1 : Matrix (Index 2) (Index 2) F) *ᵥ x = -x
  rw [Matrix.neg_mulVec, Matrix.one_mulVec]

theorem negIdentity_mem_center : negIdentity F ∈ Subgroup.center (Sp F) :=
  scalar_is_central _ (-1) (fun x => by simp)

theorem mem_center_iff (g : Sp F) :
    g ∈ Subgroup.center (Sp F) ↔ g = 1 ∨ g = negIdentity F := by
  constructor
  · intro hg
    obtain ⟨a, ha⟩ := central_is_scalar g hg
    have hs := preserves g (e (n := 2) (F := F) 0) (f (n := 2) (F := F) 0)
    rw [← smul_eq_mulVec g, ← smul_eq_mulVec g, ha, ha] at hs
    have ha₂ : a ^ 2 = 1 := by simpa [map_smul, e, Pi.single_apply, pow_two] using hs
    rcases sq_eq_one_iff.mp ha₂ with rfl | rfl
    · left; apply ext_action; intro x; simp [ha]
    · right; apply ext_action; intro x; simp [ha]
  · rintro (rfl | rfl)
    · exact (Subgroup.center (Sp F)).one_mem
    · exact negIdentity_mem_center

theorem negIdentity_ne_one (hodd : (2 : F) ≠ 0) : negIdentity F ≠ 1 := by
  intro h
  have hv := congrArg (fun g : Sp F => (g • e (n := 2) (F := F) 0) (.inl 0)) h
  have he : (-1 : F) = 1 := by simpa [e] using hv
  apply hodd
  calc
    (2 : F) = 1 + 1 := by norm_num
    _ = -1 + 1 := by rw [he]
    _ = 0 := neg_add_cancel 1

theorem card_center (hodd : (2 : F) ≠ 0) : Nat.card (Subgroup.center (Sp F)) = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨negIdentity F, negIdentity_mem_center⟩, ?_, ?_⟩
  · intro h
    exact negIdentity_ne_one hodd (congrArg Subtype.val h).symm
  · ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (mem_center_iff x.val).mp x.property with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

def centerEquivC2 (hodd : (2 : F) ≠ 0) :
    Subgroup.center (Sp F) ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq (card_center hodd) (by simp)

section Covers
variable [Finite F] [hF : Fact (2 < Nat.card F)]

instance : IsQuasisimple (Sp F) := quasisimple hF.out
instance : IsQuasisimple (PSp F) := projective_quasisimple hF.out

@[expose] def quotientCover (F : Type u) [Field F] [Finite F] [Fact (2 < Nat.card F)] :
    Covering (Sp F) (PSp F) where
  toMonoidHom := QuotientGroup.mk' _
  surjective := QuotientGroup.mk'_surjective _

@[simp] theorem quotientCover_toMonoidHom :
    (quotientCover F).toMonoidHom = QuotientGroup.mk' (Subgroup.center (Sp F)) := rfl

@[simp] theorem quotientCover_ker :
    (quotientCover F).toMonoidHom.ker = Subgroup.center (Sp F) :=
  QuotientGroup.ker_mk' _

def kernelEquivC2 (hodd : (2 : F) ≠ 0) :
    (quotientCover F).toMonoidHom.ker ≃* Multiplicative (ZMod 2) := by
  rw [quotientCover_ker]
  exact centerEquivC2 hodd


end Covers

universe v
variable {K : Type v} [Field K]

@[expose] def fieldEquivSp (e : F ≃+* K) : Sp F ≃* Sp K where
  toFun g := ⟨g.val.map e, SymplecticGroup.map_mem g.property e⟩
  invFun g := ⟨g.val.map e.symm, SymplecticGroup.map_mem g.property e.symm⟩
  left_inv g := by apply Subtype.ext; ext i j; exact e.symm_apply_apply _
  right_inv g := by apply Subtype.ext; ext i j; exact e.apply_symm_apply _
  map_mul' g h := by apply Subtype.ext; exact Matrix.map_mul

@[expose] def fieldEquivPSp (e : F ≃+* K) : PSp F ≃* PSp K :=
  QuotientGroup.congr _ _ (fieldEquivSp e) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.centerCongr (fieldEquivSp e) ⟨y, hy⟩).property
    · intro hx
      exact ⟨(fieldEquivSp e).symm x,
        (Subgroup.centerCongr (fieldEquivSp e).symm ⟨x, hx⟩).property,
        (fieldEquivSp e).apply_symm_apply x⟩)

@[simp] theorem fieldEquivPSp_projection (e : F ≃+* K) (g : Sp F) :
    fieldEquivPSp e (QuotientGroup.mk' _ g) = QuotientGroup.mk' _ (fieldEquivSp e g) := rfl

omit [Field F] in
theorem card_gt_two [Finite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : Nat.card F = p) : 2 < Nat.card F := by
  have := hp.two_le
  omega

theorem two_ne_zero [Finite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : Nat.card F = p) : (2 : F) ≠ 0 := by
  let := Fintype.ofFinite F
  let : Fact p.Prime := ⟨hp⟩
  let : CharP F p := charP_of_card_eq_prime (by simpa only [Nat.card_eq_fintype_card] using hcard)
  intro h
  have hd := (CharP.cast_eq_zero_iff F p 2).mp h
  have hlt : 2 < p := by have := hp.two_le; omega
  exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hlt hd

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime
