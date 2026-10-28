module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.FieldCentralizer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.Structure

/-!
# Full centralizers of linear four-groups

The linear part of a four-group centralizer is the actor itself. The
quadratic field image has order at most two, so two nonlinear centralizer
elements differ by an element of the actor. This proves that the full
centralizer is abelian, without identifying it with the actor.

Consequently ambient tau meets the linear layer in exactly the actor, and
centralizes every element of its full centralizer. The field-of-nine
consumer uses this to establish E0 for field-involution centralizers even
though the linear actor does not contain the field involution.

Source: Aschbacher–Smith E.1.1–2 and E.1.14(6), pp.209–210, 214;
the linear self-centralizer calculation is in `LinearWitnesses.Structure`.
-/

public section
open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors
variable {F : Type*} [Field F] [Finite F] [Finite (PGammaL2 F)]

/-- The literal linear intersection of the full centralizer. -/
theorem centralizer_inf_linear {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p ^ 2) (A : Subgroup (PGammaL2 F))
    (hA : IsElementaryAbelian 2 A) (hr : Group.rank A = 2)
    (hAL : A ≤ pGammaL2PGLRange F) :
    centralizer (A : Set (PGammaL2 F)) ⊓ pGammaL2PGLRange F = A := by
  let L := pGammaL2PGLRange F
  let D := A.subgroupOf L
  let := hA
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.subgroupOf hAL
  have hD : Group.rank D = 2 :=
    (Group.rank_congr (subgroupOfEquivOfLe hAL)).trans hr
  have hmodel : Nonempty (L ≃* PSL2 F) ∨ Nonempty (L ≃* PGL2 F) :=
    Or.inr ⟨(pGammaL2PGLRangeEquiv F).symm⟩
  have hq : IsOddPrimePower (Nat.card F) := ⟨p, 2, hp, ho, by decide, hF⟩
  have hfour := LinearWitnesses.large_actor_isKleinFour hq hmodel D (by omega)
  have hc := LinearWitnesses.kleinFour_centralizer_eq_self hq hmodel D hfour
  apply le_antisymm
  · rintro x ⟨hx, hxL⟩
    have hh : (⟨x, hxL⟩ : L) ∈ centralizer (D : Set L) := by
      rw [mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (mem_centralizer_iff.mp hx y hy)
    rw [hc] at hh
    exact hh
  · exact le_inf (Subgroup.le_centralizer A) hAL

/-- The full centralizer is abelian; it need not equal the actor. -/
theorem centralizer_commutative {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hne : σ ≠ 1)
    (A : Subgroup (PGammaL2 F)) (hA : IsElementaryAbelian 2 A)
    (hr : Group.rank A = 2) (hAL : A ≤ pGammaL2PGLRange F) :
    IsMulCommutative (centralizer (A : Set (PGammaL2 F))) := by
  have hc := centralizer_inf_linear hp ho hF A hA hr hAL
  have hmem (x : PGammaL2 F) : x ∈ pGammaL2PGLRange F ↔ x.right = 1 := by
    rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom]
    rfl
  refine ⟨⟨?_⟩⟩
  intro x y
  apply Subtype.ext
  by_cases hx : x.val.right = 1
  · have hxA : x.val ∈ A := hc.le ⟨x.property, (hmem x).mpr hx⟩
    exact mem_centralizer_iff.mp y.property x hxA
  by_cases hy : y.val.right = 1
  · have hyA : y.val ∈ A := hc.le ⟨y.property, (hmem y).mpr hy⟩
    exact (mem_centralizer_iff.mp x.property y hyA).symm
  have he : x.val.right = y.val.right :=
    ((fieldAut_eq_one_or hp hF σ hne x.val.right).resolve_left hx).trans
      ((fieldAut_eq_one_or hp hF σ hne y.val.right).resolve_left hy).symm
  have hdL : y.val * x.val⁻¹ ∈ pGammaL2PGLRange F := by
    apply (hmem _).mpr
    simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right, he, mul_inv_cancel]
  have hdA : y.val * x.val⁻¹ ∈ A := hc.le
    ⟨(centralizer (A : Set (PGammaL2 F))).mul_mem y.property
      ((centralizer (A : Set (PGammaL2 F))).inv_mem x.property), hdL⟩
  have hh := mem_centralizer_iff.mp x.property _ hdA
  calc
    x.val * y.val = (x.val * (y.val * x.val⁻¹)) * x.val := by group
    _ = ((y.val * x.val⁻¹) * x.val) * x.val := by rw [hh]
    _ = y.val * x.val := by group

/-- Only the linear part of ambient tau is necessarily the actor. -/
theorem tau_inf_linear {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    (T : Sylow 2 (PGammaL2 F)) (A : Subgroup (PGammaL2 F))
    (hA : IsElementaryAbelian 2 A) (hr : Group.rank A = 2)
    (hAL : A ≤ pGammaL2PGLRange F) (hAT : A ≤ (T : Subgroup _)) :
    tau (T : Subgroup _) A ⊓ pGammaL2PGLRange F = A := by
  rw [full_tau_eq_inf_centralizer hp ho hF hlarge, inf_assoc,
    centralizer_inf_linear hp ho hF A hA hr hAL, inf_eq_right.mpr hAT]

/-- Every element centralizing a linear four-group also centralizes its full tau. -/
theorem tau_le_centralizer_of_mem {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    (σ : F ≃+* F) (hne : σ ≠ 1)
    (T : Sylow 2 (PGammaL2 F)) (A : Subgroup (PGammaL2 F))
    (hA : IsElementaryAbelian 2 A) (hr : Group.rank A = 2)
    (hAL : A ≤ pGammaL2PGLRange F)
    (x : PGammaL2 F) (hx : x ∈ centralizer (A : Set (PGammaL2 F))) :
    tau (T : Subgroup _) A ≤ centralizer ({x} : Set (PGammaL2 F)) := by
  let := centralizer_commutative hp ho hF σ hne A hA hr hAL
  rw [full_tau_eq_inf_centralizer hp ho hF hlarge]
  rintro y ⟨_, hy⟩
  rw [mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (IsMulCommutative.is_comm.comm
    (⟨y, hy⟩ : centralizer (A : Set (PGammaL2 F))) ⟨x, hx⟩)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors
