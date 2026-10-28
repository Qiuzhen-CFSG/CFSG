module
public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow.RadicalBounds.Pairing

/-!
# Commuting subgroups of the arms radical

Quotienting the highest-root coordinate gives K² ⊕ k². The genuine
commutator is its nondegenerate trace hyperbolic form. A commuting family's
image has isotropic k-span, of order at most q⁴. Restoring the highest-root
coordinate gives the bound q⁵. No linearity or normality of the family is
assumed, and the argument includes q = 2.

The proof uses the published coordinate equivalence through the actual
central quotient, then transfers to `Parabolics.radical` by its proved
subgroup equality.

Source: GLS3 2.4.5(b)(4) and §2.6 (`refs/KGroup/GLS3/chapter2.tex`),
for the triality rank used on printed p.356 of `refs/quasithin.pdf`.
-/

public section
noncomputable section
open Triality.Standard.RadicalCoordinates
open Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.Parabolics
open scoped commutatorElement
namespace Triality.Standard.TwoRank.RadicalBounds

private abbrev ArmsVector (P : Parameters) :=
  (ExtensionField P × fixedField P) × (ExtensionField P × fixedField P)

private def armsVector (P : Parameters) (v : ArmsParameters P) : ArmsVector P :=
  ((v.1 0, v.2 0), (v.1 1, v.2 1))

private theorem armsVector_pair (P : Parameters) (v w : ArmsParameters P) :
    hyperbolic (extendedTrace P) (armsVector P v) (armsVector P w) =
      armsCommutator P v w := by
  simp only [hyperbolic_apply, extendedTrace_apply, armsVector, armsCommutator, armsCocycle]
  ring

/-- Any commuting family in the genuine arms radical has at most q⁵ elements. -/
theorem card_arms_commuting (P : Parameters) (hp : P.prime = 2)
    {ι : Type*} [Finite ι] (f : ι → armsSubgroup P) (hinj : Function.Injective f)
    (hcomm : ∀ i j, Commute (f i) (f j)) : Nat.card ι ≤ P.q ^ 5 := by
  let v : ι → ArmsParameters P := fun i => (armsEquiv P hp).symm (f i)
  let x : ι → ArmsVector P := fun i => armsVector P (v i)
  let W := Submodule.span (fixedField P) (Set.range x)
  have hpair (i j : ι) : hyperbolic (extendedTrace P) (x i) (x j) = 0 := by
    rw [armsVector_pair]
    apply (armsEquiv_central_eq_one_iff P hp _).mp
    rw [← armsEquiv_commutator P hp]
    simp only [v, Equiv.apply_symm_apply]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm i j).eq
  have hsq : Nat.card W ^ 2 ≤ P.q ^ 8 := by
    have h := card_span_sq_le (hyperbolic (extendedTrace P))
      (hyperbolic_nondegenerate _ (extendedTrace_nondegenerate P hp))
      (Set.range x) (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hpair i j)
    simpa only [ArmsVector, Nat.card_prod, card_extensionField, card_fixedField,
      ← pow_succ, ← pow_add] using h
  have hW : Nat.card W ≤ P.q ^ 4 := by
    have he : P.q ^ 8 = (P.q ^ 4) ^ 2 := by ring
    rw [he] at hsq
    exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hsq
  let g : ι → W × fixedField P := fun i =>
    (⟨x i, Submodule.subset_span ⟨i, rfl⟩⟩, (v i).2 2)
  have hg : Function.Injective g := by
    intro i j hij
    have hx : x i = x j := congrArg (fun z : W × fixedField P => z.1.val) hij
    have hz : (v i).2 2 = (v j).2 2 := congrArg Prod.snd hij
    have hv : v i = v j := by
      apply Prod.ext
      · funext k
        fin_cases k
        · exact congrArg (fun z : ArmsVector P => z.1.1) hx
        · exact congrArg (fun z : ArmsVector P => z.2.1) hx
      · funext k
        fin_cases k
        · exact congrArg (fun z : ArmsVector P => z.1.2) hx
        · exact congrArg (fun z : ArmsVector P => z.2.2) hx
        · exact hz
    exact hinj ((armsEquiv P hp).symm.injective hv)
  calc
    Nat.card ι ≤ Nat.card (W × fixedField P) := Nat.card_le_card_of_injective g hg
    _ = Nat.card W * P.q := by rw [Nat.card_prod, card_fixedField]
    _ ≤ P.q ^ 4 * P.q := Nat.mul_le_mul_right _ hW
    _ = P.q ^ 5 := by ring

/-- The arms-radical branch of the triality elementary-subgroup bound. -/
theorem arms_radical_card_le (P : Parameters) (hp : P.prime = 2)
    (E : Subgroup (radical P .arms)) [IsElementaryAbelian 2 E] :
    Nat.card E ≤ P.q ^ 5 := by
  let e : radical P .arms ≃* armsSubgroup P :=
    MulEquiv.subgroupCongr (radical_eq_descendedRootSubgroup P hp .arms)
  let : CommGroup E := IsMulCommutative.instCommGroup
  apply card_arms_commuting P hp (fun x : E => e x.val)
    (e.injective.comp Subtype.val_injective)
  intro x y
  show e x.val * e y.val = e y.val * e x.val
  rw [← map_mul, ← map_mul]
  exact congrArg e (congrArg (fun z : E => z.val) (mul_comm x y))

end Triality.Standard.TwoRank.RadicalBounds
