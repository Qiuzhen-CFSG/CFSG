module

public import Theory.Representation.PSL3Two.SmallModules
public import Theory.Representation.BinaryOffender.Basic
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.ElementaryAbelian.Quotient

/-!
# The line radical on two natural SL₃(2) modules

The shear four-group R fixes the plane with last coordinate zero in
each summand. Its fixed space on W ⊕ W consequently has dimension four,
so R is an offender of rank two and fixed codimension two. Within the
diagonal SL₃(2), the pointwise fixer of this fixed space is exactly R:
fixing the first two basis vectors specifies two columns, and determinant
one specifies the remaining diagonal entry.

This does not classify offenders in a Sylow subgroup of the full
normalizer of the diagonal action. In particular its pointwise-fixer
statement concerns SL₃(2), not that larger normalizer.

Source application: Aschbacher–Smith, combined manuscript of 1 March
2004, the doubled-natural branch of 13.6.20, printed p.931.
-/

public section
open Matrix Representation Representation.BinaryOffender Subgroup
namespace BinaryLinearThree.DoubledFixedSpace

/-- The common fixed vectors of the shear four-group on one summand. -/
theorem natural_fixed_iff (x : Vector) :
    (∀ r ∈ R, W r x = x) ↔ x 2 = 0 := by
  constructor
  · intro h
    have he := congrFun (h (shear (Multiplicative.ofAdd (1, 0))) ⟨_, rfl⟩) 0
    change (!![1,0,1; 0,1,0; 0,0,1].mulVec x) 0 = x 0 at he
    have hx : x 0 + x 2 = x 0 := by
      simpa [mulVec, dotProduct, Fin.sum_univ_three] using he
    exact add_left_cancel (hx.trans (add_zero (x 0)).symm)
  · intro hx r hr
    obtain ⟨c, rfl⟩ := hr
    change !![1,0,c.toAdd.1; 0,1,c.toAdd.2; 0,0,1].mulVec x = x
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three, hx]

/-- The fixed space on the doubled module is the product of the two planes. -/
theorem mem_fixedSpace_iff (u : Vector × Vector) :
    u ∈ fixedSpace (W.prod W) R ↔ u.1 2 = 0 ∧ u.2 2 = 0 := by
  constructor
  · intro hu
    exact ⟨(natural_fixed_iff u.1).mp (fun r hr => congrArg Prod.fst (hu ⟨r, hr⟩)),
      (natural_fixed_iff u.2).mp (fun r hr => congrArg Prod.snd (hu ⟨r, hr⟩))⟩
  · intro hu r
    exact Prod.ext ((natural_fixed_iff u.1).mpr hu.1 r r.property)
      ((natural_fixed_iff u.2).mpr hu.2 r r.property)

private def fixedCoordinates : fixedSpace (W.prod W) R ≃
    (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2) where
  toFun u := ((u.val.1 0, u.val.1 1), (u.val.2 0, u.val.2 1))
  invFun c := ⟨(![c.1.1, c.1.2, 0], ![c.2.1, c.2.2, 0]),
    (mem_fixedSpace_iff _).mpr ⟨rfl, rfl⟩⟩
  left_inv u := by
    apply Subtype.ext
    have hu := (mem_fixedSpace_iff u.val).mp u.property
    apply Prod.ext <;> ext i <;> fin_cases i <;> simp [hu.1, hu.2]
  right_inv c := rfl

/-- There are sixteen fixed vectors in the six-dimensional doubled module. -/
theorem card_fixedSpace : Nat.card (fixedSpace (W.prod W) R) = 16 := by
  rw [Nat.card_congr fixedCoordinates]
  simp

theorem finrank_fixedSpace : Module.finrank (ZMod 2) (fixedSpace (W.prod W) R) = 4 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace (W.prod W) R)
  rw [Nat.card_zmod, card_fixedSpace] at hc
  exact (Nat.pow_right_injective (by decide : 1 < 2) hc).symm

theorem fixedCodim_radical : fixedCodim (W.prod W) R = 2 := by
  have hf := fixedCodim_add_finrank (W.prod W) R
  rw [finrank_fixedSpace] at hf
  have hd : Module.finrank (ZMod 2) (Vector × Vector) = 6 := by
    simp [Vector, Matrix.PSL3Two.Fano.Vector, Module.finrank_prod]
  rw [hd] at hf
  omega

/-- The actual shear four-group attains the offender bound on W ⊕ W. -/
theorem radical_isOffender : IsOffender (W.prod W) R := by
  let : IsElementaryAbelian 2 (Multiplicative (ZMod 2 × ZMod 2)) := {
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      decide +kernel }
  let : IsElementaryAbelian 2 R :=
    IsElementaryAbelian.of_surjective shear.rangeRestrict shear.rangeRestrict_surjective
  refine ⟨⟨?_, inferInstance⟩, ?_⟩
  · intro h
    have hc := card_R
    rw [h, Subgroup.card_bot] at hc
    omega
  · rw [fixedCodim_radical, BinaryOffender.rank, card_R]
    decide

private theorem mem_radical_of_fixes_plane (g : Group)
    (hg : ∀ x : Vector, x 2 = 0 → W g x = x) : g ∈ R := by
  have h0 := hg ![1,0,0] rfl
  have h1 := hg ![0,1,0] rfl
  have hc0 (i : Fin 3) : g.val i 0 = (![1,0,0] : Vector) i := by
    have hi := congrFun h0 i
    change (g.val.mulVec ![1,0,0]) i = _ at hi
    simpa [mulVec, dotProduct, Fin.sum_univ_three] using hi
  have hc1 (i : Fin 3) : g.val i 1 = (![0,1,0] : Vector) i := by
    have hi := congrFun h1 i
    change (g.val.mulVec ![0,1,0]) i = _ at hi
    simpa [mulVec, dotProduct, Fin.sum_univ_three] using hi
  have hc2 : g.val 2 2 = 1 := by
    have hd := g.property
    change g.val.det = 1 at hd
    rw [Matrix.det_fin_three] at hd
    simpa [hc0, hc1] using hd
  refine ⟨Multiplicative.ofAdd (g.val 0 2, g.val 1 2), ?_⟩
  apply Subtype.ext
  change !![1,0,g.val 0 2; 0,1,g.val 1 2; 0,0,1] = g.val
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc0, hc1, hc2]

/-- Within the diagonal component, R is the full pointwise fixer of C(W ⊕ W)(R). -/
theorem fixes_fixedSpace_iff (g : Group) :
    (∀ u ∈ fixedSpace (W.prod W) R, (W.prod W) g u = u) ↔ g ∈ R := by
  constructor
  · intro hg
    apply mem_radical_of_fixes_plane g
    intro x hx
    exact congrArg Prod.fst (hg (x, 0) ((mem_fixedSpace_iff _).mpr ⟨hx, rfl⟩))
  · intro hg u hu
    exact hu ⟨g, hg⟩

end BinaryLinearThree.DoubledFixedSpace
