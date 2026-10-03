module
public import Theory.Character.ConjClassFunction

/-!
# Summing a class function over class representatives

Grouping the group elements by their conjugacy classes weights each value by
the size of its class. This is the class-sum form of character orthogonality.
-/

open scoped BigOperators
noncomputable section

/-- Interchange a finite weighted sum and the first argument of the scalar
product. No character or conjugacy invariance assumption is needed. -/
public theorem sum_scalarProduct_mul {Q ι : Type*} [Fintype Q] (s : Finset ι)
    (χ : ι → ClassFunction Q) (θ : ClassFunction Q) (w : ι → ℂ) :
    ∑ i ∈ s, scalarProduct Q (χ i) θ * w i =
      scalarProduct Q (fun q => ∑ i ∈ s, χ i q * w i) θ := by
  classical
  simp only [scalarProduct]
  simp_rw [mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Sum a class function using any complete, nonrepeating list of representatives. -/
public theorem IsClassFunction.sum_eq_sum_class_representatives
    {G : Type*} [Group G] [Fintype G] {ι : Type*} [Fintype ι]
    {χ : ClassFunction G} (hχ : IsClassFunction χ) (r : ι → G)
    (hr : Function.Bijective (fun i => ConjClasses.mk (r i))) :
    ∑ g : G, χ g = ∑ i : ι, (Nat.card (ConjClasses.mk (r i)).carrier : ℂ) * χ (r i) := by
  classical
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  let f := toConjClassFunction χ hχ
  have hfiber (d : ConjClasses G) :
      Fintype.card {g : G // ConjClasses.mk g = d} = Nat.card d.carrier := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight
      (fun _ => ConjClasses.mem_carrier_iff_mk_eq.symm))
  calc
    ∑ g : G, χ g = ∑ d : ConjClasses G, (Nat.card d.carrier : ℂ) * f d := by
      have h := Fintype.sum_fiberwise' ConjClasses.mk f
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hfiber, f, toConjClassFunction_apply] using h.symm
    _ = ∑ i : ι, (Nat.card (ConjClasses.mk (r i)).carrier : ℂ) * χ (r i) :=
      (Fintype.sum_equiv (Equiv.ofBijective (fun i => ConjClasses.mk (r i)) hr)
        _ _ (fun _ => by simp [f, toConjClassFunction_apply])).symm
