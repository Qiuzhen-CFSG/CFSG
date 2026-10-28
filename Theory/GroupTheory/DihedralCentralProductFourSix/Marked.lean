module
public import Theory.GroupTheory.DihedralCentralProductFourSix.Model

/-!
# Assembling marked dihedral factors

Commuting factor maps with aligned central involutions descend from the literal
direct product to its central-product quotient. Generation gives surjectivity;
the structurally computed quotient order gives injectivity. The resulting
equivalence retains each original factor map and identifies the exact kernel.

Source: Aschbacher–Smith 8.2.12, printed p.722 (PDF p.739); the assembly is
the uniform version of `DihedralCentralProductThree.Marked`.
-/

namespace DihedralCentralProductFourSix
open DihedralGroup

variable {P : Type*} [Group P] {n : ℕ}
  (f : Fin (n + 1) → DihedralGroup 4 →* P)
  (hc : Pairwise fun i j => ∀ x y, Commute (f i x) (f j y))

/-- Multiplication of the commuting factor images. -/
public noncomputable def productMap : D n →* P :=
  MonoidHom.noncommPiCoprod f hc

@[simp] public theorem productMap_single (i : Fin (n + 1)) (x : DihedralGroup 4) :
    productMap f hc (Pi.mulSingle i x) = f i x :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

public theorem productMap_surjective (hg : (⨆ i, (f i).range) = ⊤) :
    Function.Surjective (productMap f hc) := by
  apply MonoidHom.range_eq_top.mp
  exact (MonoidHom.noncommPiCoprod_range f).trans hg

public theorem Delta_le_productMap_ker
    (hz : ∀ i, f i (r 2) = f 0 (r 2)) : Delta n ≤ (productMap f hc).ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  change productMap f hc (c 0 * c i.succ) = 1
  simp only [map_mul, c, productMap_single, hz]
  rw [← map_mul]
  rw [show (r 2 : DihedralGroup 4) * r 2 = 1 from by decide, map_one]

/-- The quotient map induced by the aligned factor maps. -/
public noncomputable def markedQuotientMap
    (hz : ∀ i, f i (r 2) = f 0 (r 2)) : Model n →* P :=
  QuotientGroup.lift (Delta n) (productMap f hc) (Delta_le_productMap_ker f hc hz)

@[simp] public theorem markedQuotientMap_mk
    (hz : ∀ i, f i (r 2) = f 0 (r 2)) (x : D n) :
    markedQuotientMap f hc hz (QuotientGroup.mk x) = productMap f hc x := by rfl

public theorem markedQuotientMap_surjective
    (hz : ∀ i, f i (r 2) = f 0 (r 2)) (hg : (⨆ i, (f i).range) = ⊤) :
    Function.Surjective (markedQuotientMap f hc hz) := by
  intro p
  obtain ⟨x, hx⟩ := productMap_surjective f hc hg p
  exact ⟨QuotientGroup.mk x, hx⟩

/-- Recognition with every concrete factor map fixed. -/
public noncomputable def markedRecognition [Finite P]
    (hz : ∀ i, f i (r 2) = f 0 (r 2)) (hg : (⨆ i, (f i).range) = ⊤)
    (hP : Nat.card P = 2 ^ (1 + 2 * (n + 1))) : Model n ≃* P :=
  MulEquiv.ofBijective (markedQuotientMap f hc hz)
    ((markedQuotientMap_surjective f hc hz hg).bijective_of_nat_card_le
      (by rw [Model_card, hP]))

@[simp] public theorem markedRecognition_single [Finite P]
    (hz : ∀ i, f i (r 2) = f 0 (r 2)) (hg : (⨆ i, (f i).range) = ⊤)
    (hP : Nat.card P = 2 ^ (1 + 2 * (n + 1))) (i : Fin (n + 1)) (x : DihedralGroup 4) :
    markedRecognition f hc hz hg hP (QuotientGroup.mk (Pi.mulSingle i x)) = f i x :=
  productMap_single f hc i x

public theorem ker_productMap [Finite P]
    (hz : ∀ i, f i (r 2) = f 0 (r 2)) (hg : (⨆ i, (f i).range) = ⊤)
    (hP : Nat.card P = 2 ^ (1 + 2 * (n + 1))) : (productMap f hc).ker = Delta n := by
  apply le_antisymm ?_ (Delta_le_productMap_ker f hc hz)
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply (markedRecognition f hc hz hg hP).injective
  exact hx.trans (map_one _).symm

end DihedralCentralProductFourSix
