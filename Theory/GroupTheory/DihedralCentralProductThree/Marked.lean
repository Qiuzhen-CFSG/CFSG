module
public import Theory.GroupTheory.DihedralCentralProductThree.Model

/-!
# Marked maps out of the threefold dihedral central product

Three commuting factor maps, agreeing on the central rotations, descend to
the explicit quotient. If their images generate a group of order 128, the
quotient map is an equivalence. The exact kernel and the maps on all three
factors are retained. Intrinsic construction of the factors is separate.

Source: the central-product notation in Aschbacher–Smith 15.3.58(2),
printed pp.1148–1149; the construction follows the checked six-factor model.
-/

namespace DihedralCentralProductThree
open DihedralGroup

variable {P : Type*} [Group P]
  (f : Fin 3 → DihedralGroup 4 →* P)
  (hc : Pairwise fun i j => ∀ x y, Commute (f i x) (f j y))

/-- Multiplication of the three commuting factor images. -/
public noncomputable def productMap : D →* P :=
  MonoidHom.noncommPiCoprod f hc

@[simp] public theorem productMap_single (i : Fin 3) (x : DihedralGroup 4) :
    productMap f hc (Pi.mulSingle i x) = f i x :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

public theorem productMap_surjective (hg : (⨆ i, (f i).range) = ⊤) :
    Function.Surjective (productMap f hc) := by
  apply MonoidHom.range_eq_top.mp
  exact (MonoidHom.noncommPiCoprod_range f).trans hg

public theorem Delta_le_productMap_ker
    (hz : ∀ i, f i (r 2) = f 0 (r 2)) : Delta ≤ (productMap f hc).ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  change productMap f hc (c 0 * c i.succ) = 1
  simp only [map_mul, c, productMap_single, hz]
  rw [← map_mul]
  rw [show (r 2 : DihedralGroup 4) * r 2 = 1 from by decide, map_one]

/-- The quotient map induced by three aligned factor maps. -/
public noncomputable def markedQuotientMap
    (hz : ∀ i, f i (r 2) = f 0 (r 2)) : Model →* P :=
  QuotientGroup.lift Delta (productMap f hc) (Delta_le_productMap_ker f hc hz)

@[simp] public theorem markedQuotientMap_mk
    (hz : ∀ i, f i (r 2) = f 0 (r 2)) (x : D) :
    markedQuotientMap f hc hz (QuotientGroup.mk x) = productMap f hc x := by rfl

public theorem markedQuotientMap_surjective
    (hz : ∀ i, f i (r 2) = f 0 (r 2)) (hg : (⨆ i, (f i).range) = ⊤) :
    Function.Surjective (markedQuotientMap f hc hz) := by
  intro p
  obtain ⟨x, hx⟩ := productMap_surjective f hc hg p
  exact ⟨QuotientGroup.mk x, hx⟩

/-- Recognition with the three concrete factor maps fixed. -/
public noncomputable def markedRecognition [Finite P]
    (hz : ∀ i, f i (r 2) = f 0 (r 2)) (hg : (⨆ i, (f i).range) = ⊤)
    (hP : Nat.card P = 128) : Model ≃* P :=
  MulEquiv.ofBijective (markedQuotientMap f hc hz)
    ((markedQuotientMap_surjective f hc hz hg).bijective_of_nat_card_le
      (by rw [Model_card, hP]; decide))

@[simp] public theorem markedRecognition_single [Finite P]
    (hz : ∀ i, f i (r 2) = f 0 (r 2)) (hg : (⨆ i, (f i).range) = ⊤)
    (hP : Nat.card P = 128) (i : Fin 3) (x : DihedralGroup 4) :
    markedRecognition f hc hz hg hP (QuotientGroup.mk (Pi.mulSingle i x)) = f i x :=
  productMap_single f hc i x

public theorem ker_productMap [Finite P]
    (hz : ∀ i, f i (r 2) = f 0 (r 2)) (hg : (⨆ i, (f i).range) = ⊤)
    (hP : Nat.card P = 128) : (productMap f hc).ker = Delta := by
  apply le_antisymm ?_ (Delta_le_productMap_ker f hc hz)
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply (markedRecognition f hc hz hg hP).injective
  exact hx.trans (map_one _).symm

end DihedralCentralProductThree
