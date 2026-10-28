module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.RootQuotient
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.OddCore.Bounds
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.OddCore.FiveCentralizer
public import Theory.GroupTheory.CoprimeQuotientNormalizer

/-!
# The odd-core identification from Held's five-element centralizer

The four-group bound puts the odd core of the full root centralizer at
order at most 81 and shows that every five-element fixes it pointwise.
Consequently a five-element centralizer whose order is not divisible by
nine forces this core to equal the central root subgroup of order three.
The actual root quotient then has trivial odd core.

The final two theorems discharge the five-element premise using Held 5.3.
They identify the odd core under the finite simple local hypotheses and
the explicit order-72 intersection hypothesis from the local dihedral
geometry. Constructing that intersection order remains with its separate
source owner; neither quotient recognition nor a root factor is assumed.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemmas 5.3–5.4, printed pp.236–237.
-/

open Subgroup

namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e)

/-- The precise consequence of Held 5.3 needed after the four-group bound:
one order-five element of A has centralizer whose order is not divisible by nine. -/
public theorem oddCore_eq_rootKernel_of_five_centralizer [Finite G]
    (hY : Nat.card (centralizer ({pi D e * mu D e} : Set G) ⊓
      rootCentralizer D e L : Subgroup G) = 72)
    (hfive : ∃ w ∈ L.A, orderOf w = 5 ∧
      ¬ 9 ∣ Nat.card (centralizer ({w} : Set G))) :
    pPrimeCore 2 (rootCentralizer D e L) = rootKernel D e L := by
  obtain ⟨w, hwA, hw, hwC⟩ := hfive
  let B := rootCentralizer D e L
  let K := pPrimeCore 2 B
  let wB : B := ⟨w, A_le_rootCentralizer D e L hwA⟩
  have hwB : orderOf wB = 5 := (orderOf_coe wB).symm.trans hw
  have hfix := OddCore.five_centralizes D e L hY wB hwB
  let j : K →* centralizer ({w} : Set G) :=
    { toFun := fun x => ⟨x.val.val, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hfix x x.property).symm.eq)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hinj : Function.Injective j := by
    intro x y h
    have hh := congrArg (fun z : centralizer ({w} : Set G) => (z : G)) h
    exact Subtype.ext (Subtype.ext hh)
  have hdiv := card_dvd_of_injective j hinj
  obtain ⟨n, hn⟩ := (OddCore.three_group_bound D e L hY).1.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra! h
    exact hwC ((show 9 ∣ Nat.card K from by
      rw [hn]; exact Nat.pow_dvd_pow 3 h).trans hdiv)
  have hKle : Nat.card K ≤ 3 := by
    rw [hn]
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 3) hnle
  exact (eq_of_le_of_card_ge (rootKernel_le_oddCore D e L)
    (by rw [rootKernel_card]; exact hKle)).symm

/-- The existing quotient by the central root is odd-core-free once the
source five-element centralizer consequence has been supplied. -/
public theorem rootQuotient_oddCore_eq_bot_of_five_centralizer [Finite G]
    (hY : Nat.card (centralizer ({pi D e * mu D e} : Set G) ⊓
      rootCentralizer D e L : Subgroup G) = 72)
    (hfive : ∃ w ∈ L.A, orderOf w = 5 ∧
      ¬ 9 ∣ Nat.card (centralizer ({w} : Set G))) :
    pPrimeCore 2 (rootQuotient D e L) = ⊥ := by
  let q := QuotientGroup.quotientMulEquivOfEq
    (oddCore_eq_rootKernel_of_five_centralizer D e L hY hfive)
  have h := pPrimeCore_map_iso 2 q
  rw [pPrimeCore_quotient_pPrimeCore_eq_bot, Subgroup.map_bot] at h
  exact h.symm

/-- Held 5.4: the odd core of the full root centralizer is its central
root subgroup. The order-72 intersection is the only additional local
premise; the required five-element centralizer bound is supplied by 5.3. -/
public theorem oddCore_eq_rootKernel [Finite G] [IsSimpleGroup G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hcentralizer : Nat.card (centralizer ({D.a10NoncentralInvolution e} : Set G)) = 2880)
    (hY : Nat.card (centralizer ({pi D e * mu D e} : Set G) ⊓
      rootCentralizer D e L : Subgroup G) = 72) :
    pPrimeCore 2 (rootCentralizer D e L) = rootKernel D e L := by
  exact oddCore_eq_rootKernel_of_five_centralizer D e L hY
    (OddCore.exists_five_centralizer_not_nine D e L hfusion hcentralizer)

/-- The literal quotient of the full root centralizer by the central root
has trivial odd core under the source hypotheses and the order-72 input. -/
public theorem rootQuotient_oddCore_eq_bot [Finite G] [IsSimpleGroup G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hcentralizer : Nat.card (centralizer ({D.a10NoncentralInvolution e} : Set G)) = 2880)
    (hY : Nat.card (centralizer ({pi D e * mu D e} : Set G) ⊓
      rootCentralizer D e L : Subgroup G) = 72) :
    pPrimeCore 2 (rootQuotient D e L) = ⊥ := by
  let q := QuotientGroup.quotientMulEquivOfEq
    (oddCore_eq_rootKernel D e L hfusion hcentralizer hY)
  have h := pPrimeCore_map_iso 2 q
  rw [pPrimeCore_quotient_pPrimeCore_eq_bot, Subgroup.map_bot] at h
  exact h.symm

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor
