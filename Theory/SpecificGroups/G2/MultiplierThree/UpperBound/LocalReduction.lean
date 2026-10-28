module

public import Theory.SpecificGroups.G2.MultiplierThree.PrimeSupport
public import Theory.SpecificGroups.G2.MultiplierThree.UpperBound.RootDefect
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.Involution

/-!
# Local calculations sufficient for the G₂(3) multiplier upper bound

The involution centralizer has odd index, and the positive unipotent
subgroup has index prime to three. A lift of the first with odd kernel
excludes two from the universal kernel order. Six additive root lifts whose product
errors are powers of one central element with cube one construct a lift
of the second with kernel of order at most three. Central transfer then
excludes nine. The proved prime-support theorem finishes the upper bound.

The local lift and the cyclic root-defect calculation remain explicit
inputs here. These conditional results do not yet establish the source
multiplier row or its unconditional upper bound.

Source: Aschbacher–Smith I.1.2 and I.1.4(2), printed pp.407–408
(PDF pp.418–419); GLS3 §6.1, Tables 6.1.2–6.1.3, citing Griess [Gr1].
-/

namespace Atlas.G2.FiniteCover.MultiplierThree
open PerfectCentralCovering
open MultiplierOrdinary

/-- The marked involution centralizer contains a Sylow two-subgroup. -/
public theorem not_two_dvd_involutionCentralizer_index :
    ¬ 2 ∣ TernaryLocals.Involution.P.index := by
  have h := TernaryLocals.Involution.P.card_mul_index
  rw [TernaryLocals.Involution.card, card_Model] at h
  norm_num at h
  have hi : TernaryLocals.Involution.P.index = 7371 := by omega
  rw [hi]
  decide

variable {E : Type*} [Group E] [Finite E]

/-- A lift of the literal involution centralizer with odd kernel removes
the two-primary global kernel. A cubic local kernel is permitted, as
required by the orthogonal-root commutators in GLS3 §6.3. -/
public theorem not_two_dvd_kernel_of_involution_lift
    (f : Cover E (Model (ZMod 3))) (H : Subgroup E)
    (hH : H.map f.toMonoidHom = TernaryLocals.Involution.P)
    (hodd : ¬ 2 ∣ Nat.card (H ⊓ f.toMonoidHom.ker : Subgroup E)) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker :=
  f.not_dvd_kernel_of_local_lift H _ hH not_two_dvd_involutionCentralizer_index hodd

/-- A local lift of the literal unipotent subgroup with kernel of order
at most three bounds the three-primary part of the global kernel. -/
public theorem not_nine_dvd_kernel_of_unipotent_lift
    (f : Cover E (Model (ZMod 3))) (H : Subgroup E)
    (hH : H.map f.toMonoidHom = unipotent (K := ZMod 3))
    (hb : Nat.card (H ⊓ f.toMonoidHom.ker : Subgroup E) ≤ 3) :
    ¬ 9 ∣ Nat.card f.toMonoidHom.ker := by
  have hi : ¬ 3 ∣ (unipotent (K := ZMod 3)).index := not_dvd_unipotent_index
  exact f.not_primePower_dvd_kernel_of_local_bound (p := 3) H _ hH hi
    (n := 2) (by omega)

/-- The exceptional root-relation calculation may retain one cyclic
central error of exponent three; complete splitting is unnecessary. -/
public theorem not_nine_dvd_kernel_of_cubic_root_defect
    (f : Cover E (Model (ZMod 3))) (L : RootSections f.toMonoidHom)
    (z : E) (hz : z ∈ f.toMonoidHom.ker) (hz3 : z ^ 3 = 1)
    (hL : L.ProductCompatibleModulo (Subgroup.zpowers z)) :
    ¬ 9 ∣ Nat.card f.toMonoidHom.ker := by
  have hN : Subgroup.zpowers z ≤ f.toMonoidHom.ker := Subgroup.zpowers_le.mpr hz
  have hNz := hN.trans f.ker_le_center
  let : (Subgroup.zpowers z).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_center_iff.mp (hNz hx) g, mul_inv_cancel_right]
    exact hx⟩
  obtain ⟨H, hH, hker⟩ := L.exists_local_lift_of_product_modulo _ hN hL
  apply not_nine_dvd_kernel_of_unipotent_lift f H hH
  rw [hker, Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (by decide) hz3

end Atlas.G2.FiniteCover.MultiplierThree
