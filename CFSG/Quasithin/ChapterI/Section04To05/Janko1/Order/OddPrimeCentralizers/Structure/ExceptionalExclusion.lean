module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.AlternativesData
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.FourCentralizers
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.FixedInvolution
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.Transport
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.LocalGeometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.ConjugateCentralizer
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.NormalizerSylow

/-!
# Assembly of the exceptional order-27 contradiction

Let Y=C_A(X)X and Z=N_{N_G(A)}(Y). The order-three actor fixes an
involution. The conjugate-centralizer calculation identifies C_G(Y)
with a conjugate B of A. Normalizer functoriality puts Z in N_G(B),
and the local calculation makes both A and B normalize Z. Since Y≤Z,
C_G(Z)≤B is a three-group. A normal Sylow three-subgroup of N_G(Z)
therefore contains both A and B. Their common ambient Sylow subgroup
has a unique abelian subgroup of order 27, forcing A=B, whereas X≤B
and X is not contained in A.

The conditional assembly retains the local calculations as explicit inputs.
The final theorem `not_exceptionalOddNormalizer` supplies all of them from
the local geometry, conjugate-centralizer, and normalizer-Sylow proofs.
Source: Bender, *Finite groups with large subgroups* (1974), (4.1), p.225.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- Bender's final contradiction, conditional on the three remaining
source calculations. Final assembly must discharge all four producer
arguments (the first two belong to the same local calculation). -/
public theorem not_exceptionalOddNormalizer_of_local_steps (h : Janko1CentralizerData G)
    (localGeometry : ∀ (A : Subgroup G), ExceptionalOddNormalizer A →
      ∀ (V X : Subgroup G), IsElementaryAbelian 2 V → Nat.card V = 4 →
        Nat.card X = 3 → X ≤ normalizer (V : Set G) →
        normalizer (A : Set G) = A ⊔ (V ⊔ X) → ExceptionalLocalGeometry A X)
    (sylowControl : ∀ (A : Subgroup G), ExceptionalOddNormalizer A →
      ExceptionalSylowControl A)
    (conjugateCentralizer : ∀ (x : G), x ∈ centralizer ({h.z} : Set G) →
      orderOf x = 3 → ∀ (A : Subgroup G), OddCentralizerComplement h x A →
      ExceptionalOddNormalizer A → ∀ (X : Subgroup G), Nat.card X = 3 →
      (∃ t : G, orderOf t = 2 ∧ X ≤ centralizer ({t} : Set G)) →
      Nat.card (exceptionalPlane A X) = 9 →
      ∃ g : G, A.map (MulAut.conj g).toMonoidHom =
        centralizer (exceptionalPlane A X : Set G) ∧
        exceptionalPlane A X ≤ A.map (MulAut.conj g).toMonoidHom)
    (normalizerSylow : ∀ (D : Subgroup G), Nat.card D = 27 →
      ¬ IsMulCommutative D → IsPGroup 3 (centralizer (D : Set G)) →
      ∃ P : Sylow 3 (normalizer (D : Set G)), (P : Subgroup (normalizer (D : Set G))).Normal)
    (x : G) (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = 3)
    (A : Subgroup G) (a : OddCentralizerComplement h x A)
    (e : ExceptionalOddNormalizer A) : False := by
  obtain ⟨V, X, hV, hVcard, hXcard, hXV, hN⟩ := e.normalizer_decomposition
  have geometry := localGeometry A e V X hV hVcard hXcard hXV hN
  have control := sylowControl A e
  obtain ⟨t, _, ht, hXt⟩ := h.three_normalizing_four_fixes_involution V X hVcard hXcard hXV
  obtain ⟨g, hg, hYB⟩ := conjugateCentralizer x hxC hx A a e X hXcard
    ⟨t, ht, hXt⟩ geometry.plane_card
  let B := A.map (MulAut.conj g).toMonoidHom
  have eB : ExceptionalOddNormalizer B := e.map (MulAut.conj g)
  let Y := exceptionalPlane A X
  let Z := exceptionalPlaneNormalizer A X
  have hZNA : Z ≤ normalizer (A : Set G) := inf_le_left
  have hZNB : Z ≤ normalizer (B : Set G) := by
    change Z ≤ normalizer (A.map (MulAut.conj g).toMonoidHom : Set G)
    rw [hg]
    exact inf_le_right.trans (normalizer_le_normalizer_centralizer Y)
  have hAZ : A ≤ normalizer (Z : Set G) := control.normalizes_nonabelian Z hZNA
    geometry.normalizer_card geometry.normalizer_nonabelian
  have hBZ : B ≤ normalizer (Z : Set G) :=
    (sylowControl B eB).normalizes_nonabelian Z hZNB
      geometry.normalizer_card geometry.normalizer_nonabelian
  have hXN : X ≤ normalizer (A : Set G) := by
    rw [hN]
    exact le_sup_of_le_right le_sup_right
  have hYN : Y ≤ normalizer (A : Set G) := sup_le
    (inf_le_left.trans A.le_normalizer) hXN
  have hYZ : Y ≤ Z := le_inf hYN Y.le_normalizer
  have hCZB : centralizer (Z : Set G) ≤ B := by
    change centralizer (Z : Set G) ≤ A.map (MulAut.conj g).toMonoidHom
    rw [hg]
    exact centralizer_le hYZ
  have hBp : IsPGroup 3 B := IsPGroup.of_card (n := 3) (by simpa using eB.card)
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by simpa using e.card)
  obtain ⟨P, hPN⟩ := normalizerSylow Z geometry.normalizer_card
    geometry.normalizer_nonabelian (hBp.to_le hCZB)
  let N := normalizer (Z : Set G)
  let _ : (P : Subgroup N).Normal := hPN
  have leP (D : Subgroup N) (hD : IsPGroup 3 D) : D ≤ (P : Subgroup N) := by
    apply sup_eq_right.mp
    exact P.is_maximal' (hD.to_sup_of_normal_right P.isPGroup') le_sup_right
  have hAP : A ≤ (P : Subgroup N).map N.subtype := by
    intro w hw
    exact ⟨⟨w, hAZ hw⟩, leP (A.subgroupOf N) hAp.comap_subtype hw, rfl⟩
  have hBP : B ≤ (P : Subgroup N).map N.subtype := by
    intro w hw
    exact ⟨⟨w, hBZ hw⟩, leP (B.subgroupOf N) hBp.comap_subtype hw, rfl⟩
  obtain ⟨S, hS⟩ := (P.isPGroup'.map N.subtype).exists_le_sylow
  let _ := eB.elementary
  have hBA : B = A := control.unique_abelian S (hAP.trans hS) B
    (hBP.trans hS) inferInstance eB.card
  apply geometry.outside
  exact (show X ≤ Y from le_sup_right).trans (hYB.trans hBA.le)

/-- The elementary abelian order-27 configuration in Bender (4.1) cannot
occur for the odd complement of an element of order three in `C_G(z)`.
All intermediate local calculations in the conditional assembly are
discharged from the original centralizer data and exceptional normalizer. -/
public theorem not_exceptionalOddNormalizer (h : Janko1CentralizerData G)
    (x : G) (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = 3)
    (A : Subgroup G) (a : OddCentralizerComplement h x A)
    (e : ExceptionalOddNormalizer A) : False :=
  h.not_exceptionalOddNormalizer_of_local_steps
    h.exceptional_localGeometry h.exceptional_sylowControl
    h.exceptional_conjugate_centralizer h.normalizerSylow_of_nonabelian_order27
    x hxC hx A a e

end CFSG.Quasithin.Janko1CentralizerData
