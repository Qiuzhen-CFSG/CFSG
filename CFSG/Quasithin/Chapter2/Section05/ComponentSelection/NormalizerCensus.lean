module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSetup
public import CFSG.Quasithin.Chapter1.Section01Inheritance

/-!
# The core normalizer in the component-selection argument

Write H as the intersection of the normalizers of its two-subgroups B_i.
If O2(H) lies in Q = O2(H_U), every B_i lies in Q. The relative normalizer
N_H(Q) is therefore an intersection of relative normalizers inside the
characteristic-two group N_G(Q), so it too has characteristic two.

When every H_U-invariant two-subgroup of H lies in Q, the two-core of this
normalizer is exactly Q. Consequently an element of H centralizing Q lies
in Q. Applied to the original central involution after Q is placed in S,
this supplies the nonzero marker used by the component projections. The
saturation hypothesis is precisely the stated invariant-subgroup hypothesis
of 2.5.3(3); its construction from a maximal local pair remains with the
component-selection assembly.

Source: Aschbacher--Smith, Lemma 2.5.3(1,3--4), printed pp.551--553.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup
variable {G : Type*} [Group G] [Finite G]
variable {M H U HU : Subgroup G}

/-- Original 2.5.3(1), with the actual local pair and finite normalizer
intersection. Every relative characteristic-two hypothesis is constructed. -/
theorem lemma_2_5_3_one
    (hEven : IsEvenCharacteristic G) (hM : M ∈ Chapter1.He G)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hH : H = ⨅ i, normalizer (B i : Set G))
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hcore : twoCore H ≤ twoCore HU) :
    H ⊓ normalizer (twoCore HU : Set G) ∈ Chapter1.He G := by
  let N := normalizer (twoCore HU : Set G)
  let A := H ⊓ N
  have hHN (i : Fin n) : H ≤ normalizer (B i : Set G) := by
    rw [hH]
    exact iInf_le _ i
  have hBQ (i : Fin n) : B i ≤ twoCore HU :=
    (le_pCoreIn_of_normalizes (hp i) (hBH i) (hHN i)).trans hcore
  have hBA (i : Fin n) : B i ≤ A :=
    le_inf (hBH i) ((hBQ i).trans (twoCore HU).le_normalizer)
  have hNe : N ∈ Chapter1.He G := (lemma_2_3_8_2 hEven hM hpair).2.2
  apply Chapter1.lemma_1_1_3_3 hNe (show A ≤ N from inf_le_right) B hp hBA
  · intro i j _
    exact le_inf (hBA j) ((hBH j).trans (hHN i))
  · change H ⊓ N = N ⊓ ⨅ i, normalizer (B i : Set G)
    rw [← hH, inf_comm]

omit [Finite G] in
/-- Saturation identifies the literal relative-normalizer core. This is
valid in both the component-present and component-free source branches. -/
theorem core_normalizer_eq_of_saturation
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU) :
    twoCore (H ⊓ normalizer (twoCore HU : Set G)) = twoCore HU := by
  let A := H ⊓ normalizer (twoCore HU : Set G)
  have hHUA : HU ≤ A := le_inf hpair.2 (le_normalizer_twoCore HU)
  apply le_antisymm
  · exact hsat (twoCore A) ((pCoreIn_le 2 A).trans inf_le_left)
      (isPGroup_pCoreIn 2 A) (hHUA.trans (le_normalizer_twoCore A))
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 HU)
      ((pCoreIn_le 2 HU).trans hHUA) inf_le_right

/-- The source's saturation places every H-element centralizing Q inside
Q, using the proved characteristic-two core normalizer. -/
theorem centralizer_le_core_of_saturation
    (hEven : IsEvenCharacteristic G) (hM : M ∈ Chapter1.He G)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hH : H = ⨅ i, normalizer (B i : Set G))
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU) :
    H ⊓ centralizer (twoCore HU : Set G) ≤ twoCore HU := by
  have hcore : twoCore H ≤ twoCore HU :=
    hsat (twoCore H) (pCoreIn_le 2 H) (isPGroup_pCoreIn 2 H)
      (hpair.2.trans (le_normalizer_twoCore H))
  have he := core_normalizer_eq_of_saturation hpair hsat
  have hA := lemma_2_5_3_one hEven hM B hp hBH hH hpair hcore
  intro x hx
  have hxC : x ∈ centralizer
      (twoCore (H ⊓ normalizer (twoCore HU : Set G)) : Set G) := by
    rw [he]
    exact hx.2
  have hxQ := hA ⟨⟨hx.1, centralizer_le_normalizer _ hx.2⟩, hxC⟩
  change x ∈ twoCore (H ⊓ normalizer (twoCore HU : Set G)) at hxQ
  rwa [he] at hxQ

/-- The original selected involution belongs to the local-pair core after
the source Sylow alignment, with no component-projection assumption. -/
theorem SourceTuple.central_involution_mem_core_of_saturation
    {S T : Subgroup G} {z : G} (d : SourceTuple M H S T z)
    (hEven : IsEvenCharacteristic G) (hM : M ∈ Chapter1.He G)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hH : H = ⨅ i, normalizer (B i : Set G))
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hQS : twoCore HU ≤ S)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU) :
    z ∈ twoCore HU := by
  have hSH : S ≤ H := by
    obtain ⟨P, hP⟩ := d.sylow_intersection
    rw [← hP]
    exact (map_subtype_le _).trans inf_le_left
  apply centralizer_le_core_of_saturation hEven hM B hp hBH hH hpair hsat
  refine ⟨hSH (d.center_le d.mem_center), ?_⟩
  obtain ⟨zT, hzT, rfl⟩ := d.mem_center
  intro q hq
  exact congrArg Subtype.val (mem_center_iff.mp hzT ⟨q, d.lt.le (hQS hq)⟩)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
