module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Source

/-!
# The characteristic-centralizer argument in MS93 (4.2)(i)

A characteristic subgroup W of R is contained in A D, where A lies in W
and centralizes O_2(M), and D is centralized by L. Consequently
W = A (W intersect D). The centralizer T_1 = C_R(W) is characteristic in R;
(L T_1) intersect O_2(M) centralizes both factors of W and lies in T_1.
The genuine source minimality clause (4.0) forces T_1 = R.

This is the group-theoretic final step; the earlier marked-module proof of
the product containment is not assumed to follow from a family label.

Source: Meierfrankenfeld--Stellmacher (1993), (4.0) and (4.2)(i), pp.881--882.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.Transfer

variable {M : Type*} [Group M]

/-- The last group-theoretic step of (4.2)(i). Minimality is applied to
the intrinsic centralizer of W in R, whose characteristicity follows from
that of W. The product containment splits W as A (W intersect D). -/
theorem centralizes_of_minimal_and_split {L R W A D : Subgroup M}
    (hmin : CharacteristicMinimal L R) (hQR : pCore 2 M ≤ R)
    (hWR : W ≤ R) (hchar : (W.subgroupOf R).Characteristic)
    (hAW : A ≤ W) (hWD : W ≤ A ⊔ D)
    (hQA : pCore 2 M ≤ centralizer (A : Set M))
    (hDQ : D ≤ pCore 2 M) (hLD : L ≤ centralizer (D : Set M)) :
    R ≤ centralizer (W : Set M) := by
  let W₀ := W.subgroupOf R
  let T₁ : Subgroup R := centralizer (W₀ : Set R)
  let N := T₁.map R.subtype
  have hNC : N ≤ centralizer (W : Set M) := by
    rintro x ⟨t, ht, rfl⟩ w hw
    exact congrArg Subtype.val (ht ⟨w, hWR hw⟩ hw)
  have hsplit : W ≤ A ⊔ (W ⊓ D) := by
    intro w hw
    have hAD : A ≤ normalizer D :=
      (le_centralizer_iff.mpr (hDQ.trans hQA)).trans (Subgroup.centralizer_le_normalizer _)
    have hm : w ∈ (A : Set M) * (D : Set M) := by
      rw [← coe_mul_of_left_le_normalizer_right A D hAD]
      exact hWD hw
    obtain ⟨a, ha, d, hd, rfl⟩ := hm
    have hdW : d ∈ W := (W.mul_mem_cancel_left (hAW ha)).mp hw
    exact (A ⊔ (W ⊓ D)).mul_mem ((show A ≤ A ⊔ (W ⊓ D) from le_sup_left) ha)
      ((show W ⊓ D ≤ A ⊔ (W ⊓ D) from le_sup_right) ⟨hdW, hd⟩)
  have hLC : L ⊔ N ≤ centralizer (W ⊓ D : Set M) :=
    sup_le (hLD.trans (centralizer_le inf_le_right))
      (hNC.trans (centralizer_le inf_le_left))
  have hclosed : (L ⊔ N) ⊓ pCore 2 M ≤ N := by
    intro x hx
    have hxC : x ∈ centralizer (W : Set M) := by
      have hAWx : A ⊔ (W ⊓ D) ≤ centralizer ({x} : Set M) := by
        apply sup_le
        · intro a ha
          simpa only [mem_centralizer_singleton_iff] using (hQA hx.2 a ha)
        · intro d hd
          simpa only [mem_centralizer_singleton_iff] using (hLC hx.1 d hd)
      intro w hw
      have hh := hAWx (hsplit hw)
      exact mem_centralizer_singleton_iff.mp hh
    refine ⟨⟨x, hQR hx.2⟩, ?_, rfl⟩
    intro w hw
    exact Subtype.ext (hxC w hw)
  let : W₀.Characteristic := hchar
  have htop : T₁ = ⊤ := hmin T₁ inferInstance hclosed
  intro r hr
  apply hNC
  exact ⟨⟨r, hr⟩, htop ▸ mem_top _, rfl⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.Transfer
