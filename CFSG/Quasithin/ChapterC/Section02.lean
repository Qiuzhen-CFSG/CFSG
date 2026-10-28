module

public import Theory.GroupTheory.RadicalNormalizerControl

/-!
# More general pushing up: radical subgroups

The elementary input C.2.1 says that a radical two-subgroup R is the
unique maximal two-subgroup normalized by N_H(R), and contains O₂(H).
These statements use the literal radical equality, so they are available
independently of the chapter's SQTK and pushing-up interfaces.

The reusable proof works at any prime: in the product with a normalized
p-subgroup, R is self-normalizing; the normalizer condition forces equality.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
combined manuscript (1 March 2004), §C.2, Lemma C.2.1, printed p.144.
The later pushing-up results C.2.2--C.2.14 remain to be assembled here.
-/

namespace CFSG.Quasithin.ChapterC

open Subgroup

variable {H : Type*} [Group H] [Finite H]

/-- C.2.1(1), in the stronger greatest-element form: every two-subgroup
normalized by N_H(R) lies in R. The nontriviality required by B₂(H) is
unnecessary for this elementary conclusion. -/
public theorem radical_isGreatest_normalized_twoSubgroup
    (R : Subgroup H) (hR : IsPGroup 2 R)
    (hrad : (pCore 2 (normalizer (R : Set H))).map
      (normalizer (R : Set H)).subtype = R) :
    IsGreatest {S : Subgroup H | IsPGroup 2 S ∧
      normalizer (R : Set H) ≤ normalizer (S : Set H)} R := by
  refine ⟨⟨hR, le_rfl⟩, ?_⟩
  intro S hS
  exact le_of_normalizer_le_normalizer_of_pCore_normalizer_le R S hR hS.1
    hrad.le hS.2

/-- C.2.1(1): the maximal two-subgroups normalized by N_H(R) form {R}. -/
public theorem radical_maximal_normalized_twoSubgroups
    (R : Subgroup H) (hR : IsPGroup 2 R)
    (hrad : (pCore 2 (normalizer (R : Set H))).map
      (normalizer (R : Set H)).subtype = R) :
    {S : Subgroup H | Maximal (fun S : Subgroup H => IsPGroup 2 S ∧
      normalizer (R : Set H) ≤ normalizer (S : Set H)) S} = {R} := by
  have hgreat := radical_isGreatest_normalized_twoSubgroup R hR hrad
  ext S
  constructor
  · intro hS
    exact le_antisymm (hgreat.2 hS.1) (hS.2 hgreat.1 (hgreat.2 hS.1))
  · intro hS
    have hSR : S = R := hS
    subst S
    exact ⟨hgreat.1, fun T hT _ => hgreat.2 hT⟩

/-- C.2.1(2): a radical two-subgroup contains O₂(H). -/
public theorem twoCore_le_radical
    (R : Subgroup H) (hR : IsPGroup 2 R)
    (hrad : (pCore 2 (normalizer (R : Set H))).map
      (normalizer (R : Set H)).subtype = R) : pCore 2 H ≤ R :=
  pCore_le_of_pCore_normalizer_le R hR hrad.le

end CFSG.Quasithin.ChapterC
