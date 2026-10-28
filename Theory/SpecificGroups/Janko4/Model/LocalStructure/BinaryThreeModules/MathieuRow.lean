module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
public import Theory.Representation.PSL3Two.SmallModules
public import Theory.SpecificGroups.PSL3Two.Cardinality

/-!
# The J₄ Mathieu local excludes a normal binary-three residual

The literal max1 subgroup has a two-group kernel and simple M₂₄ quotient.
A normal embedded residual with quotient SL₃(2) has order 2ⁿ·168. Its
Mathieu image is therefore either trivial, forcing a factor seven into the
binary kernel, or the whole quotient, forcing a factor five into 2ⁿ·168.
Both possibilities are impossible. The marking is an actual equivalence
from the residual's full two-core quotient, and normality is relative to
the local subgroup. No coverage of maximal two-locals is asserted.

Source: the J₄ row (a) in the final inspection of Aschbacher–Smith 4.4.3,
printed pp.622–623 of `refs/quasithin.pdf`; GLS3 Table 5.3i. The existing
literal ATLAS max1 quotient and kernel certificates supply the model facts.
-/

public section
open Subgroup
namespace Janko4.LocalStructure.BinaryThreeModules
variable {M S : Type*} [Group M] [Group S] [Finite S]

private theorem marked_card (e : (S ⧸ pCore 2 S) ≃* BinaryLinearThree.Group) :
    ∃ n : ℕ, Nat.card S = 2 ^ n * 168 := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := S)).exists_card_eq
  refine ⟨n,?_⟩
  have h := (pCore 2 S).card_mul_index
  rw [index_eq_card,Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_SL,hn] at h
  exact h.symm

/-- The literal max1 row has no normal embedded binary-three residual. -/
theorem not_max1_of_normal_marked_residual
    (r : S →* M) (hr : Function.Injective r) (hn : r.range.Normal)
    (e : (S ⧸ pCore 2 S) ≃* BinaryLinearThree.Group) :
    ¬ Nonempty (M ≃* Janko4.Cardinality.max1Subgroup
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four) := by
  rintro ⟨a⟩
  let C := Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  let K := Janko4.Cardinality.localKernel Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  let b := localQuotientEquivM24 Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  let q : C →* Sporadic.Mathieu.M24 := b.toMonoidHom.comp (QuotientGroup.mk' K)
  have hq : Function.Surjective q := b.surjective.comp (QuotientGroup.mk'_surjective K)
  have hk : q.ker = K := by
    rw [MonoidHom.ker_comp_of_injective _ _ b.injective,QuotientGroup.ker_mk']
  let f : S →* C := a.toMonoidHom.comp r
  have hf : Function.Injective f := a.injective.comp hr
  have hfn : f.range.Normal := by
    rw [MonoidHom.range_comp]
    exact hn.map a.toMonoidHom a.surjective
  have hqn : (q.comp f).range.Normal := by
    rw [MonoidHom.range_comp]
    exact hfn.map q hq
  let := Sporadic.Mathieu.m24_isSimpleGroup
  obtain ⟨n,hncard⟩ := marked_card e
  rcases hqn.eq_bot_or_eq_top with hzero | htop
  · have hle : f.range ≤ K := by
      rw [MonoidHom.range_comp] at hzero
      exact hk ▸ (map_eq_bot_iff f.range).mp hzero
    let fK : S →* K := f.codRestrict K (fun x => hle ⟨x,rfl⟩)
    have hiK : Function.Injective fK := fun x y hxy => hf (congrArg Subtype.val hxy)
    have hdiv := (show 7 ∣ Nat.card S by rw [hncard]; exact dvd_mul_of_dvd_right (by decide) _).trans
      (card_dvd_of_injective fK hiK)
    rw [Janko4.Cardinality.localKernel_card] at hdiv
    norm_num at hdiv
  · have hd := card_dvd_of_surjective (q.comp f) (MonoidHom.range_eq_top.mp htop)
    have hfive : 5 ∣ Nat.card S := (show 5 ∣ Nat.card Sporadic.Mathieu.M24 by
      rw [Sporadic.Mathieu.m24_order]; norm_num).trans hd
    rw [hncard] at hfive
    rcases (show Nat.Prime 5 by decide).dvd_mul.mp hfive with hpow | h168
    · have hh := (show Nat.Prime 5 by decide).dvd_of_dvd_pow hpow
      norm_num at hh
    · norm_num at h168
end Janko4.LocalStructure.BinaryThreeModules
