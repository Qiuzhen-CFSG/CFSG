module
public import Theory.Representation.NormalElementaryQuotient.SubgroupSpace

/-!
# Transport of literal subgroup spaces

The subgroup space inside a normal elementary abelian group retains its
original additive carrier. Its inclusion gives a binary linear equivalence;
subgroup sums and disjointness become subspace sums and disjointness.
Conjugation by a lift of the acting quotient sends this subspace to the
space of the conjugate subgroup, using the unchanged quotient map.

These transports apply to the crossed moved factors in the Chapter 10
central Hall action. Source: Aschbacher--Smith 3.2.6 and 10.1.1,
printed pp.581,741.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.NormalElementaryQuotient
variable {H Q : Type*} [Group H] [Group Q]
  (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
  (q : H →* Q) (hq : Function.Surjective q)
  (hker : q.ker = centralizer (W : Set H))

omit [W.Normal] in
def subgroupSpaceEquiv (A : Subgroup H) [IsElementaryAbelian 2 A] (hA : A ≤ W) :
    Additive A ≃ₗ[ZMod 2] subgroupSpace W A := by
  let f := (inclusion hA).toAdditive.toZModLinearMap 2
  let g : Additive A →ₗ[ZMod 2] subgroupSpace W A := f.codRestrict _ (fun a => a.toMul.property)
  exact LinearEquiv.ofBijective g ⟨fun _ _ he => Subtype.ext (congrArg (fun v => (v.val.toMul : H)) he),
    fun v => ⟨Additive.ofMul ⟨v.val.toMul,v.property⟩,rfl⟩⟩

omit [W.Normal] in
theorem subgroupSpaceEquiv_apply_coe (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : A ≤ W) (a : Additive A) :
    ((subgroupSpaceEquiv W A hA a).val.toMul : H) = (a.toMul : H) := by rfl

omit [W.Normal] in
theorem subgroupSpace_sup {A B : Subgroup H} (hA : A ≤ W) (hB : B ≤ W) :
    subgroupSpace W (A ⊔ B) = subgroupSpace W A ⊔ subgroupSpace W B := by
  unfold subgroupSpace
  rw [subgroupOf_sup hA hB]
  rw [(Subgroup.toAddSubgroup : Subgroup W ≃o AddSubgroup (Additive W)).map_sup]
  exact (AddSubgroup.toZModSubmodule (n := 2) :
    AddSubgroup (Additive W) ≃o Submodule (ZMod 2) (Additive W)).map_sup _ _

omit [W.Normal] in
theorem subgroupSpace_disjoint {A B : Subgroup H} (hd : Disjoint A B) :
    Disjoint (subgroupSpace W A) (subgroupSpace W B) := by
  apply Submodule.disjoint_def.mpr
  intro v hA hB
  have he := Subgroup.mem_bot.mp (hd.eq_bot.le ⟨hA,hB⟩)
  exact Additive.toMul.injective (Subtype.ext he)

theorem subgroupSpace_map_conj (A : Subgroup H) (g : H) :
    (subgroupSpace W A).map (representation W q hq hker (q g)) =
      subgroupSpace W (A.map (MulAut.conj g).toMonoidHom) := by
  ext v
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨u.toMul,hu, (representation_apply W q hq hker g u).symm⟩
  · intro hv
    obtain ⟨a,ha,he⟩ := hv
    change g*a*g⁻¹ = (v.toMul : H) at he
    have haw : a ∈ W := by
      have hh := (inferInstance : W.Normal).conj_mem v.toMul v.toMul.property g⁻¹
      rw [←he] at hh
      simpa only [inv_inv,inv_mul_cancel_left,mul_assoc,inv_mul_cancel,mul_one] using hh
    refine ⟨Additive.ofMul ⟨a,haw⟩,ha,?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (representation_apply W q hq hker g _).trans he
end Representation.NormalElementaryQuotient
