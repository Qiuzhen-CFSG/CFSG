module
public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.NormalizerAction
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.Representation.BinaryTransvectionGroups.Duality
public import Theory.ElementaryAbelian.Join
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The full axis of an elementary TI pair

For disjoint equal-order elementary TI subgroups V and A, put U = N_V(A)
and B = N_A(V). If U is a hyperplane of V, the literal action of B on V is
exactly the full radical with axis U. Mutual-normalizer commutation fixes U
pointwise. For v outside U, I.6.2's surjectivity of b ↦ [b,v] gives every
possible displacement of v in U; a linear map is determined by U and v.

The product U B is elementary and normal inside V ∨ A, hence is contained
in that pair's relative two-core. No odd-dihedral recognition is assumed.
Source: Aschbacher–Smith, I.6.2(2a), pp.424–425, and the construction before
12.2.20, p.802. The hyperplane must still be constructed in the source setting.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative

namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G]

def pairAxisSpace (V A : Subgroup G) [IsElementaryAbelian 2 V] :
    Submodule (ZMod 2) (Additive V) :=
  AddSubgroup.toZModSubmodule 2 ((normalizer (A : Set G)).subgroupOf V).toAddSubgroup

theorem pairAxisSpace_exists_form (V A : Subgroup G) [IsElementaryAbelian 2 V]
    (hh : IsCoatom (pairAxisSpace V A)) :
    ∃ f : Module.Dual (ZMod 2) (Additive V), f ≠ 0 ∧
      ∀ v : Additive V, f v = 0 ↔ (v.toMul : G) ∈ normalizer (A : Set G) := by
  obtain ⟨f, hf, hle⟩ := (pairAxisSpace V A).exists_le_ker_of_lt_top hh.lt_top
  have hk : f.ker ≠ ⊤ := fun h => hf (LinearMap.ker_eq_top.mp h)
  have he := (hh.le_iff_eq hk).mp hle
  refine ⟨f, hf, fun v => ?_⟩
  change v ∈ f.ker ↔ _
  rw [he]
  rfl

noncomputable def pairNormalizerLinearAction (V A : Subgroup G)
    [IsElementaryAbelian 2 V] :
    (A ⊓ normalizer (V : Set G) : Subgroup G) →* BinaryLinear.GL (Additive V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive V)).toMonoidHom.comp
    (Representation.elementaryRepresentation
      (V.normalizerMonoidHom.comp (inclusion inf_le_right))).asGroupHom

theorem pairNormalizerLinearAction_apply (V A : Subgroup G)
    [IsElementaryAbelian 2 V]
    (b : ↥(A ⊓ normalizer (V : Set G))) (v : Additive V) :
    ((pairNormalizerLinearAction V A b v).toMul : G) =
      (b : G) * (v.toMul : G) * (b : G)⁻¹ := rfl

theorem pairNormalizerLinearAction_range_eq_radical [Finite G]
    (V A : Subgroup G) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hV : IsTISubgroup V) (hA : IsTISubgroup A)
    (hcard : Nat.card V = Nat.card A)
    (f : Module.Dual (ZMod 2) (Additive V)) (hf : f ≠ 0)
    (hker : ∀ v : Additive V, f v = 0 ↔ (v.toMul : G) ∈ normalizer (A : Set G)) :
    (pairNormalizerLinearAction V A).range = BinaryLinear.radical f.ker := by
  have hfix (b : ↥(A ⊓ normalizer (V : Set G))) (v : Additive V) (hv : f v = 0) :
      pairNormalizerLinearAction V A b v = v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [pairNormalizerLinearAction_apply]
    exact mul_inv_eq_iff_eq_mul.mpr
      (ti_pair_commute_of_mutual_normalizers V A hVA v.toMul.property
        ((hker v).mp hv) b.property.1 b.property.2).symm.eq
  have hrad (b : ↥(A ⊓ normalizer (V : Set G))) :
      pairNormalizerLinearAction V A b ∈ BinaryLinear.radical f.ker := by
    refine ⟨hfix b, fun v => ?_⟩
    apply (hker _).mpr
    have hc := ti_pair_commutator_mem_opposite A V hVA.symm hA b.property v.toMul.property
    have hc' : ⁅(b : G), (v.toMul : G)⁆ ∈ V ⊓ normalizer (A : Set G) := by
      rw [← commutatorElement_inv]
      exact (V ⊓ normalizer (A : Set G)).inv_mem hc
    have hd : ((pairNormalizerLinearAction V A b v - v).toMul : G) =
        ⁅(b : G), (v.toMul : G)⁆ := by
      simp only [toMul_sub, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv,
        pairNormalizerLinearAction_apply, commutatorElement_def]
    rw [hd]
    exact hc'.2
  apply le_antisymm
  · rintro t ⟨b, rfl⟩
    exact hrad b
  intro t ht
  obtain ⟨v, hv⟩ : ∃ v : Additive V, f v ≠ 0 := by
    by_contra! hn
    exact hf (LinearMap.ext hn)
  have hv1 : f v = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hv
  have hvU : (v.toMul : G) ∉ V ⊓ normalizer (A : Set G) :=
    fun hvU => hv ((hker v).mpr hvU.2)
  have hu : ((t v - v).toMul : G) ∈ V ⊓ normalizer (A : Set G) :=
    ⟨(t v - v).toMul.property, (hker _).mp (ht.2 v)⟩
  obtain ⟨b, hb, hcomm⟩ := ti_pair_exists_commutator V A hVA hV hA hcard
    v.toMul.property hvU hu
  refine ⟨⟨b, hb⟩, ?_⟩
  have heval : pairNormalizerLinearAction V A ⟨b, hb⟩ v = t v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [pairNormalizerLinearAction_apply]
    simp only [commutatorElement_def, toMul_sub,
      div_eq_mul_inv] at hcomm
    exact mul_right_cancel hcomm
  apply LinearEquiv.ext
  intro w
  have hw : f (w - f w • v) = 0 := by
    rw [map_sub, map_smul, hv1, smul_eq_mul, mul_one, sub_self]
  have hbfix := hfix ⟨b, hb⟩ (w - f w • v) hw
  have htfix := ht.1 (w - f w • v) hw
  simp only [map_sub, map_smul, heval] at hbfix htfix
  exact sub_left_injective (hbfix.trans htfix.symm)

theorem ti_pair_mutual_normalizers_le_twoCore (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hV : IsTISubgroup V) (hA : IsTISubgroup A) :
    (V ⊓ normalizer (A : Set G)) ⊔ (A ⊓ normalizer (V : Set G)) ≤
      (V ⊔ A).pCoreIn 2 := by
  let U := V ⊓ normalizer (A : Set G)
  let B := A ⊓ normalizer (V : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ V from inf_le_left)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (show B ≤ A from inf_le_left)
  let : IsElementaryAbelian 2 (U ⊔ B : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer
      (le_centralizer_iff.mp (ti_pair_mutual_normalizers_commute V A hVA))
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 (U ⊔ B : Subgroup G))
    (sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right))
    (ti_pair_sup_le_normalizer V A hVA hV hA)

end CFSG.Quasithin.ChapterI.Section06To08
