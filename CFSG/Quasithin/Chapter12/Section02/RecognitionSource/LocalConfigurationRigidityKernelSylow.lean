module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityKernelCommon
public import Theory.Representation.BinaryNaturalFullAction
public import Theory.GroupTheory.SylowNormalJoinIntersection

/-!
# The Sylow product from the original binary natural action

Every automorphism of V is realized inside L. Correcting an element of LT
by its marked representative in L gives LT=L C_{LT}(V). Both factors are
normal in LT, so intersecting with the original Sylow subgroup gives
T=(T∩L)C_T(V), with the exact ambient inclusions.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
12.2.20 and12.2.25, printed pp.802,805. The higher-dimensional consumer
in LocalConfigurationRigidityKernelD45 replaces C_T(V) by V C_T(L).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {d : ℕ}
namespace RigidityKernel

/-- Every automorphism of the binary natural module is realized by L.
Inside LT this gives a product with the literal centralizer of V. -/
theorem local_join_split
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) :
    L ⊔ (T : Subgroup G) = L ⊔ ((L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G)) := by
  let J := L ⊔ (T : Subgroup G)
  have hJV : J ≤ normalizer (V : Set G) := sup_le D.normalizes
    (((structural G T L h).2.2 V D).1)
  obtain ⟨e,f,hf⟩ := A.natural
  apply le_antisymm _ (sup_le le_sup_left inf_le_left)
  intro g hg
  let a : MulAut V := V.normalizerMonoidHom ⟨g,hJV hg⟩
  obtain ⟨x,hx⟩ := Representation.specialLinearNatural_binary_full d ((f.symm.trans a).trans f)
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (e.symm x)
  have hel : e (QuotientGroup.mk' (pCore 2 L) l) = x := by rw [hl,e.apply_symm_apply]
  have ha : V.normalizerMonoidHom ⟨l,D.normalizes l.property⟩ = a := by
    ext v
    have hact := hf l v
    rw [hel] at hact
    have heq := hx (f v)
    simp only [MulEquiv.trans_apply, f.symm_apply_apply] at heq
    rw [heq, f.symm_apply_apply] at hact
    exact hact.symm
  have hk : (⟨l,D.normalizes l.property⟩⁻¹ * (⟨g,hJV hg⟩ : normalizer (V : Set G))) ∈
      V.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ha]
    exact inv_mul_cancel a
  rw [normalizerMonoidHom_ker] at hk
  have hc : (l : G)⁻¹*g ∈ J ⊓ centralizer (V : Set G) :=
    ⟨J.mul_mem (J.inv_mem ((show L ≤ J from le_sup_left) l.property)) hg,hk⟩
  simpa only [mul_inv_cancel_left] using mul_mem_sup l.property hc

/-- The original Sylow is the product (T∩L)C_T(V), the consequence of
12.2.20 used in the common centralizer proof. -/
theorem sylow_split_over_kernel
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) :
    (T : Subgroup G) = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (V : Set G)) := by
  let J := L ⊔ (T : Subgroup G)
  let B := J ⊓ centralizer (V : Set G)
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hLJ : L ≤ J := le_sup_left
  have hBJ : B ≤ J := inf_le_left
  have hJV : J ≤ normalizer (V : Set G) := sup_le D.normalizes
    (((structural G T L h).2.2 V D).1)
  have hJB : J ≤ normalizer (B : Set G) :=
    (le_inf J.le_normalizer (hJV.trans (normalizer_le_normalizer_centralizer V))).trans
      inf_normalizer_le_normalizer_inf
  let : (L.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let : (B.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJB
  have hcover : L.subgroupOf J ⊔ B.subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup hLJ hBJ, ← local_join_split h D structural A, subgroupOf_self]
  have he := (T.subtype hTJ).inf_sup_eq_sup_inf_normal (L.subgroupOf J) (B.subgroupOf J)
  rw [hcover, inf_top_eq] at he
  have hm := congrArg (map J.subtype) he
  rw [Subgroup.map_sup, map_inf _ _ _ J.subtype_injective, map_inf _ _ _ J.subtype_injective,
    Sylow.coe_subtype, map_subgroupOf_eq_of_le hTJ, map_subgroupOf_eq_of_le hLJ,
    map_subgroupOf_eq_of_le hBJ] at hm
  simpa only [B, inf_assoc, ← inf_assoc, inf_eq_left.mpr hTJ] using hm

end RigidityKernel
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
