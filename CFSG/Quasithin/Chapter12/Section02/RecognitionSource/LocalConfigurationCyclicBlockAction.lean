module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicPair
public import Theory.Representation.BinaryNaturalAutomorphisms

/-!
# The full natural action and its literal local kernel

The marked action of L/O₂(L) realizes all automorphisms of V. Its kernel
inside L is therefore exactly O₂(L). In LT the kernel is still a two-group:
its intersection with L is a two-group, and LT/L is a two-group. Reducedness
places O₂(LT) in the kernel, giving equality. All normality remains relative
to LT. The prime-order pair also supplies U≤T.

Source: Aschbacher--Smith, 12.2.20--24, printed pp.802--804.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U W : Subgroup G} {d p : ℕ} {g v : G}

omit [Finite G] in
theorem NaturalLocalAnalysis.autModel (A : NaturalLocalAnalysis T L V d)
    (hLV : L ≤ normalizer (V : Set G)) :
    ∃ e : (L ⧸ pCore 2 L) ≃* MulAut V,
      ∀ l : L, e (QuotientGroup.mk' (pCore 2 L) l) =
        V.normalizerMonoidHom ⟨l, hLV l.property⟩ := by
  obtain ⟨e,f,hf⟩ := A.natural
  let e' := (e.trans (MulEquiv.ofBijective (binaryNaturalAut d)
    (binaryNaturalAut_bijective d))).trans (MulAut.congr f.symm)
  refine ⟨e', ?_⟩
  intro l
  ext v
  exact hf l v

omit [Finite G] in
theorem NaturalLocalAnalysis.simple_aut (A : NaturalLocalAnalysis T L V d)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) : IsSimpleGroup (MulAut V) := by
  let := hq
  obtain ⟨e,f,hf⟩ := A.natural
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) :=
    IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin d) (ZMod 2) ⧸
      center (Matrix.SpecialLinearGroup (Fin d) (ZMod 2))) := IsQuasisimple.simple
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) :=
    (BinaryLinear.OuterCyclic.projectiveEquivSL (by have := A.dimension.1; omega)).symm.isSimpleGroup
  exact (((MulEquiv.ofBijective (binaryNaturalAut d) (binaryNaturalAut_bijective d)).trans
    (MulAut.congr f.symm)).symm).isSimpleGroup


theorem InvariantOddLocalAnalysis.core_le_sylow_of_prime_order
    (S : InvariantOddLocalAnalysis T L V d p H P U W g v) (hc : Nat.card P = p) :
    U ≤ (T : Subgroup G) := by
  have hTH : (T : Subgroup G) ≤ H :=
    S.overgroup ▸ (le_sup_right : (T : Subgroup G) ≤ P ⊔ (T : Subgroup G))
  have hUc : U ≤ H.pCoreIn 2 := S.module_eq_of_prime_order hc ▸ S.in_core
  apply hUc.trans
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
    pCoreIn_le_sylow H (T.subtype hTH)

omit [Finite G] in
theorem NaturalLocalAnalysis.componentAut_ker (A : NaturalLocalAnalysis T L V d)
    (D : ChosenModule T L V) :
    (V.normalizerMonoidHom.comp (inclusion D.normalizes)).ker = pCore 2 L := by
  obtain ⟨e,he⟩ := A.autModel D.normalizes
  ext l
  change V.normalizerMonoidHom ⟨l,D.normalizes l.property⟩ = 1 ↔ l ∈ pCore 2 L
  rw [← he, e.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff l

omit [Finite G] in
theorem NaturalLocalAnalysis.componentAut_surjective (A : NaturalLocalAnalysis T L V d)
    (D : ChosenModule T L V) :
    Function.Surjective (V.normalizerMonoidHom.comp (inclusion D.normalizes)) := by
  obtain ⟨e,he⟩ := A.autModel D.normalizes
  intro a
  obtain ⟨q,rfl⟩ := e.surjective a
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  exact ⟨l,(he l).symm⟩

omit [Finite G] in
/-- The full local kernel, with normality only inside LT. -/
theorem NaturalLocalAnalysis.joinAut_kernel_isPGroup (A : NaturalLocalAnalysis T L V d)
    (D : ChosenModule T L V) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    IsPGroup 2 (V.normalizerMonoidHom.comp (inclusion (sup_le D.normalizes hTV))).ker := by
  let J := L ⊔ (T : Subgroup G)
  let X := L.subgroupOf J
  let : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let a := V.normalizerMonoidHom.comp (inclusion (sup_le D.normalizes hTV))
  let f := (QuotientGroup.mk' X).comp a.ker.subtype
  have hp : IsPGroup 2 (J ⧸ X) :=
    isPGroup_quotient_of_sup_eq_top X ((T : Subgroup G).subgroupOf J)
      T.isPGroup'.comap_subtype (by
        rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self])
  let j : f.ker →* pCore 2 L := {
    toFun x := ⟨⟨x.val.val.val,(QuotientGroup.eq_one_iff (N := X) x.val.val).mp x.property⟩, by
      apply (A.componentAut_ker D).le
      exact x.val.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (Subtype.ext (Subtype.ext
      (congrArg (fun z : pCore 2 L => z.val.val) he)))
  have hk : IsPGroup 2 f.ker := pCore_isPGroup.of_injective j hj
  have hh := (hp.to_subgroup ⊤).comap_of_ker_isPGroup f hk
  rw [comap_top] at hh
  exact hh.of_equiv topEquiv

omit [Finite G] in
/-- The precise full kernel of conjugation on V is O₂(LT). -/
theorem NaturalLocalAnalysis.joinAut_ker (A : NaturalLocalAnalysis T L V d)
    (D : ChosenModule T L V) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    (V.normalizerMonoidHom.comp (inclusion (sup_le D.normalizes hTV))).ker =
      pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
  let a := V.normalizerMonoidHom.comp (inclusion (sup_le D.normalizes hTV))
  apply le_antisymm
  · exact le_sSup ⟨a.normal_ker,A.joinAut_kernel_isPGroup D hTV⟩
  · intro x hx
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change (x : G) * (z : G) * (x : G)⁻¹ = (z : G)
    have hc := D.core_centralizes (mem_map_of_mem (L ⊔ (T : Subgroup G)).subtype hx)
    exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hc) z z.property).symm


end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
