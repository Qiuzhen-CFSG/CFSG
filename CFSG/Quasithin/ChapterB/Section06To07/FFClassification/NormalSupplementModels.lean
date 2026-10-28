module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.Quotient
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.BinaryLinear.Ambient
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.G2
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.AlternatingSeven.Ambient
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Model exclusions for normal Sylow supplements through literal quotients

If H=KT is minimal parabolic, every nonsolvable image is minimal parabolic:
the kernel either lies in the unique maximal-overgroup core or its product
with T is H, and the latter would make the image a two-group. This carries
the actual normal-supplement A₇ and A₈ obstructions through arbitrary action
kernels. Separately, K/O₂(K) identifies with the image of K in H/O₂(H),
which excludes SL₄(2), SL₅(2), A₇, A₈ and G₂(2)′ with the intrinsic core.

The Chapter 12 application is in LocalConfigurationNaturalHStarSourceResidualModels.
These are the quotient comparisons used in Aschbacher–Smith E.2.2 and
12.2.7, printed pp.215–216 and 797–798. The underlying concrete model
proofs retain their source attribution in the imported modules.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

/-- Every nonsolvable surjective image retains minimal parabolicity. -/
theorem minimalParabolic_surjective_of_not_solvable
    {A : Type*} [Group A] (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (f : G →* A) (hf : Function.Surjective f) (hs : ¬ Group.IsSolvable A) :
    IsMinimalParabolicOver (T.mapSurjective hf) ⊤ := by
  let : Finite A := Finite.of_surjective f hf
  apply minimalParabolic_map_of_kernel_le_core T hP f hf
  obtain hk | hk := minimalParabolic_normal_subgroup_dichotomy T hP f.ker
  · exact hk
  exfalso
  have ht : (T : Subgroup G).map f = ⊤ := by
    have he := congrArg (Subgroup.map f) hk
    simpa only [Subgroup.map_sup, Subgroup.map_ker_self, sup_bot_eq,
      map_top_of_surjective f hf] using he
  have hp : IsPGroup 2 (⊤ : Subgroup A) := ht ▸ T.isPGroup'.map f
  have hpA : IsPGroup 2 A := hp.of_equiv topEquiv
  let : Group.IsNilpotent A := hpA.isNilpotent
  exact hs inferInstance

/-- An alternating image of a normal Sylow supplement excludes minimal parabolicity,
with no condition on the kernel of the image map. -/
theorem normal_supplement_image_not_alternating
    {A : Type*} [Group A] (T : Sylow 2 G) (K : Subgroup G) [K.Normal]
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (f : G →* A) (hf : Function.Surjective f)
    {n : ℕ} (hn : n = 7 ∨ n = 8) (e : K.map f ≃* alternatingGroup (Fin n)) :
    ¬ IsMinimalParabolicOver T ⊤ := by
  intro hP
  let : Finite A := Finite.of_surjective f hf
  let : (K.map f).Normal := (inferInstance : K.Normal).map f hf
  have hs : ¬ Group.IsSolvable A := by
    intro hs
    let := hs
    let : Group.IsSolvable (alternatingGroup (Fin n)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (K.map f).subtype.comp e.symm.toMonoidHom)
        ((K.map f).subtype_injective.comp e.symm.injective)
    let : Group.IsPerfect (alternatingGroup (Fin n)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp only [Nat.card_fin]; omega)⟩
    let : Nontrivial (alternatingGroup (Fin n)) :=
      alternatingGroup.nontrivial_of_three_le_card (by simp only [Nat.card_fin]; omega)
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin n)) inferInstance
  have hgen' : K.map f ⊔ ((T.mapSurjective hf) : Subgroup A) = ⊤ := by
    change K.map f ⊔ (T : Subgroup G).map f = _
    rw [← Subgroup.map_sup, hgen, map_top_of_surjective f hf]
  have hP' := minimalParabolic_surjective_of_not_solvable T hP f hf hs
  rcases hn with rfl | rfl
  · exact not_minimalParabolic_of_alternatingSeven_supplement
      (T.mapSurjective hf) (K.map f) e hgen' hP'
  · exact not_minimalParabolic_of_binary_linear_supplement
      (T.mapSurjective hf) (K.map f) (Or.inl rfl)
      ((e.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two).trans
        (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))) hgen' hP'

/-- The same exclusion for the literal kernel quotient of a supplement's action.
The carrier equivalence accounts for intrinsic subgroup inclusions. -/
theorem normal_supplement_action_quotient_not_alternating
    {A B : Type*} [Group A] [Group B]
    (T : Sylow 2 G) (K : Subgroup G) [K.Normal]
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (eK : B ≃* K)
    (a : G →* A) (N : Subgroup B) [N.Normal]
    (hk : (a.comp (K.subtype.comp eK.toMonoidHom)).ker = N)
    {n : ℕ} (hn : n = 7 ∨ n = 8) (e : (B ⧸ N) ≃* alternatingGroup (Fin n)) :
    ¬ IsMinimalParabolicOver T ⊤ := by
  let f := a.rangeRestrict
  let k := (f.subgroupMap K).comp eK.toMonoidHom
  have hker : k.ker = N := by
    rw [← MonoidHom.comap_ker, Subgroup.ker_subgroupMap, MonoidHom.ker_rangeRestrict]
    exact hk
  let E : (B ⧸ N) ≃* K.map f :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective k
        ((f.subgroupMap_surjective K).comp eK.surjective))
  exact normal_supplement_image_not_alternating T K hgen f
    a.rangeRestrict_surjective hn (E.symm.trans e)

private def normalTwoCoreQuotientEquiv (K : Subgroup G) [K.Normal] :
    (K ⧸ pCore 2 K) ≃* K.map (QuotientGroup.mk' (pCore 2 G)) := by
  let f := (QuotientGroup.mk' (pCore 2 G)).subgroupMap K
  have he : f.ker = pCore 2 K := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 (inferInstance : K.Normal).isSubnormal).symm
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((QuotientGroup.mk' (pCore 2 G)).subgroupMap_surjective K))

private theorem quotient_supplement (T : Sylow 2 G) (K : Subgroup G)
    (hgen : K ⊔ (T : Subgroup G) = ⊤) :
    K.map (QuotientGroup.mk' (pCore 2 G)) ⊔
      ((T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))) : Subgroup _) = ⊤ := by
  change K.map _ ⊔ (T : Subgroup G).map _ = _
  rw [← Subgroup.map_sup, hgen, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

private theorem quotient_minimal (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤) :
    IsMinimalParabolicOver
      (T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))) ⊤ := by
  apply minimalParabolic_surjective T hP
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup.le_sylow_of_normal T

theorem normal_supplement_twoCore_not_binary_linear
    (T : Sylow 2 G) (K : Subgroup G) [K.Normal]
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hP : IsMinimalParabolicOver T ⊤)
    {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* SL(n, ZMod 2)) := by
  rintro ⟨e⟩
  let q := QuotientGroup.mk' (pCore 2 G)
  let : (K.map q).Normal := (inferInstance : K.Normal).map q (QuotientGroup.mk'_surjective _)
  exact not_minimalParabolic_of_binary_linear_supplement
    (T.mapSurjective (QuotientGroup.mk'_surjective _)) (K.map q) hn
    ((normalTwoCoreQuotientEquiv K).symm.trans e) (quotient_supplement T K hgen)
    (quotient_minimal T hP)

theorem normal_supplement_twoCore_not_alternating
    (T : Sylow 2 G) (K : Subgroup G) [K.Normal]
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hP : IsMinimalParabolicOver T ⊤)
    {n : ℕ} (hn : n = 7 ∨ n = 8) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin n)) := by
  rintro ⟨e⟩
  let q := QuotientGroup.mk' (pCore 2 G)
  let : (K.map q).Normal := (inferInstance : K.Normal).map q (QuotientGroup.mk'_surjective _)
  let e' := (normalTwoCoreQuotientEquiv K).symm.trans e
  rcases hn with rfl | rfl
  · exact not_minimalParabolic_of_alternatingSeven_supplement
      (T.mapSurjective (QuotientGroup.mk'_surjective _)) (K.map q) e'
      (quotient_supplement T K hgen) (quotient_minimal T hP)
  · exact not_minimalParabolic_of_binary_linear_supplement
      (T.mapSurjective (QuotientGroup.mk'_surjective _)) (K.map q) (Or.inl rfl)
      ((e'.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two).trans
        (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide)))
      (quotient_supplement T K hgen) (quotient_minimal T hP)

theorem normal_supplement_twoCore_not_binary_g2
    (T : Sylow 2 G) (K : Subgroup G) [K.Normal]
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hP : IsMinimalParabolicOver T ⊤) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  rintro ⟨e⟩
  let q := QuotientGroup.mk' (pCore 2 G)
  let : (K.map q).Normal := (inferInstance : K.Normal).map q (QuotientGroup.mk'_surjective _)
  exact not_minimalParabolic_of_normal_binary_g2_derived
    (T.mapSurjective (QuotientGroup.mk'_surjective _)) (K.map q)
    (quotient_supplement T K hgen) ((normalTwoCoreQuotientEquiv K).symm.trans e)
    (quotient_minimal T hP)
end CFSG.Quasithin.ChapterB
