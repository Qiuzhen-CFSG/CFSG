module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.InitialFusion.ActorFusion.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.AmbientElementary
public import Theory.GroupTheory.SaturatedCentralizerTransport

/-!
# Transporting actor fusion into the actual normalizer of F

Conjugate F into the marked involution's Sylow subgroup while carrying a
to z. Relative normality makes the resulting conjugate Sylow normalize F.
Sylow conjugacy inside N_G(F), and the unique nonidentity point in the
centralizer of the coordinate Sylow, then give fusion of z and a inside N_G(F).

The normalizer acts on the actual coordinate group F. Its stabilizer of z
is exactly the local Sylow action, by N_G(F) ∩ C_G(z) = T. Thus the remaining
part of Lemma 3 is a concrete finite automorphism problem, with no abstract
family tag or additional ambient fusion hypothesis.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, paragraph preceding Lemma 3, printed p.5.
-/

open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.ActorFusion
open LocalModelDichotomy

universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

@[expose] public noncomputable def coordinates : modelF ≃* F D k :=
  (modelF.equivMapOfInjective (into D k) (into_injective D k)).trans
    (MulEquiv.subgroupCongr (modelF_map D k))

public theorem coordinates_coe (x : modelF) : (coordinates D k x : G) = into D k x := rfl

@[expose] public noncomputable def normalizerAction : normalizer (F D k : Set G) →* MulAut modelF :=
  (MulAut.congr (coordinates D k).symm).toMonoidHom.comp (F D k).normalizerMonoidHom

public theorem normalizerAction_apply (n : normalizer (F D k : Set G)) (x : modelF) :
    into D k (normalizerAction D k n x) = (n : G) * into D k x * (n : G)⁻¹ := by
  change (coordinates D k ((coordinates D k).symm
    ((F D k).normalizerMonoidHom n (coordinates D k x))) : G) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

@[expose] public noncomputable def actorImage : Subgroup (MulAut modelF) := (normalizerAction D k).range

variable [Finite G]

public theorem normalizerAction_local (x : modelT) :
    normalizerAction D k ⟨into D k x, caseIISylow_le_normalizer_F D k
      (mem_map_of_mem _ x.property)⟩ = localAction x := by
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  apply into_injective D k
  rw [normalizerAction_apply]
  change into D k x * into D k y * (into D k x)⁻¹ =
    into D k ((x : TwistedModel) * y * (x : TwistedModel)⁻¹)
  simp only [map_mul, map_inv]

public theorem localActor_le_actorImage : localActor ≤ actorImage D k := by
  rintro f ⟨x, rfl⟩
  exact ⟨_, normalizerAction_local D k x⟩

local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm

private theorem centralizes_modelT (x : TwistedModel)
    (hx : x ∈ centralizer (modelT : Set TwistedModel)) : x = 1 ∨ x = z 0 := by
  have h : ∀ x : TwistedModel,
      (z 1 * x = x * z 1) → (z 2 * x = x * z 2) →
      (z 3 * x = x * z 3) → (a * x = x * a) →
      (b * x = x * b) → (d * x = x * d) → x = 1 ∨ x = z 0 := by decide +kernel
  apply h x
  all_goals apply hx
  all_goals change _ ∈ (centralizer {a.right}).comap SemidirectProduct.rightHom
  all_goals apply mem_centralizer_singleton_iff.mpr
  all_goals decide +kernel

private theorem centralizes_caseIISylow (x : G)
    (hx : x ∈ centralizer (caseIISylow D k : Set G)) : x = 1 ∨ x = D.z := by
  have hz : z 0 ∈ modelT := modelE_le_modelT (z_mem_modelE 0)
  change x ∈ centralizer (modelT.map (into D k) : Set G) at hx
  rw [centralizer_map D k modelT hz] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rcases centralizes_modelT y hy with rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr (into_z_zero D k)

public theorem actorImage_stabilizer (f : MulAut modelF) (hf : f ∈ actorImage D k)
    (hz : f zF = zF) : f ∈ localActor := by
  obtain ⟨n, rfl⟩ := hf
  have hnC : (n : G) ∈ D.centralizer := by
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    have hh := congrArg (fun x : modelF => into D k x) hz
    rw [normalizerAction_apply] at hh
    simpa only [zF, into_z_zero D k] using hh
  have hnT : (n : G) ∈ caseIISylow D k := by
    change (n : G) ∈ (caseIISylow D k : Subgroup G)
    rw [← normalizer_F_inf_centralizer D k]
    exact ⟨n.property, hnC⟩
  obtain ⟨x, hx, he⟩ := hnT
  refine ⟨⟨x, hx⟩, ?_⟩
  rw [← normalizerAction_local D k ⟨x, hx⟩]
  congr 1
  exact Subtype.ext he

public theorem normalizer_fuses_a (h : IsConj D.z (into D k a)) :
    ∃ n : normalizer (F D k : Set G), (n : G) * D.z * (n : G)⁻¹ = into D k a := by
  have hTC : (caseIISylow D k : Subgroup G) ≤ D.centralizer := by
    rintro x ⟨y, hy, rfl⟩
    exact (k y).property
  have hFa : F D k ≤ centralizer {into D k a} := by
    rw [← F_centralizer D k]
    exact centralizer_le (show ({into D k a} : Set G) ⊆ F D k from
      Set.singleton_subset_iff.mpr (by rw [← modelF_map D k]; exact mem_map_of_mem _ aF.property))
  have hFp : IsPGroup 2 (F D k) :=
    IsPGroup.of_card (n := 4) (by simpa using F_card D k)
  obtain ⟨g, hg, hFg⟩ := exists_conj_into_saturated_centralizer D.z (into D k a)
    (caseIISylow D k) (F D k) (caseIISylow D k).isPGroup' hFp hTC hFa
    (fun V hV hTV _ => (caseIISylow D k).is_maximal' hV hTV) h.symm
  let P : Sylow 2 G := g⁻¹ • caseIISylow D k
  have hFP : F D k ≤ P := by
    intro x hx
    have hh : (MulAut.conj g) x ∈ caseIISylow D k := hFg (mem_map_of_mem _ hx)
    have hm := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hh
    change (MulAut.conj g⁻¹) ((MulAut.conj g) x) ∈ P at hm
    change x ∈ P
    simpa [MulAut.conj_apply, mul_assoc] using hm
  have hPN : (P : Subgroup G) ≤ normalizer (F D k : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hFP).mp
      (elementary_sixteen_normal_in_sylow D k P (F D k) hFP (F_elementary D k) (F_card D k))
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq (normalizer (F D k : Set G))
    (P.subtype hPN) ((caseIISylow D k).subtype (caseIISylow_le_normalizer_F D k))
  have hPconj : (n : G) • P = caseIISylow D k := by
    rw [Sylow.smul_subtype] at hn
    exact Sylow.subtype_injective hn
  have haP : into D k a ∈ centralizer (P : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    have hh := mem_centralizer_singleton_iff.mp (hTC hy)
    have hga : (MulAut.conj g⁻¹) D.z = into D k a := by
      have hh := congrArg (MulAut.conj g⁻¹) hg
      simpa [MulAut.conj_apply, mul_assoc] using hh.symm
    change (MulAut.conj g⁻¹) y * into D k a = into D k a * (MulAut.conj g⁻¹) y
    simpa only [map_mul, hga] using congrArg (MulAut.conj g⁻¹) hh
  have hanT : (MulAut.conj (n : G)) (into D k a) ∈
      centralizer (caseIISylow D k : Set G) := by
    rw [← hPconj]
    rintro x ⟨y, hy, rfl⟩
    change (MulAut.conj (n : G)) y * (MulAut.conj (n : G)) (into D k a) =
      (MulAut.conj (n : G)) (into D k a) * (MulAut.conj (n : G)) y
    simpa only [map_mul] using congrArg (MulAut.conj (n : G)) (haP y hy)
  have hna : (MulAut.conj (n : G)) (into D k a) = D.z := by
    rcases centralizes_caseIISylow D k _ hanT with hh | hh
    · have han : into D k a ≠ 1 := by
        intro he
        have ha1 : a = 1 := (into_injective D k) (he.trans (map_one _).symm)
        have ho := actor_orders.1
        simp [ha1] at ho
      exact (han ((MulAut.conj (n : G)).injective (hh.trans (map_one _).symm))).elim
    · exact hh
  refine ⟨n⁻¹, ?_⟩
  have hh := congrArg (MulAut.conj (n : G)⁻¹) hna
  simpa [MulAut.conj_apply, mul_assoc] using hh.symm

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.ActorFusion
