module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Transport
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Filters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.SymplecticNativeApplication

/-!
# Original A5-pair core control in the reduced symplectic row

The binary native endpoints are solvable. In every surviving degree their
cores lie in the perfect determinant kernels, which are their solvable
residuals. Reduction therefore identifies the original A5 factors with
the original parabolic residuals. The restored full endpoint maps supply
the actual inner-factor markings.

The native quotient-action kernel calculation then compares both original
join cores without a splitting assumption. The original one-normalized-
Borel argument gives both containments, in either point/plane orientation.

Source: DGS (15.2), pp.226–228; Aschbacher–Smith F.1.12(I)(2), pp.262–264.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.A5PairCatalogue.Symplectic
open Subgroup Theory.GroupTheory RankTwoAmalgam
open DGS85.OriginalExtension
open Chapter6.Source.RankOneGeneric.Global.OriginalSymplectic
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open scoped MatrixGroups commutatorElement
variable (F : Type) [Field F] [Finite F] [CharP F 2]
omit [Finite F] in
private theorem inner_injective : Function.Injective (MulAut.conj : Sp F →* MulAut (Sp F)) :=
  Theory.GroupTheory.conj_injective_of_center_eq_bot EvenProjective.center_eq_bot

omit [Finite F] in
private theorem local_join_core (K : Subgroup (Sp F))
    (hdetect : ∀ (a : MulAut (Sp F)) (hK : K.map a.toMonoidHom = K),
      (∃ k : ℕ, a^(2^k)=1) →
      (∀ x : K, restrict a K hK x / x ∈ pCore 2 K) →
      ∃ k : K, a = MulAut.conj k.val)
    (U : Subgroup (MulAut (Sp F))) (hn : U ≤ normalizer (K.map MulAut.conj : Set _)) :
    (K.map MulAut.conj ⊔ U).pCoreIn 2 = (K.map MulAut.conj).pCoreIn 2 := by
  apply join_pCore_eq_of_quotient_action_detection 2 _ U hn
  intro a ha htwo hc
  have hnorm : a ∈ normalizer (K.map MulAut.conj : Set _) :=
    (sup_le (K.map MulAut.conj).le_normalizer hn) ha
  have hK : K.map a.toMonoidHom = K := by
    apply Subgroup.map_injective (inner_injective F)
    have he : MulAut.conj.comp a.toMonoidHom =
        (MulAut.conj a).toMonoidHom.comp MulAut.conj := by
      ext x y
      simp
    rw [map_map,he,←map_map]
    exact mem_normalizer_iff_map_conj_eq.mp hnorm
  have hdiff (x : K) : restrict a K hK x / x ∈ pCore 2 K := by
    have hh := hc ⟨MulAut.conj x.val,mem_map_of_mem MulAut.conj x.property⟩
    change ⁅a,MulAut.conj x.val⁆ ∈ (K.map MulAut.conj).pCoreIn 2 at hh
    rw [←map_pCoreIn_of_injective 2 _ _ (inner_injective F)] at hh
    have he : MulAut.conj (restrict a K hK x / x).val = ⁅a,MulAut.conj x.val⁆ := by
      apply MulEquiv.ext
      intro y
      change (a x.val / x.val) * y * (a x.val / x.val)⁻¹ =
        a (x.val * a.symm (x.val⁻¹ * y * x.val) * x.val⁻¹)
      simp only [div_eq_mul_inv,map_mul,map_inv,MulEquiv.apply_symm_apply]
      group
    rw [←he] at hh
    exact (mem_map_iff_mem K.subtype_injective).mp
      ((mem_map_iff_mem (inner_injective F)).mp hh)
  obtain ⟨k,hk⟩ := hdetect a hK htwo hdiff
  rw [hk]
  exact mem_map_of_mem MulAut.conj k.property

private theorem native_core_eq {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2^m)
    (point : Bool) (U : Subgroup (MulAut (Sp F)))
    (hn : U ≤ normalizer ((localFactor F point).map MulAut.conj : Set _)) :
    ((localFactor F point).map MulAut.conj ⊔ U).pCoreIn 2 =
      ((localFactor F point).map MulAut.conj).pCoreIn 2 := by
  apply local_join_core F _ ?_ U hn
  intro a hK htwo hc
  cases point
  · obtain ⟨k,_,hk⟩ := plane_core_inner_of_quotient_trivial hF hm a hK htwo hc
    exact ⟨k,hk⟩
  · obtain ⟨k,_,hk⟩ := point_core_inner_of_quotient_trivial hF hm a hK htwo hc
    exact ⟨k,hk⟩

variable {X : Type*} [Group X] (K U : Subgroup X)
  (hn : U ≤ normalizer (K : Set X))
  (f : X →* MulAut (Sp F)) (hf : Function.Injective f) (point : Bool)
  (hK : K.map f = (localFactor F point).map MulAut.conj)

include hn hf hK in
private theorem core_eq {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2^m) :
    (K ⊔ U).pCoreIn 2 = K.pCoreIn 2 := by
  apply Subgroup.map_injective hf
  rw [map_pCoreIn_of_injective 2 _ _ hf,map_pCoreIn_of_injective 2 _ _ hf,
    Subgroup.map_sup,hK]
  apply native_core_eq F hm hF point (U.map f)
  rw [←hK]
  exact (map_mono hn).trans (le_normalizer_map f)


private theorem model_core_le_residual {n : ℕ} (hF : Nat.card F = 2^n)
    (hn : 1<n) (b : Bool) :
    pCore 2 (SymplecticNative.endpoint F b) ≤
      solvableResidual (SymplecticNative.endpoint F b) := by
  cases b
  · change pCore 2 (planeParabolic (F := F)) ≤ solvableResidual (planeParabolic (F := F))
    apply (map_le_map_iff_of_injective planeParabolic.subtype_injective).mp
    rw [planeParabolic_solvableResidual_eq hF hn,←planeLocal_core_map]
    exact map_subtype_le _
  · change pCore 2 (pointParabolic (F := F)) ≤ solvableResidual (pointParabolic (F := F))
    apply (map_le_map_iff_of_injective pointParabolic.subtype_injective).mp
    rw [pointParabolic_solvableResidual_eq hF hn,←pointLocal_core_map]
    exact map_subtype_le _

private theorem original_local_core
    {G : Type*} [Group G] [Finite G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (i : Fin 2)
    (a : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n) (b : Bool)
    (e : parabolic L (SuzukiContainment.reducedSylow L S) i ≃* SymplecticNative.endpoint F b)
    (f : parabolic L S i →* MulAut (Sp F)) (hf : Function.Injective f)
    (hr : (solvableResidual (parabolic L S i)).map f =
      (localFactor F b).map MulAut.conj) :
    twoCore (L i ⊔ S) = twoCore (L i) := by
  let P := parabolic L S i
  have hLP : L i ≤ P := le_sup_left.trans le_sup_left
  have hSP : S ≤ P := le_sup_right.trans le_sup_left
  have he : (L i).subgroupOf P = solvableResidual P := by
    apply map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le hLP]
    exact local_eq_residual_of_reduced_equiv h i a e (model_core_le_residual F hF hn b)
  have hmark : ((L i).subgroupOf P).map f = (localFactor F b).map MulAut.conj := by
    rw [he]
    exact hr
  have hnorm : S.subgroupOf P ≤ normalizer ((L i).subgroupOf P : Set P) := by
    rw [←subgroupOf_normalizer_eq hLP]
    exact comap_mono (h.S_normalizes i)
  have hh := congrArg (map P.subtype) (core_eq F ((L i).subgroupOf P)
    (S.subgroupOf P) hnorm f hf b hmark hn hF)
  rw [map_pCoreIn_of_injective 2 _ _ P.subtype_injective,
    map_pCoreIn_of_injective 2 _ _ P.subtype_injective,Subgroup.map_sup,
    map_subgroupOf_eq_of_le hLP,map_subgroupOf_eq_of_le hSP] at hh
  exact hh

variable {G : Type*} [Group G] [Finite G] {K R S : Subgroup G}

omit [CharP F 2] [Finite G] in
private theorem parameter
    (a : ∀ i, Nonempty ((![K,R] i ⧸ pCore 2 (![K,R] i)) ≃* alternatingGroup (Fin 5)))
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0<n) (b : Bool)
    (e : Iso (reducedAmalgam ![K,R] S) (SymplecticNative.amalgam F b)) : 1<n := by
  by_contra hgt
  have hn1 : n = 1 := by omega
  have hc : Nat.card F = 2 := by simpa only [hn1,pow_one] using hF
  let c : SymplecticNative.endpoint F (!b) ≃* Binary.LocalProduct := by
    cases b
    · exact Binary.pointParabolicEquivProd hc
    · exact Binary.planeParabolicEquivProd hc
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin 2)) := Group.isSolvable_of_comm (by decide)
  let j := e.right.trans c
  exact overgroup_not_solvable 1 (a 1).some (le_sup_left.trans le_sup_left)
    (Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective)

/-- Both original factors in the full symplectic row, without an assumed
perfect-factor marking or a splitting of either original extension. -/
theorem core_and_containment (h : HypothesisF11 ![K,R] S)
    (a : ∀ i, Nonempty ((![K,R] i ⧸ pCore 2 (![K,R] i)) ≃* alternatingGroup (Fin 5)))
    (hnorm : ∃ j, borel (![K,R] j) S ≤ normalizer (S : Set G))
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0<n) (b : Bool)
    (e : Iso (reducedAmalgam ![K,R] S) (SymplecticNative.amalgam F b)) :
    (∀ i, twoCore (![K,R] i ⊔ S) = twoCore (![K,R] i)) ∧
      (∀ i, S ≤ ![K,R] i) := by
  have hn' := parameter F a hF hn b e
  obtain ⟨f⟩ := exists_original_symplectic_marking_of_reduced_iso h F hF hn' b e
  have hc : ∀ i, twoCore (![K,R] i ⊔ S) = twoCore (![K,R] i) := by
    intro i
    fin_cases i
    · exact original_local_core F h 0 (a 0).some hF hn' b e.left
        f.left f.left_injective f.left_residual
    · exact original_local_core F h 1 (a 1).some hF hn' (!b) e.right
        f.right f.right_injective f.right_residual
  exact ⟨hc,h.a5_pair_containment_of_core_eq a hnorm hc⟩

end CFSG.Quasithin.ChapterF.Source.A5PairCatalogue.Symplectic
