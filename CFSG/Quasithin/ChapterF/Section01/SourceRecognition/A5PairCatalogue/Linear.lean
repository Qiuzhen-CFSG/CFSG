module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Transport
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Filters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.LinearNative
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.AmbientLocalCores

/-!
# Original A5-pair core control in the reduced linear row

The binary point parabolic is solvable and cannot contain an original
A5-marked factor. At every other field degree, the native core calculation
places each model parabolic core in its concrete solvable residual. The
unchanged reduced cores and residuals then construct both original-factor
markings, without assuming either original factor perfect.

Native DGS restoration carries those markings into the full automorphism
group of PSL3. The local normalizer/core calculation applies to the image
of the original S and yields both literal join-core equalities. One
normalized original Borel suffices for both containments. Both orientations
and the full odd-inclusive overlap of the supplied Iso are retained.

Source: DGS (15.2), pp.226–228; Aschbacher–Smith F.1.12(I)(1) and its proof,
printed pp.262–264. The input is a genuine reduced linear comparison, not
an original marking, a splitting, or a recognition callback.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.A5PairCatalogue
open Subgroup Theory.GroupTheory RankTwoAmalgam
open DGS85.OriginalExtension Matrix.PSL3 Matrix.PSL3.LinearThree
open SourceCompletion.LinearThreeEven
open scoped MatrixGroups

private theorem binary_point_solvable (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2) : Group.IsSolvable (pointParabolic F) := by
  let := Fintype.ofFinite F
  let e : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by rwa [← Nat.card_eq_fintype_card])).symm
  have hu : ∀ a : F, a ≠ 0 → a = 1 := by
    intro a ha
    apply e.injective
    have hne : e a ≠ 0 := by simpa only [map_ne_zero] using ha
    have h : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
    simpa only [map_one] using h (e a) hne
  have hp : pointLocalSL F = pointParabolicSL F := by
    apply le_antisymm (pointLocalSL_le F)
    intro g hg
    have h := (mem_pointParabolicSL_iff F g).mp hg
    have hn : g.val 0 0 ≠ 0 := by
      intro hz
      have hi := congrArg (fun a : Matrix.SpecialLinearGroup (Fin 3) F => a.val 0 0)
        (inv_mul_cancel g)
      change (g⁻¹.val * g.val) 0 0 = 1 at hi
      simp [Matrix.mul_apply, Fin.sum_univ_three, h.1, h.2, hz] at hi
    exact (mem_pointLocalSL_iff F g).mpr ⟨hu _ hn,h⟩
  have he : pointLocal F = pointParabolic F :=
    congrArg (fun K => K.map (Matrix.PSL3.projection F)) hp
  rw [← he]
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  exact Group.isSolvable_of_isSolvable_injective
    (f := (ChapterF.GreenBook.LieModels.LinearThree.pointLocalEquivS4 F hF).toMonoidHom)
    (ChapterF.GreenBook.LieModels.LinearThree.pointLocalEquivS4 F hF).injective

private theorem linear_model_residual (F : Type) [Field F] [Finite F]
    (hc : 4 ≤ Nat.card F) (b : Bool) :
    (solvableResidual (SmallCompletion.parabolic F b)).map
      (SmallCompletion.parabolic F b).subtype = OuterExtensions.localFactor F (!b) := by
  cases b
  · exact ParabolicResiduals.pointParabolic_residual F hc
  · exact ParabolicResiduals.lineParabolic_residual F hc

private theorem linear_model_core_le_residual (F : Type) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n) (b : Bool) :
    pCore 2 (SmallCompletion.parabolic F b) ≤
      solvableResidual (SmallCompletion.parabolic F b) := by
  let P := SmallCompletion.parabolic F b
  let K := OuterExtensions.localFactor F (!b)
  have hc : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 2^2 ≤ 2^n from Nat.pow_le_pow_right (by decide) hn)
  have hr : (solvableResidual P).map P.subtype = K := linear_model_residual F hc b
  have hKP : K ≤ P := hr ▸ map_subtype_le _
  have hnP : P ≤ normalizer (K : Set PSL(3,F)) := by
    rw [←hr]
    simpa only [normalizer_eq_top, ←MonoidHom.range_eq_map, range_subtype] using
      (solvableResidual P).le_normalizer_map P.subtype
  have hh := OuterExtensions.AmbientLocalCores.local_join_core_in_aut
    F (by omega : 0<n) hF (!b) (P.map MulAut.conj) (by
      rintro a ⟨x,hx,rfl⟩
      exact mem_normalizer_iff_map_conj_eq.mp (hnP hx))
  have hcore : (K ⊔ P).pCoreIn 2 = K.pCoreIn 2 := by
    apply map_injective (Matrix.PSL3.ExtensionBorel.inner_injective F)
    rw [map_pCoreIn_of_injective 2 _ _ (Matrix.PSL3.ExtensionBorel.inner_injective F),
      map_pCoreIn_of_injective 2 _ _ (Matrix.PSL3.ExtensionBorel.inner_injective F), Subgroup.map_sup]
    exact hh
  rw [sup_eq_right.mpr hKP] at hcore
  apply (map_le_map_iff_of_injective P.subtype_injective).mp
  change P.pCoreIn 2 ≤ _
  rw [hr,hcore]
  exact map_subtype_le _

private theorem linear_core_of_marking {X : Type*} [Group X]
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0<n)
    (K U : Subgroup X) (hU : U ≤ normalizer (K : Set X))
    (f : X →* MulAut PSL(3,F)) (hf : Function.Injective f) (b : Bool)
    (hK : K.map f = (OuterExtensions.localFactor F b).map MulAut.conj) :
    (K ⊔ U).pCoreIn 2 = K.pCoreIn 2 := by
  apply map_injective hf
  rw [map_pCoreIn_of_injective 2 _ _ hf,map_pCoreIn_of_injective 2 _ _ hf,Subgroup.map_sup,hK]
  apply OuterExtensions.AmbientLocalCores.local_join_core_in_aut F hn hF b (U.map f)
  rintro a ⟨x,hx,rfl⟩
  apply map_injective (Matrix.PSL3.ExtensionBorel.inner_injective F)
  have he : (MulAut.conj (f x)).toMonoidHom.comp MulAut.conj =
      MulAut.conj.comp (f x).toMonoidHom := by
    ext y z
    simp
  rw [map_map,←he,←map_map,←hK]
  have he' : (MulAut.conj (f x)).toMonoidHom.comp f =
      f.comp (MulAut.conj x).toMonoidHom := by
    ext y
    simp
  rw [map_map,he',←map_map]
  have hxK := mem_normalizer_iff_map_conj_eq.mp (hU hx)
  change K.map (MulAut.conj x).toMonoidHom = K at hxK
  rw [hxK]

variable {G : Type*} [Group G] [Finite G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The nonbinary reduced linear row controls both ORIGINAL join cores.
The actual factor markings are derived from the A5 quotients and reduced
residuals before native restoration is applied. -/
theorem linear_join_cores (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n) (b : Bool)
    (e : Iso (reducedAmalgam L S) (LinearNative.amalgam F b)) :
    ∀ i, twoCore (L i ⊔ S) = twoCore (L i) := by
  let c := LinearNative.reducedCompletion F b e
  have hmark (i : Fin 2) :
      ∃ k : Bool, ((L i).subgroupOf
        (parabolic L (SuzukiContainment.reducedSylow L S) i)).map
        (completionEndpoint c i) = OuterExtensions.localFactor F k := by
    have hc : 4 ≤ Nat.card F := by
      rw [hF]
      exact (show 2^2 ≤ 2^n from Nat.pow_le_pow_right (by decide) hn)
    fin_cases i
    · refine ⟨!b, ?_⟩
      have hm := local_marking_of_reduced_equiv h 0 (a 0).some e.left
        (linear_model_core_le_residual F hF hn b)
      have hh := congrArg (map (SmallCompletion.parabolic F b).subtype) hm
      rw [map_map,linear_model_residual F hc b] at hh
      exact hh
    · refine ⟨!(!b), ?_⟩
      have hm := local_marking_of_reduced_equiv h 1 (a 1).some e.right
        (linear_model_core_le_residual F hF hn (!b))
      have hh := congrArg (map (SmallCompletion.parabolic F (!b)).subtype) hm
      rw [map_map,linear_model_residual F hc (!b)] at hh
      exact hh
  intro i
  obtain ⟨k,hk⟩ := hmark i
  obtain ⟨f,hf,hfactor⟩ := exists_original_endpoint_local_marking h c
    (LinearNative.reduced_preserved F h b e hF hn)
    (LinearNative.reduced_overlap F b e)
    (LinearNative.reduced_normalizer F b e hF (by omega)) i
    (OuterExtensions.localFactor F k) hk
  let P := parabolic L S i
  have hLP : L i ≤ P := le_sup_left.trans le_sup_left
  have hSP : S ≤ P := le_sup_right.trans le_sup_left
  have hnorm : S.subgroupOf P ≤ normalizer ((L i).subgroupOf P : Set P) := by
    rw [←subgroupOf_normalizer_eq hLP]
    exact comap_mono (h.S_normalizes i)
  have hh := congrArg (map P.subtype) (linear_core_of_marking F hF (by omega)
    ((L i).subgroupOf P) (S.subgroupOf P) hnorm f hf k hfactor)
  rw [map_pCoreIn_of_injective 2 _ _ P.subtype_injective,
    map_pCoreIn_of_injective 2 _ _ P.subtype_injective,Subgroup.map_sup,
    map_subgroupOf_eq_of_le hLP,map_subgroupOf_eq_of_le hSP] at hh
  exact hh

omit [Finite G] in
/-- Both original A5 quotients exclude the binary linear row in either
orientation, before any perfectness or local marking is asserted. -/
theorem linear_parameter
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0<n) (b : Bool)
    (e : Iso (reducedAmalgam L S) (LinearNative.amalgam F b)) : 1<n := by
  by_contra hgt
  have hn1 : n = 1 := by omega
  have hc : Nat.card F = 2 := by simpa only [hn1,pow_one] using hF
  let := binary_point_solvable F hc
  cases b
  · let j : _ ≃* pointParabolic F := e.left
    exact overgroup_not_solvable 0 (a 0).some (le_sup_left.trans le_sup_left)
      (Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective)
  · let j : _ ≃* pointParabolic F := e.right
    exact overgroup_not_solvable 1 (a 1).some (le_sup_left.trans le_sup_left)
      (Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective)

/-- The entire linear catalogue row, at every positive field degree and in
both orientations, gives both original cores and both original containments.
Only one original Borel is required to normalize S. -/
theorem linear_core_and_containment (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (hnorm : ∃ j, borel (L j) S ≤ normalizer (S : Set G))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0<n) (b : Bool)
    (e : Iso (reducedAmalgam L S) (LinearNative.amalgam F b)) :
    (∀ i, twoCore (L i ⊔ S) = twoCore (L i)) ∧ (∀ i, S ≤ L i) := by
  have hc := linear_join_cores h a F hF (linear_parameter a F hF hn b e) b e
  exact ⟨hc, h.a5_pair_containment_of_core_eq a hnorm hc⟩

end CFSG.Quasithin.ChapterF.Source.A5PairCatalogue
