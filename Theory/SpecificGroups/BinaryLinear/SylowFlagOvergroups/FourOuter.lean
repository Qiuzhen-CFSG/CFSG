module
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.UniqueMaximal
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.AutomorphismActions
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Outer-invariant Sylow overgroups in binary dimension four

A proper flag stabilizer invariant under an outer automorphism preserving
its full Sylow flag has a reversal-invariant set of cuts. It lies either in
the solvable middle 2+2 parabolic or in the solvable middle minimal parabolic.
Consequently a nonsolvable proper subgroup normalized by the Sylow admits
only inner automorphisms preserving both subgroups. The actual flag and
subgroup images are retained throughout.

Source: Aschbacher–Smith, 12.2.7, printed pp.797–798, the A₈ = SL₄(2)
overcomponent exclusion. The original terminal application is in
TerminalComponentProperEight.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear.SylowFlagOvergroups
open OuterCyclic InvariantNodeActions SmallParabolicLevi
private instance {n : ℕ} : Finite (BinaryLinear.GL (Space n)) := Finite.of_injective
  (fun g : BinaryLinear.GL (Space n) => (g : Space n → Space n)) DFunLike.coe_injective

private theorem middle_solvable (b : Basis 3) :
    Group.IsSolvable (cutStabilizer b ({1} : Set (Fin 3))) := by
  let W := cutSpace b (1 : Fin 3)
  have hd : Module.finrank (ZMod 2) W = 2 := cutSpace_finrank b 1
  have hq : Module.finrank (ZMod 2) (Space 4 ⧸ W) = 2 := by
    have hh := Submodule.finrank_quotient_add_finrank W
    simp only [hd, Space, Module.finrank_fin_fun] at hh
    change Module.finrank (ZMod 2) (Space 4 ⧸ W) + 2 = 4 at hh
    omega
  let a : W ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
  let c : (Space 4 ⧸ W) ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofFinrankEq _ _ (by simpa using hq)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Group.isSolvable_of_isSolvable_injective (f := Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb (by decide : 3 ≤ 4)))
      (Equiv.Perm.viaEmbeddingHom_injective _)
  let e := (quotientTwoCoreEquivOfCoordinates W a c).trans
    (linearTwoEquivSymmetricThree.prodCongr linearTwoEquivSymmetricThree)
  let : Group.IsSolvable (parabolic W ⧸ pCore 2 (parabolic W)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsNilpotent (pCore 2 (parabolic W)) := pCore_isNilpotent
  have hs : Group.IsSolvable (parabolic W) :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 (parabolic W))).mpr
      ⟨inferInstance,inferInstance⟩
  have he : cutStabilizer b ({1} : Set (Fin 3)) = parabolic W := by
    ext g
    simp only [mem_cutStabilizer, Set.mem_singleton_iff, forall_eq]
    rfl
  exact he.symm ▸ hs

private theorem reverse_cuts (b : Basis 3) (a : MulAut (LinearGroup 4))
    (ha : a ∉ MulAut.innerSubgroup _)
    (hS : (cutStabilizer b Set.univ).map a.toMonoidHom = cutStabilizer b Set.univ)
    (s : Set (Fin 3)) (hs : (cutStabilizer b s).map a.toMonoidHom = cutStabilizer b s) :
    ∀ i : Fin 3, i.rev ∈ s ↔ i ∈ s := by
  obtain ⟨g,rfl⟩ := outer_eq_graph_inner (by decide) (by decide) a ha
  let a := graphLinear 4 * MulAut.conj g
  have hp (i : Fin 3) : (parabolic (cutSpace b i)).map a.toMonoidHom =
      parabolic (cutSpace b i.rev) := by
    rw [graph_inner_map_parabolic, graph_inner_cutSpace_of_fullFlag b g hS]
  have hi (i : Fin 3) : i ∈ s → i.rev ∈ s := by
    intro his
    have hle : cutStabilizer b s ≤ parabolic (cutSpace b i) :=
      fun x hx => (mem_cutStabilizer b s x).mp hx i his
    have hh := map_mono (f := a.toMonoidHom) hle
    rw [hs,hp] at hh
    have he : parabolic (cutSpace b i.rev) = cutStabilizer b {i.rev} := by
      ext x
      simp only [mem_cutStabilizer,Set.mem_singleton_iff,forall_eq]
      rfl
    rw [he] at hh
    exact (cutStabilizer_le_iff b s {i.rev}).mp hh (Set.mem_singleton _)
  intro i
  exact ⟨fun h => by simpa using hi i.rev h,hi i⟩

/-- A proper binary four-space Sylow overgroup preserved by an outer
Sylow-preserving automorphism is solvable. -/
theorem solvable_of_outer_invariant_four
    (S : Sylow 2 (LinearGroup 4)) (B : Subgroup (LinearGroup 4))
    (hSB : (S : Subgroup _) ≤ B) (hB : B ≠ ⊤)
    (a : MulAut (LinearGroup 4)) (ha : a ∉ MulAut.innerSubgroup _)
    (hS : (S : Subgroup _).map a.toMonoidHom = S)
    (hBa : B.map a.toMonoidHom = B) : Group.IsSolvable B := by
  classical
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer S
  obtain ⟨s,rfl⟩ := overgroup_eq_cutStabilizer S b hb B hSB
  have hr := reverse_cuts b a ha (by simpa only [hb] using hS) s hBa
  have hn : s.Nonempty := by
    by_contra he
    apply hB
    rw [Set.not_nonempty_iff_eq_empty.mp he]
    ext x
    simp only [mem_cutStabilizer,Set.mem_empty_iff_false,forall_false,forall_const,mem_top]
  by_cases hm : (1 : Fin 3) ∈ s
  · let := middle_solvable b
    exact Group.isSolvable_of_isSolvable_injective
      (f := inclusion ((cutStabilizer_le_iff b s {1}).mpr (Set.singleton_subset_iff.mpr hm)))
      (inclusion_injective _)
  · have hs : ({1} : Set (Fin 3))ᶜ ⊆ s := by
      obtain ⟨i,hi⟩ := hn
      have hzero : (0 : Fin 3) ∈ s := by
        fin_cases i
        · exact hi
        · exact (hm hi).elim
        · simpa using (hr 0).mp hi
      intro j hj
      fin_cases j
      · exact hzero
      · exact (hj rfl).elim
      · exact (hr 0).mpr hzero
    have ht : Group.IsSolvable (minimalParabolic b (1 : Fin 3)) :=
      solvable_of_uniqueMaximal S _
        (by
          have hc := fullFlag_covBy_minimalParabolic S b hb 1
          refine ⟨hc.lt, S, ⟨le_rfl,hc⟩, ?_⟩
          intro M hM
          exact ((hc.eq_or_eq hM.1 hM.2.le).resolve_right hM.2.ne))
    change Group.IsSolvable (cutStabilizer b ({1} : Set (Fin 3))ᶜ) at ht
    let := ht
    exact Group.isSolvable_of_isSolvable_injective
      (f := inclusion ((cutStabilizer_le_iff b s {1}ᶜ).mpr hs))
      (inclusion_injective _)

/-- A nonsolvable proper subgroup normalized by a full binary-four Sylow
admits only inner automorphisms preserving both subgroups. -/
theorem inner_of_preserves_nonsolvable_normalized_four
    (S : Sylow 2 (LinearGroup 4)) (B : Subgroup (LinearGroup 4))
    (hSB : (S : Subgroup _) ≤ normalizer (B : Set (LinearGroup 4))) (hB : B ≠ ⊤)
    (hns : ¬ Group.IsSolvable B)
    (a : MulAut (LinearGroup 4))
    (hS : (S : Subgroup _).map a.toMonoidHom = S)
    (hBa : B.map a.toMonoidHom = B) : a ∈ MulAut.innerSubgroup _ := by
  by_contra ha
  have hproper : B ⊔ (S : Subgroup _) ≠ ⊤ := by
    intro he
    let : B.Normal := normalizer_eq_top_iff.mp (top_unique (by
      rw [←he]
      exact sup_le B.le_normalizer hSB))
    let e : LinearGroup 4 ≃* alternatingGroup (Fin 8) :=
      (projectiveEquivLinear (by decide : 0 < 4)).symm.trans
        Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm
    let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup (LinearGroup 4) := e.isSimpleGroup
    rcases (inferInstance : B.Normal).eq_bot_or_eq_top with he | he
    · exact hns (he ▸ inferInstance)
    · exact hB he
  have hs := solvable_of_outer_invariant_four S (B ⊔ S) le_sup_right hproper a ha hS
    (by rw [Subgroup.map_sup,hBa,hS])
  let := hs
  exact hns (Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show B ≤ B ⊔ (S : Subgroup _) from le_sup_left)) (inclusion_injective _))
end BinaryLinear.SylowFlagOvergroups
