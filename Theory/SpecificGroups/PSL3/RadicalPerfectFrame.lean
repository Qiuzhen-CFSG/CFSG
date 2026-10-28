module
public import Theory.SpecificGroups.PSL3.RadicalPerfectNormalizer
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.AmbientLocalCores

/-!
# Simultaneous projective radical and perfect-local frames

The radical lifts through the odd scalar kernel, while the solvable residual
of the perfect subgroup's inverse image projects onto that subgroup. Descending
the simultaneous SL₃ frame therefore retains both literal projective images.
The full parabolic core is its root plane, since the local contains an ambient
Sylow subgroup. These equations support the original Sylow and crossing actions.

Source: Aschbacher–Smith C.4.5–7 and 4.3.16, printed pp.152–153,618.
-/

public section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3.LinearThree.OuterExtensions
namespace Matrix.PSL3.LinearThree.RadicalNormalizer
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- One projective automorphism places both the full radical normalizer and
its specified nontrivial perfect normal subgroup in the same local frame. -/
theorem projective_radical_perfect_normal_frame
    (R B : Subgroup PSL(3,F)) (hR : R.IsPRadical 2)
    [Group.IsPerfect B] (hne : B ≠ ⊥)
    (hBN : B ≤ normalizer (R : Set PSL(3,F)))
    (hNB : normalizer (R : Set PSL(3,F)) ≤ normalizer (B : Set PSL(3,F)))
    {n : ℕ} (hn : 1<n) (hF : Nat.card F = 2^n) :
    ∃ (a : MulAut PSL(3,F)) (b : Bool),
      (normalizer (R : Set PSL(3,F))).map a.toMonoidHom = parabolic F b ∧
      B.map a.toMonoidHom = localFactor F b := by
  have hker : Nat.Coprime 2 (Nat.card (projection F).ker) := by
    rw [projection_ker]
    exact (Matrix.SL3.odd_card_center F).coprime_two_left
  obtain ⟨A,hA,_,hnA⟩ := exists_radical_lift_of_central_coprime (projection F)
    (projection_surjective F) (by rw [projection_ker]) hker R hR
  let q := projection F
  let U := (solvableResidual (B.comap q)).map (B.comap q).subtype
  let : Group.IsPerfect U := Group.IsPerfect.map _
  have hU : U.map q = B := by
    rw [map_solvableResidual_comap q (projection_surjective F),solvableResidual_eq_top,
      ←MonoidHom.range_eq_map,range_subtype]
  have hUn : U ≠ ⊥ := by
    intro he
    exact hne (by rw [←hU,he,Subgroup.map_bot])
  have hUN : U ≤ normalizer (A : Set SL(3,F)) := by
    rw [←hnA]
    exact (map_subtype_le _).trans (comap_mono hBN)
  have hNU : normalizer (A : Set SL(3,F)) ≤ normalizer (U : Set SL(3,F)) := by
    rw [←hnA]
    apply (comap_mono hNB).trans
    rw [comap_normalizer_eq_of_surjective _ (projection_surjective F)]
    exact normalizer_le_normalizer_characteristic_image (B.comap q) (solvableResidual _)
  obtain ⟨e,he⟩ := radical_perfect_normal_frame A U hA hUn hUN hNU hn hF
  let a := Matrix.HigherLinear.SubspaceTransport.slConj e
  let d := centerAction F a
  have hd : d.toMonoidHom.comp q = q.comp a.toMonoidHom := by
    ext x
    rfl
  have hmap (J : Subgroup SL(3,F)) :
      (J.map q).map d.toMonoidHom = (J.map a.toMonoidHom).map q := by
    rw [Subgroup.map_map,Subgroup.map_map,hd]
  have hnq : (normalizer (A : Set SL(3,F))).map q = normalizer (R : Set PSL(3,F)) := by
    rw [←hnA]
    exact map_comap_eq_self_of_surjective (projection_surjective F) _
  rcases he with he | he
  · refine ⟨d,true,?_,?_⟩
    · rw [←hnq,hmap,he.1]
      rfl
    · rw [←hU,hmap,he.2]
      rfl
  · refine ⟨d,false,?_,?_⟩
    · rw [←hnq,hmap,he.1]
      rfl
    · rw [←hU,hmap,he.2]
      rfl

/-- The two-core of the full parabolic is its literal root plane. -/
theorem parabolic_core_eq_rootPlane {n : ℕ} (hn : 0<n)
    (hF : Nat.card F = 2^n) (b : Bool) :
    (parabolic F b).pCoreIn 2 = rootPlane F b := by
  have hUL : unipotent F ≤ localFactor F b := by
    cases b
    · exact unipotent_le_lineLocal F
    · exact unipotent_le_pointLocal F
  have hLP : localFactor F b ≤ parabolic F b := by
    cases b
    · exact map_mono (lineLocalSL_le F)
    · exact map_mono (pointLocalSL_le F)
  have hRP : rootPlane F b ≤ parabolic F b := by
    rw [←normalizer_rootPlane F b]
    exact (rootPlane F b).le_normalizer
  have hR := AmbientLocalCores.local_core_eq_rootPlane F hn hF b
  have hcore : (parabolic F b).pCoreIn 2 ≤ localFactor F b := by
    have h := pCoreIn_le_sylow (parabolic F b)
      ((unipotentSylow F hn hF).subtype (hUL.trans hLP))
    change (parabolic F b).pCoreIn 2 ≤
      ((unipotent F).subgroupOf (parabolic F b)).map (parabolic F b).subtype at h
    rw [map_subgroupOf_eq_of_le (hUL.trans hLP)] at h
    exact h.trans hUL
  apply le_antisymm
  · rw [←hR]
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _) hcore
      (hLP.trans ((parabolic F b).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))))
  · apply le_pCoreIn_of_normalizes (hR ▸ isPGroup_pCoreIn 2 _) hRP
    rw [normalizer_rootPlane]

/-- The same frame identifies the radical itself and the full perfect local. -/
theorem projective_radical_perfect_root_frame
    (R B : Subgroup PSL(3,F)) (hR : R.IsPRadical 2)
    [Group.IsPerfect B] (hne : B ≠ ⊥)
    (hBN : B ≤ normalizer (R : Set PSL(3,F)))
    (hNB : normalizer (R : Set PSL(3,F)) ≤ normalizer (B : Set PSL(3,F)))
    {n : ℕ} (hn : 1<n) (hF : Nat.card F = 2^n) :
    ∃ (a : MulAut PSL(3,F)) (b : Bool),
      R.map a.toMonoidHom = rootPlane F b ∧
      B.map a.toMonoidHom = localFactor F b := by
  obtain ⟨a,b,hN,hB⟩ := projective_radical_perfect_normal_frame R B hR hne hBN hNB hn hF
  refine ⟨a,b,?_,hB⟩
  have hc : (normalizer (R : Set PSL(3,F))).pCoreIn 2 = R := hR.2
  rw [←hc,map_pCoreIn_of_injective 2 _ _ a.injective,hN,
    parabolic_core_eq_rootPlane (by omega) hF]

/-- A local Sylow can be aligned by conjugation inside that same local. This
keeps its characteristic root plane fixed. -/
theorem local_sylow_frame {n : ℕ} (hn : 0<n) (hF : Nat.card F = 2^n)
    (b : Bool) (P : Sylow 2 (localFactor F b)) :
    ∃ g : localFactor F b,
      (((P : Subgroup (localFactor F b)).map (localFactor F b).subtype).map
        (MulAut.conj g.val).toMonoidHom = unipotent F) ∧
      (rootPlane F b).map (MulAut.conj g.val).toMonoidHom = rootPlane F b := by
  have hUL : unipotent F ≤ localFactor F b := by
    cases b
    · exact unipotent_le_lineLocal F
    · exact unipotent_le_pointLocal F
  let P₀ := (unipotentSylow F hn hF).subtype hUL
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (localFactor F b) P P₀
  have hh := congrArg (fun Q : Sylow 2 (localFactor F b) =>
    (Q : Subgroup (localFactor F b)).map (localFactor F b).subtype) hg
  have hf : (localFactor F b).subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj g.val).toMonoidHom.comp (localFactor F b).subtype := rfl
  change ((P : Subgroup (localFactor F b)).map (MulAut.conj g).toMonoidHom).map
    (localFactor F b).subtype =
    ((unipotent F).subgroupOf (localFactor F b)).map (localFactor F b).subtype at hh
  rw [Subgroup.map_map,hf,←Subgroup.map_map,map_subgroupOf_eq_of_le hUL] at hh
  refine ⟨g,hh,mem_normalizer_iff_map_conj_eq.mp ?_⟩
  rw [normalizer_rootPlane]
  have hLP : localFactor F b ≤ parabolic F b := by
    cases b
    · exact map_mono (lineLocalSL_le F)
    · exact map_mono (pointLocalSL_le F)
  exact hLP g.property

end Matrix.PSL3.LinearThree.RadicalNormalizer
