module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.SymplecticFourMarking
public import Theory.GroupTheory.EquivariantParabolicLift
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.MarkedParabolicPair
public import Theory.SpecificGroups.SymplecticFour.Sylow.Normalizer

/-!
# Two invariant parabolics of the original symplectic component

Align the component Sylow with the standard unipotent subgroup. The image
of the actual solvable supplement intersection has characteristic Sylow.
The marked C.2.7 parabolic fixes a diagram type, so both incident parabolics
are invariant. Their full preimages are proper, generate the original
component, and contain its intersection with the supplement.

Source: Aschbacher–Smith 15.3.20, printed pp.1127–1128.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Theory.SpecificGroups.SymplecticFour DiagramAutomorphisms
variable {G : Type*} [Group G] [Finite G]

private theorem preserves_class_of_conjugate
    {F : Type*} [Field F] (a : MulAut (Sp F)) (M P : Subgroup (Sp F))
    (hM : M.map a.toMonoidHom = M) (g : Sp F)
    (hg : M.map (MulAut.conj g).toMonoidHom = P) : PreservesParabolicClass a P := by
  refine ⟨a g * g⁻¹,?_⟩
  calc
    P.map a.toMonoidHom = (M.map (MulAut.conj g).toMonoidHom).map a.toMonoidHom := by rw [hg]
    _ = (M.map a.toMonoidHom).map (MulAut.conj (a g)).toMonoidHom := by
      rw [map_map,map_map]
      congr 1
      ext x
      simp
    _ = M.map (MulAut.conj (a g)).toMonoidHom := by rw [hM]
    _ = P.map (MulAut.conj (a g * g⁻¹)).toMonoidHom := by
      rw [←hg,map_map]
      congr 1
      ext x
      simp [mul_assoc]

/-- The two original parabolics from a symplectic core marking. -/
theorem symplecticFour_original_parabolic_pair
    {I L R M A : Subgroup G} (h : Input KnownSimple.IsKnownSimple I R M L)
    (hn : A ≤ normalizer (L : Set G)) (hAM : A ≤ M)
    (hsol : Group.IsSolvable A) (T : Sylow 2 L)
    (hTA : (T : Subgroup L) ≤ A.subgroupOf L)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (e : (L ⧸ pCore 2 L) ≃* Sp F) :
    ∃ P Q : Subgroup G, P < L ∧ Q < L ∧ P ⊔ Q = L ∧
      A ≤ normalizer (P : Set G) ∧ A ≤ normalizer (Q : Set G) ∧ A ⊓ L ≤ P ⊓ Q := by
  let q₀ := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq₀ : Function.Surjective q₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let U₀ := T.mapSurjective hq₀
  let U := unipotentSylow (show Nat.card F = 2^2 by omega) (by decide)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp F) U₀ U
  let e' := e.trans (MulAut.conj g)
  let q := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hT : (T : Subgroup L).map q = unipotent := by
    have hh := congrArg (fun V : Sylow 2 (Sp F) => (V : Subgroup (Sp F))) hg
    change ((T : Subgroup L).map q₀).map (MulAut.conj g).toMonoidHom = unipotent at hh
    rw [map_map] at hh
    exact hh
  let α : A →* MulAut (Sp F) := (MulAut.congr e').toMonoidHom.comp
    ((quotientAut (pCore 2 L)).comp (L.normalizerMonoidHom.comp (inclusion hn)))
  have heq (a : A) (l : L) :
      q (L.normalizerMonoidHom (inclusion hn a) l) = α a (q l) := by
    change e' (QuotientGroup.mk' _ _) = e' (quotientAut _ _ (e'.symm (e' _)))
    rw [e'.symm_apply_apply,quotientAut_apply_mk]
    rfl
  let B := (A.subgroupOf L).map q
  let : Group.IsSolvable A := hsol
  let i : (A.subgroupOf L) →* A :=
    {toFun := fun a => ⟨a.val.val,a.property⟩,map_one' := rfl,map_mul' := fun _ _ => rfl}
  let : Group.IsSolvable (A.subgroupOf L) := Group.isSolvable_of_isSolvable_injective
    (f := i) (by
      intro a b hab
      have hv : (a.val.val : G) = b.val.val := congrArg (fun z : A => (z : G)) hab
      exact Subtype.ext (Subtype.ext hv))
  have hBsol : Group.IsSolvable B := Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
  have hUB : unipotent ≤ B := hT ▸ map_mono hTA
  have hBN : B ≤ normalizer (unipotent (F := F) : Set (Sp F)) :=
    solvable_overgroups_of_orthogonal_root_orbits
      (show Nat.card F = 2^2 by omega) (by decide)
      (fun D hs hu => solvable_unipotent_point_orbit_orthogonal (by omega) D hs hu)
      U B hBsol hUB
  have hBb : B ≤ pointParabolic ⊓ planeParabolic := by
    exact hBN.trans_eq borel_eq_normalizer_unipotent.symm
  have hBinv (a : A) : B.map (α a).toMonoidHom = B :=
    EquivariantLift.map_invariant L q hn α heq A.le_normalizer a
  have hMinv (a : A) : ((M.subgroupOf L).map q).map (α a).toMonoidHom =
      (M.subgroupOf L).map q :=
    EquivariantLift.map_invariant L q hn α heq (hAM.trans M.le_normalizer) a
  obtain ⟨k,hk⟩ := symplecticFour_core_parabolic h hF e'
  have hpair (a : A) : pointParabolic.map (α a).toMonoidHom = pointParabolic ∧
      planeParabolic.map (α a).toMonoidHom = planeParabolic := by
    apply parabolic_pair_map_of_solvable_marked_overgroup
      (show Nat.card F = 2^2 by omega) (by decide) B hBsol hUB (α a) (hBinv a)
    rcases hk with hp | hp
    · exact Or.inl (preserves_class_of_conjugate (α a) _ _ (hMinv a) k hp)
    · exact Or.inr (preserves_class_of_conjugate (α a) _ _ (hMinv a) k hp)
  refine ⟨EquivariantLift.lift L q pointParabolic,EquivariantLift.lift L q planeParabolic,
    EquivariantLift.lift_lt L q hq pointParabolic_ne_top,
    EquivariantLift.lift_lt L q hq planeParabolic_ne_top,?_,
    EquivariantLift.normalizes_lift L q hn α heq (fun a => (hpair a).1),
    EquivariantLift.normalizes_lift L q hn α heq (fun a => (hpair a).2),?_⟩
  · rw [←EquivariantLift.lift_sup L q hq,parabolics_sup_eq_top,EquivariantLift.lift_top]
  · apply le_inf
    · apply EquivariantLift.le_lift L q inf_le_right
      simpa only [inf_subgroupOf_right] using hBb.trans inf_le_left
    · apply EquivariantLift.le_lift L q inf_le_right
      simpa only [inf_subgroupOf_right] using hBb.trans inf_le_right
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
