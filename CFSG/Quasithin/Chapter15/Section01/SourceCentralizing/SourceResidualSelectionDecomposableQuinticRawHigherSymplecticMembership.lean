module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherSymplecticLifts
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SymplecticMembership
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SymplecticMembership

/-!
# Both symplectic residuals in the original raw local family

One Sylow alignment preserves the actual marked parabolic. Its invariance
fixes the diagram, so both native residuals belong to the same original
local family. The internal import reuses only the two generic equivariance
proofs; no private declaration occurs in the public statement.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {G : Type*} [Group G] [Finite G]

/-- A literal marked symplectic core produces both residual memberships. -/
theorem PreparedChosenModule.raw_symplectic_core_residual_members
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 K : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (K ⧸ pCore 2 K) ≃* Sp F)
    (hm : ∃ g : Sp F,
      (((centralizer (Z1 : Set G) ⊓ Mc).subgroupOf K).map
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))).map
        (MulAut.conj g).toMonoidHom = pointParabolic ∨
      (((centralizer (Z1 : Set G) ⊓ Mc).subgroupOf K).map
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))).map
        (MulAut.conj g).toMonoidHom = planeParabolic) :
    ∃ e' : (K ⧸ pCore 2 K) ≃* Sp F,
      ∀ P ∈ ({pointParabolic,planeParabolic} : Set (Subgroup (Sp F))),
        let B := (P.comap (e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))).map K.subtype
        (solvableResidual B).map B.subtype ∈ Chapter1.LIn (centralizer (Z1 : Set G))
          ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) := by
  let G1 := centralizer (Z1 : Set G)
  let S := (T : Subgroup G) ⊓ G1
  let MZ := G1 ⊓ Mc
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hK.2
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  have hnK : S ≤ normalizer (K : Set G) := by
    apply h.raw_local_normalizes_of_oddRank hG T hZ hZne hK hq Nat.prime_three (by decide)
    rw [primeRank_equiv 3 e]
    exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic.trans
      (primeRank_subgroup_le 3 _)
  obtain ⟨Q,hQ⟩ := ComponentModels.source20_sylow_intersection hK.2
  let q₀ := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq₀ : Function.Surjective q₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp F) (Q.mapSurjective hq₀)
    (unipotentSylow hF hn.le)
  let e' := e.trans (MulAut.conj g)
  let ec' := e.trans (MulAut.conj g)
  let q := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hU : (Q : Subgroup K).map q = unipotent := by
    have hh := congrArg (fun U : Sylow 2 (Sp F) => (U : Subgroup (Sp F))) hg
    change ((Q : Subgroup K).map q₀).map (MulAut.conj g).toMonoidHom = unipotent at hh
    rw [map_map] at hh
    exact hh
  have hQL : (Q : Subgroup K) = (S ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [map_subgroupOf_eq_of_le (show S ⊓ K ≤ K from inf_le_right)]
    exact hQ
  let α : S →* MulAut (Sp F) := (MulAut.congr ec').toMonoidHom.comp
    ((quotientAut (pCore 2 K)).comp (K.normalizerMonoidHom.comp (inclusion hnK)))
  have heq (s : S) (k : K) :
      q (K.normalizerMonoidHom (inclusion hnK s) k) = α s (q k) := by
    have hc (x : K) : q x = ec' (QuotientGroup.mk' (pCore 2 K) x) := rfl
    rw [hc,hc]
    exact CaseIComponentData.quotient_marking_equivariant (pCore 2 K) ec'
      (K.normalizerMonoidHom (inclusion hnK s)) k
  have hnSK : S ≤ normalizer ((S ⊓ K) : Set G) :=
    (le_inf S.le_normalizer hnK).trans inf_normalizer_le_normalizer_inf
  have hUi (s : S) : unipotent.map (α s).toMonoidHom = unipotent := by
    have hh := EquivariantLift.map_invariant K q hnK α heq (D := S ⊓ K) hnSK s
    rw [←hQL,hU] at hh
    exact hh
  have hSM : S ≤ MZ := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro x hx
    exact ⟨(show S ≤ G1 from inf_le_right) hx,hMc.2 (fun z hz =>
      (centralInvolutions_le_centralizer_sylow T hz x ((show S ≤ (T : Subgroup G) from inf_le_left) hx)).symm)⟩
  let D := (MZ.subgroupOf K).map q
  have hDi (s : S) : D.map (α s).toMonoidHom = D :=
    EquivariantLift.map_invariant K q hnK α heq (hSM.trans MZ.le_normalizer) s
  have hDm : ∃ x : Sp F,
      D.map (MulAut.conj x).toMonoidHom = pointParabolic ∨
      D.map (MulAut.conj x).toMonoidHom = planeParabolic := by
    obtain ⟨x,hx⟩ := hm
    refine ⟨x*g⁻¹,?_⟩
    have he : D.map (MulAut.conj (x*g⁻¹)).toMonoidHom =
        ((MZ.subgroupOf K).map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))).map (MulAut.conj x).toMonoidHom := by
      change (((MZ.subgroupOf K).map _).map _) = _
      rw [map_map,map_map]
      congr 1
      ext k
      simp [q,e',mul_assoc]
    rwa [he]
  have hpair (s : S) :
      pointParabolic.map (α s).toMonoidHom = pointParabolic ∧
      planeParabolic.map (α s).toMonoidHom = planeParabolic := by
    apply parabolic_pair_map_of_unipotent_and_marked_class hF hn _ (hUi s)
    obtain ⟨x,hx⟩ := hDm
    rcases hx with hp | hp
    · exact Or.inl (CaseIComponentData.preserves_class_of_invariant D _ _ (hDi s) x hp)
    · exact Or.inr (CaseIComponentData.preserves_class_of_invariant D _ _ (hDi s) x hp)
  refine ⟨e',?_⟩
  intro P hP
  have hPi (s : S) : P.map (α s).toMonoidHom = P := by
    rcases hP with rfl | hP
    · exact (hpair s).1
    · have he : P = planeParabolic := hP
      subst P
      exact (hpair s).2
  let B := (P.comap q).map K.subtype
  let R := (solvableResidual B).map B.subtype
  have hnB : S ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    intro x hx b hb
    obtain ⟨k,hk,rfl⟩ := hb
    let x₀ : S := ⟨x,hx⟩
    refine ⟨K.normalizerMonoidHom (inclusion hnK x₀) k,?_,rfl⟩
    change q (K.normalizerMonoidHom (inclusion hnK x₀) k) ∈ P
    rw [heq]
    exact hPi x₀ ▸ mem_map_of_mem (α x₀).toMonoidHom hk
  have hnR : S ≤ normalizer (R : Set G) := by
    change S ≤ normalizer ((solvableResidual B).map B.subtype : Set G)
    exact hnB.trans (normalizer_le_normalizer_characteristic_image B (solvableResidual B))
  let : Group.IsPerfect R := Group.IsPerfect.map B.subtype
  have hsurj : Function.Surjective q := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : IsPGroup 2 q.ker := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ e'.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨hfit,⟨er⟩⟩ := RawClassicalResidual.symplectic_data K q hsurj hker hF hn P hP
  let : IsSimpleGroup SL(2,F) := NaturalExtension.model_simple (by omega)
  let : IsSimpleGroup (R ⧸ pCore 2 R) := er.isSimpleGroup
  let : Nontrivial R := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (pCore 2 R))
  have hz : center (R ⧸ pCore 2 R) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (R ⧸ pCore 2 R)) inferInstance with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hz)).elim
  let : IsQuasisimple (R ⧸ pCore 2 R) :=
    { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hc : R.pCoreIn 2 ≠ ⊥ := by
    intro hh
    have hb : pCore 2 R = ⊥ := (map_eq_bot_iff_of_injective _ R.subtype_injective).mp hh
    have ht := centralizer_generalizedFitting_le R
    rw [hfit,hb] at ht
    rw [show centralizer ((⊥ : Subgroup R) : Set R) = ⊤ from
      centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup R) ≤ center R from bot_le)] at ht
    have ht' : (⊤ : Subgroup R) = ⊥ := bot_unique ht
    exact (top_ne_bot : (⊤ : Subgroup R) ≠ ⊥) ht'
  have hRK : R ≤ K := (map_subtype_le _).trans (map_subtype_le _)
  exact ⟨hRK.trans hK.1,
    (Chapter1.mem_LIn_of_normalized_perfect hK.2.2.1
      (hRK.trans le_sup_left) hnR hc).2⟩


end CFSG.Quasithin.Chapter15.Section01
