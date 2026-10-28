module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianExchangedTorus
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelStructure
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
/-!
# The original normal PSL₃ Sylow normalizer

The full normalizer of the original T intersect K is solvable, including
O₂(K). Its product with T lies in M by the original solvable-overgroup
argument. The original residual L₁ normalizes this Borel: its join with
the Borel is solvable, and solvable Sylow overgroups in PSL₃ lie in the
same Borel. This retains the full intrinsic kernel and the literal original
T intersect L action, whose displacements are cubic on the odd quotient.

Source: Aschbacher--Smith 12.6.31, printed pp.836--837.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)

include hz hTV hTz hbound hTI hns hH hKH in
/-- The original normalizer lies in M and is preserved by L₁T. -/
theorem SourceHypothesis.original_abelian_normal_linearThree_sylow_normalizer
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2^n)) :
    ∃ P : Sylow 2 K,
      (P : Subgroup K).map K.subtype = (T : Subgroup G) ⊓ K ∧
      let B := (normalizer (P : Set K)).map K.subtype
      B ≤ M L ∧ Group.IsSolvable B ∧
      (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G) ≤ normalizer (B : Set G) ∧
      B.pCoreIn 2 = (T : Subgroup G) ⊓ K := by
  let E := D.fullSetup hZ T z
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hnK : H ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKH).mp hn
  let : (K.subgroupOf H).Normal := hn
  obtain ⟨P₀,hP₀⟩ := (T.subtype hTH).exists_subgroupOf_eq_of_normal (K.subgroupOf H)
  let e₀ := subgroupOfEquivOfLe hKH
  let P := P₀.mapSurjective (f := e₀.toMonoidHom) e₀.surjective
  have hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K := by
    change (P₀ : Subgroup (K.subgroupOf H)).map e₀.toMonoidHom = _
    rw [hP₀]
    ext c
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ha
    · intro ht
      exact ⟨⟨⟨c,hKH c.property⟩,c.property⟩,ht,rfl⟩
  have hPmap : (P : Subgroup K).map K.subtype = (T : Subgroup G) ⊓ K := by
    rw [hP,subgroupOf_map_subtype]
  let B := (normalizer (P : Set K)).map K.subtype
  have hBeq : B = K ⊓ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
    have he : ((P : Subgroup K).map K.subtype).subgroupOf K = (P : Subgroup K) :=
      comap_map_eq_self_of_injective K.subtype_injective _
    have hh := subgroupOf_normalizer_eq (map_subtype_le (P : Subgroup K))
    rw [he] at hh
    change (normalizer (((P : Subgroup K).map K.subtype) : Set G)).subgroupOf K =
      normalizer (P : Set K) at hh
    change (normalizer (P : Set K)).map K.subtype = _
    rw [←hh,subgroupOf_map_subtype,hPmap,inf_comm]
  have hTB : (T : Subgroup G) ≤ normalizer (B : Set G) := by
    rw [hBeq]
    apply (le_inf (hTH.trans hnK) ?_).trans inf_normalizer_le_normalizer_inf
    apply le_trans (c := normalizer (normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) : Set G)) ?_
      (normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G)).le_normalizer
    exact (le_inf (T : Subgroup G).le_normalizer (hTH.trans hnK)).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨F,hF,hfin,hcardF,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let q : K →* PSL(3,F) := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
  let R := P.mapSurjective hq
  have hBN : (normalizer (P : Set K)).map q = normalizer (R : Set PSL(3,F)) := by
    exact P.normalizer_map_surjective q hq
  let : Group.IsSolvable (normalizer (R : Set PSL(3,F))) :=
    Matrix.PSL3.LinearThree.BorelStructure.sylowNormalizer_isSolvable F (by omega) hcardF R
  let : Group.IsNilpotent q.ker := (hk ▸ pCore_isPGroup).isNilpotent
  let : Group.IsSolvable (normalizer (P : Set K)) := by
    let : Group.IsSolvable ((normalizer (P : Set K)).map q) := hBN.symm ▸ inferInstance
    let : Group.IsSolvable (((normalizer (P : Set K)).map q).comap q) :=
      isSolvable_comap_of_solvable_ker q _
    exact Group.isSolvable_of_isSolvable_injective
      (inclusion_injective (le_comap_map q (normalizer (P : Set K))))
  let : Group.IsSolvable B := Group.isSolvable_of_surjective (K.subtype.subgroupMap_surjective _)
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  let : Group.IsSolvable (B ⊔ (T : Subgroup G) : Subgroup G) :=
    Group.isSolvable_sup_of_normalizes B T hTB
  have hBM : B ≤ M L := le_sup_left.trans
    (S.original_solvable_overgroup_le D hZ z hz hTV hTz hbound hTI hns le_sup_right)
  have hBL : B ≤ normalizer (E.L₁ : Set G) := by
    intro b hb
    have hbH : b ∈ H := hKH ((map_subtype_le _) hb)
    have hbNV : b ∈ normalizer (V : Set G) :=
      Mv_le_module_normalizer_of_TI hTI z hz ⟨hBM hb,by
        have hh := hH.2.1 hbH
        rwa [E.Gz_eq] at hh⟩
    exact S.original_module_normalizer_normalizes_residual D hZ z hTV hH ⟨hbH,hbNV⟩
  obtain ⟨_,_,_,e9,_,_⟩ := S.original_point_residual_quotient D hZ z hz hTz
  have hthree : IsPGroup 3 (E.L₁ ⧸ pCore 2 E.L₁) :=
    (IsElementaryAbelian.isPGroup 3 BinaryPermutation.TerminalOrthogonal.FourBlockResidual.E9).of_equiv e9.symm
  let : Group.IsNilpotent (pCore 2 E.L₁) := pCore_isPGroup.isNilpotent
  let : Group.IsNilpotent (E.L₁ ⧸ pCore 2 E.L₁) := hthree.isNilpotent
  let : Group.IsSolvable E.L₁ :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 E.L₁)).mpr ⟨inferInstance,inferInstance⟩
  let J := E.L₁ ⊔ B
  let : Group.IsSolvable J := Group.isSolvable_sup_of_normalizes E.L₁ B hBL
  let C := J.subgroupOf K
  let j : C →* J := (K.subtype.comp C.subtype).codRestrict J (fun x => x.property)
  have hj : Function.Injective j := by
    intro x y h
    have hv : x.val.val = y.val.val := congrArg (fun b : J => b.val) h
    exact Subtype.ext (Subtype.ext hv)
  let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective hj
  have hPC : (P : Subgroup K) ≤ C := fun x hx =>
    (le_sup_right : B ≤ J) (mem_map_of_mem K.subtype (P.le_normalizer hx))
  have hCN : C ≤ normalizer (P : Set K) := by
    let : Group.IsSolvable (C.map q) := Group.isSolvable_of_surjective (q.subgroupMap_surjective C)
    have hh := Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le
      F hn2 hcardF R (C.map q) inferInstance (map_mono hPC)
    rw [←hBN] at hh
    have h := map_le_iff_le_comap.mp hh
    rw [comap_map_eq] at h
    exact h.trans (sup_le le_rfl ((hk.symm ▸ pCore_isPGroup.le_sylow_of_normal P).trans P.le_normalizer))
  have hCB : J ⊓ K = B := by
    apply le_antisymm
    · intro x hx
      exact ⟨⟨x,hx.2⟩,hCN hx.1,rfl⟩
    · exact le_inf le_sup_right (map_subtype_le _)
  have hLB : E.L₁ ≤ normalizer (B : Set G) := by
    rw [←hCB]
    exact (le_inf (le_sup_left.trans J.le_normalizer)
      ((show E.L₁ ≤ H from fun x hx => hH.1.2 (Or.inl hx)).trans hnK)).trans
        inf_normalizer_le_normalizer_inf
  let N := normalizer (P : Set K)
  have hPN : (P : Subgroup K) ≤ N := P.le_normalizer
  have hc : N.pCoreIn 2 = (P : Subgroup K) := by
    apply le_antisymm
    · have hh := pCoreIn_le_sylow N (P.subtype hPN)
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hPN] using hh
    · exact le_pCoreIn_of_normalizes P.isPGroup' hPN le_rfl
  have hcore := congrArg (map K.subtype) hc
  rw [map_pCoreIn_of_injective 2 _ K.subtype K.subtype_injective,hPmap] at hcore
  exact ⟨P,hPmap,hBM,inferInstance,sup_le hLB hTB,hcore⟩
end CFSG.Quasithin.Chapter12.Section06
