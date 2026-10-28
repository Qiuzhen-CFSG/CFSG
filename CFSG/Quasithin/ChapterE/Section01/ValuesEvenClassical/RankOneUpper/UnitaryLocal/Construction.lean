module
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.Assembly
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.UnitaryLocal.OuterFixed
public import Theory.GroupTheory.SylowNormalizedSupIndex

/-!
# A concrete local subgroup for large unitary elementary subgroups

For an outer involution t in A, set M = C_L(t) and H = M τ(G,S,A).
When the ambient two-core is trivial, tau centralizes t and normalizes M.
If A contains a Sylow subgroup of M, the normalized-product index formula
makes tau Sylow in H. This proves the literal intrinsic Sylow intersection
in E.1.2(E0), with no change of the ambient S.

The fixed-subgroup identification proves M simple and nonabelian. Since
its containment in the ambient Borel would embed it in the solvable
intrinsic PSU₃ Borel, M and H escape that Borel. Elementary rank exceeding
f supplies an outer involution, using the exact inner two-rank f.

The Sylow-containment premise remains explicit, and these results do not
prove E2 or its quotient-rank bound. Source: Aschbacher–Smith E.1.1–6 and
E.1.14(1), pp.209–211, 214; GLS4 Chapter 4, Lemma 3.4(c).
-/

public section
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper.UnitaryLocal
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.Converse Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
variable {G : Type*} [Group G]

/-- The actual fixed subgroup in L, embedded in the ambient group. -/
@[expose] def fixedCore (L : Subgroup G) (t : G) : Subgroup G :=
  centralizer ({t} : Set G) ⊓ L

/-- The fixed linear subgroup extended by the ambient tau group. -/
@[expose] def localCandidate (L T A : Subgroup G) (t : G) : Subgroup G :=
  fixedCore L t ⊔ tau T A

/-- The PSL₂ identification retains the ambient embedding of the fixed subgroup. -/
theorem fixedCore_equiv (L : Subgroup G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3Model f)
    (hC : centralizer (L : Set G) = ⊥) (t : G) (ht : t ∉ L) (ht2 : t ^ 2 = 1) :
    Nonempty (fixedCore L t ≃* PSL2MatrixGroup (FixedBy.subfield (UField f) (uconj f))) := by
  obtain ⟨ef⟩ := outer_fixed_equiv L hf e hC t ht ht2
  let D := (centralizer ({t} : Set G)).subgroupOf L
  have hd : D.map L.subtype = fixedCore L t := subgroupOf_map_subtype _ _
  exact ⟨((D.equivMapOfInjective L.subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr hd)).symm.trans ef⟩

/-- With trivial two-core, ambient tau centralizes every element of A. -/
theorem tau_le_element_centralizer (T A : Subgroup G)
    (hO : pCore 2 G = ⊥) {t : G} (ht : t ∈ A) :
    tau T A ≤ centralizer ({t} : Set G) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  have hc := (mem_centralizerModulo_iff.mp hx).2 t ht
  rw [hO, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc.symm

/-- The actual ambient tau action preserves the fixed linear subgroup. -/
theorem tau_normalizes_fixedCore (L T A : Subgroup G) [L.Normal]
    (hO : pCore 2 G = ⊥) {t : G} (ht : t ∈ A) :
    tau T A ≤ normalizer (fixedCore L t : Set G) := by
  apply le_normalizer_iff.mpr
  intro x hx y hy
  have hc := tau_le_element_centralizer T A hO ht hx
  exact ⟨(centralizer ({t} : Set G)).mul_mem
    ((centralizer ({t} : Set G)).mul_mem hc hy.1)
    ((centralizer ({t} : Set G)).inv_mem hc),
    (inferInstance : L.Normal).conj_mem y hy.2 x⟩

/-- The chosen involution centralizes the whole candidate. -/
theorem localCandidate_le_centralizer (L T A : Subgroup G)
    (hO : pCore 2 G = ⊥) {t : G} (ht : t ∈ A) :
    localCandidate L T A t ≤ centralizer ({t} : Set G) :=
  sup_le inf_le_left (tau_le_element_centralizer T A hO ht)

variable [Finite G]

/-- A Sylow of the fixed group lying in A supplies all E0 containments and
the exact intrinsic Sylow intersection in the candidate. -/
theorem localCandidate_E0 (L : Subgroup G) [L.Normal] (S : Sylow 2 G)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAS : A ≤ (S : Subgroup G))
    (hO : pCore 2 G = ⊥) {t : G} (ht : t ∈ A)
    (P : Sylow 2 (fixedCore L t))
    (hPA : (P : Subgroup (fixedCore L t)).map (fixedCore L t).subtype ≤ A) :
    A ≤ localCandidate L (S : Subgroup G) A t ∧
    tau (S : Subgroup G) A ≤ localCandidate L (S : Subgroup G) A t ∧
    ∃ U : Sylow 2 (localCandidate L (S : Subgroup G) A t),
      (U : Subgroup (localCandidate L (S : Subgroup G) A t)) =
        (S : Subgroup G).subgroupOf (localCandidate L (S : Subgroup G) A t) := by
  let : IsElementaryAbelian 2 A := hA
  have hAD : A ≤ tau (S : Subgroup G) A := le_centralizerModulo_of_isMulCommutative hAS
  let H := localCandidate L (S : Subgroup G) A t
  have hD : IsPGroup 2 (tau (S : Subgroup G) A) :=
    S.isPGroup'.to_le (tau_le _ _)
  obtain ⟨U, hU⟩ := IsPGroup.exists_sylow_sup_of_coprime_index
    (fixedCore L t) (tau (S : Subgroup G) A) hD
    (tau_normalizes_fixedCore L (S : Subgroup G) A hO ht)
    (P : Subgroup (fixedCore L t)) P.not_dvd_index (hPA.trans hAD)
  refine ⟨hAD.trans le_sup_right, le_sup_right, U, ?_⟩
  have hUS : U.toSubgroup ≤ (S : Subgroup G).subgroupOf
      (fixedCore L t ⊔ tau (S : Subgroup G) A) :=
    map_le_iff_le_comap.mp (hU.le.trans (tau_le _ _))
  exact (Sylow.is_maximal' U
    (S.isPGroup'.comap_of_injective H.subtype Subtype.val_injective) hUS).symm

/-- Excess over the intrinsic rank forces an outer involution in A. -/
theorem exists_outer_involution_of_large_rank (L : Subgroup G)
    {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3Model f)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hr : f < Group.rank A) :
    ∃ t : G, t ∈ A ∧ t ∉ L ∧ t ^ 2 = 1 := by
  let : IsElementaryAbelian 2 A := hA
  have hnot : ¬ A ≤ L := by
    intro hAL
    let ea := subgroupOfEquivOfLe hAL
    let : IsElementaryAbelian 2 (A.subgroupOf L) :=
      IsElementaryAbelian.subgroupOf hAL
    have h := (A.subgroupOf L).rank_le_primeRank 2
      (IsElementaryAbelian.isPGroup 2 (A.subgroupOf L))
    rw [Group.rank_congr ea, inner_rank hf e] at h
    omega
  obtain ⟨t, htA, htL⟩ := SetLike.not_le_iff_exists.mp hnot
  exact ⟨t, htA, htL, elemPow_eq_one_of_isElementaryAbelian (A := A) t htA⟩

/-- Simplicity and nonabelianness are supplied by the actual fixed-field PSL₂. -/
theorem fixedCore_simple_nonabelian (L : Subgroup G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3Model f)
    (hC : centralizer (L : Set G) = ⊥) (t : G) (ht : t ∉ L) (ht2 : t ^ 2 = 1) :
    IsSimpleGroup (fixedCore L t) ∧ ¬ IsMulCommutative (fixedCore L t) := by
  let : NeZero f := ⟨by omega⟩
  obtain ⟨ec⟩ := fixedCore_equiv L hf e hC t ht ht2
  have hc : 4 ≤ Nat.card (FixedBy.subfield (UField f) (uconj f)) := by
    change 4 ≤ Nat.card {x : UField f // uconj f x = x}
    rw [card_fixed_UField f (by omega)]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hf
  let := BenderSuzuki.External.huppert_II_6_13
    (K := FixedBy.subfield (UField f) (uconj f)) 2 le_rfl
    (Or.inr (by omega)) (Or.inr (by omega))
  refine ⟨ec.isSimpleGroup_congr.mpr inferInstance, ?_⟩
  intro hab
  let := hab
  let : CommGroup (fixedCore L t) := IsMulCommutative.instCommGroup
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := fixedCore L t)
  have hP : ∃ P : Sylow 2 (fixedCore L t), (P : Subgroup (fixedCore L t)).Normal :=
    ⟨P, inferInstance⟩
  exact BenderSuzuki.ZD.UnitaryAutomorphisms.fixedField_psl2_no_normal_sylow
    (uform f) hf (card_fixed_UField f (by omega)) ((ec.exists_normal_sylow_iff 2).mp hP)

/-- The nonsolvable fixed subgroup escapes the solvable inner Borel. -/
theorem fixedCore_not_le_borel (L : Subgroup G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3Model f)
    (hC : centralizer (L : Set G) = ⊥) (S : Sylow 2 G)
    (t : G) (ht : t ∉ L) (ht2 : t ^ 2 = 1) :
    ¬ fixedCore L t ≤ normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
  obtain ⟨P, hP⟩ := S.exists_sylow_map_eq_inf_of_normal L
  have hB : (normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G)).comap L.subtype =
      normalizer (P : Set L) := by
    rw [← hP, comap_normalizer_eq_of_le_range (map_le_range _ _),
      comap_map_eq_self_of_injective Subtype.val_injective]
    rfl
  obtain ⟨hsimple, hnonabelian⟩ := fixedCore_simple_nonabelian L hf e hC t ht ht2
  let := hsimple
  let := (intrinsic_facts hf e P).solvable
  intro hle
  let j : fixedCore L t →* normalizer (P : Set L) :=
    { toFun x := ⟨⟨x.val, x.property.2⟩, by
        rw [← hB]
        exact hle x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : normalizer (P : Set L) => ((z : L) : G)) hxy)
  have hsolv := Group.isSolvable_of_isSolvable_injective hj
  exact hnonabelian ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr hsolv⟩⟩

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper.UnitaryLocal
