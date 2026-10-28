module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFullQuotients
public import CFSG.Quasithin.Chapter3.Defs
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.CoreFlags
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.Covers
public import Theory.GroupTheory.SylowNormalIntersectionIndex
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure

/-!
# The marked rank-one parabolic in the doubled binary escape

The original cubic residual makes L₀T₀ have Sylow index three. Restriction
to the normal component preserves that index; the literal two-core quotient
therefore identifies its intersection with a minimal parabolic in the same
full flag as T₀ ∩ K.

If every element of T₀ acts internally, a one-cut flag stabilizer contains
this node and escapes the proper marked M-intersection. Its full preimage,
joined with T₀, is proper, contradicting the original minimal escape. Hence
an actual outer actor preserves the node. Graph duality forces the middle
node of SL₄(2), excluding SL₅(2). Both the quotient kernel and the action
marking remain explicit. The last lemma discharges the required minimality
from the original H* witness using its nontrivial central paired plane.

The Chapter12 companion applies this to the original chosen module.
Source: Aschbacher--Smith, proof of 7.7.3 after 7.7.10, printed p.709,
refs/quasithin.pdf, and the flag geometry of I.1.2--3, p.407.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryMarkedParabolic
open BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
variable {G : Type*} [Group G] [Finite G]

private theorem sylow_index_three {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) (hc : Nat.card (X ⧸ pCore 2 X) = 3) : S.index = 3 := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let P := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hi := S.index_map_of_two_kernel q (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  have hp : Nat.card P = 1 := by
    rw [P.card_eq_multiplicity,hc]
    norm_num [Nat.factorization]
  have hh := (P : Subgroup (X ⧸ pCore 2 X)).index_mul_card
  rw [hp,hc,hi,mul_one] at hh
  exact hh

theorem local_base_index (P : Sylow 2 G) (A : Subgroup G)
    (hn : (P : Subgroup G) ≤ normalizer (A : Set G))
    (hc : Nat.card (A ⧸ pCore 2 A) = 3) :
    (P : Subgroup G).relIndex (A ⊔ (P : Subgroup G)) = 3 := by
  let B := A ⊔ (P : Subgroup G)
  let S := P.subtype (show (P : Subgroup G) ≤ B from le_sup_right)
  let N := A.subgroupOf B
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  obtain ⟨S₀,hS₀⟩ := S.exists_subgroupOf_eq_of_normal N
  let e : N ≃* A := subgroupOfEquivOfLe le_sup_left
  have hcN : Nat.card (N ⧸ pCore 2 N) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
    exact hc
  have hgen : N ⊔ (S : Subgroup B) = ⊤ := by
    apply map_injective B.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show A ≤ B from le_sup_left),
      Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (P : Subgroup G) ≤ B from le_sup_right),
      ←MonoidHom.range_eq_map,range_subtype]
  have hh := normal_intersection_relIndex (S : Subgroup B) ⊤ N le_top (by rw [hgen])
  rw [top_subgroupOf,relIndex_top_right,relIndex_top_right,←hS₀] at hh
  exact hh.symm.trans (sylow_index_three S₀ hcN)

theorem flag_node_of_index_three {m : ℕ} (q : G →* LinearGroup (m+1))
    (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (S : Sylow 2 G) (B : Subgroup G) (hSB : (S : Subgroup G) ≤ B)
    (hi : (S : Subgroup G).relIndex B = 3)
    (b : Basis m) (hb : (S : Subgroup G).map q = cutStabilizer b Set.univ) :
    ∃ i : Fin m, B.map q = minimalParabolic b i ∧
      B = (minimalParabolic b i).comap q := by
  let P := S.mapSurjective hq
  have hker := hk.le_sylow_of_normal S
  have himage : (P : Subgroup _).relIndex (B.map q) = 3 := by
    change ((S : Subgroup G).map q).relIndex (B.map q) = 3
    rw [relIndex_map_map,sup_eq_left.mpr hker,sup_eq_left.mpr (hker.trans hSB)]
    exact hi
  have hcover : (P : Subgroup _) ⋖ B.map q := by
    have hmax : IsCoatom ((P : Subgroup (LinearGroup (m+1))).subgroupOf (B.map q)) :=
      isCoatom_of_index_three _ himage
    have hh : ((P : Subgroup (LinearGroup (m+1))).subgroupOf (B.map q)) ⋖ ⊤ := by
      exact ⟨lt_top_iff_ne_top.mpr hmax.1,fun _ hlt => (hmax.2 _ hlt).not_lt⟩
    have := (covBy_map_subtype_iff (B.map q) _ _).mpr hh
    have hPB : (P : Subgroup (LinearGroup (m+1))) ≤ B.map q := map_mono (f := q) hSB
    rw [map_subgroupOf_eq_of_le hPB,←MonoidHom.range_eq_map,range_subtype] at this
    exact this
  obtain ⟨i,hi⟩ := (BinaryLinear.SylowFlagOvergroups.fullFlag_covBy_iff P b hb _).mp hcover
  exact ⟨i,hi,(comap_map_eq_self (hker.trans hSB)).symm.trans (congrArg (comap q) hi)⟩

omit [Finite G] in
private theorem join_ne_top_of_intersection_le
    (K R P : Subgroup G) (hRK : R < K)
    (hn : P ≤ normalizer (R : Set G)) (hPK : P ⊓ K ≤ R) : R ⊔ P ≠ ⊤ := by
  intro he
  apply hRK.not_ge
  intro k hk
  have hm : k ∈ (R : Set G) * (P : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left R P hn,he]
    exact mem_top k
  obtain ⟨r,hr,p,hp,hrp⟩ := hm
  have hrp' : r * p = k := hrp
  have hpK : p ∈ K := by
    have hh : r * p ∈ K := hrp'.symm ▸ hk
    exact (K.mul_mem_cancel_left (hRK.le hr)).mp hh
  rw [←hrp']
  exact R.mul_mem hr (hPK ⟨hp,hpK⟩)

omit [Finite G] in
/-- If the original Sylow acts internally on the binary component, a
rank-one local base is contained in a proper invariant parabolic escaping M.
The actual quotient, full kernel and original Sylow intersection are used. -/
theorem inner_flag_escape
    (K A M : Subgroup G) (P : Sylow 2 G)
    (hnK : (P : Subgroup G) ≤ normalizer (K : Set G))
    {m : ℕ} (hm : 3 ≤ m) (q : K →* LinearGroup (m+1))
    (hq : Function.Surjective q)
    (α : (P : Subgroup G) →* MulAut (LinearGroup (m+1)))
    (heq : ∀ (p : (P : Subgroup G)) (k : K),
      q (K.normalizerMonoidHom (inclusion hnK p) k) = α p (q k))
    (b : Basis m) (i : Fin m) (cuts : Set (Fin m))
    (hcuts : cuts.Nonempty)
    (hSyl : ((P : Subgroup G).subgroupOf K).map q = cutStabilizer b Set.univ)
    (hbase : ((A ⊔ (P : Subgroup G)).subgroupOf K).map q = minimalParabolic b i)
    (hM : (M.subgroupOf K).map q = cutStabilizer b cuts)
    (hAK : A ≤ K)
    (hin : ∀ p : (P : Subgroup G), α p ∈ MulAut.innerSubgroup _) :
    ∃ X : Subgroup G, A ⊔ (P : Subgroup G) ≤ X ∧ X ≠ ⊤ ∧ ¬ X ≤ M := by
  classical
  obtain ⟨c,hc⟩ := hcuts
  have hj : ∃ j : Fin m, j ≠ i ∧ j ≠ c := by
    let z : Fin m := ⟨0,by omega⟩
    let o : Fin m := ⟨1,by omega⟩
    let t : Fin m := ⟨2,by omega⟩
    by_cases hz : z ≠ i ∧ z ≠ c
    · exact ⟨z,hz⟩
    by_cases ho : o ≠ i ∧ o ≠ c
    · exact ⟨o,ho⟩
    refine ⟨t,?_⟩
    simp only [ne_eq,Fin.ext_iff] at hz ho ⊢
    dsimp only [z,o,t] at hz ho ⊢
    omega
  obtain ⟨j,hji,hjc⟩ := hj
  let F := cutStabilizer b {j}
  let R := EquivariantLift.lift K q F
  have hFproper : F ≠ ⊤ := by
    intro ht
    have hh := (cutStabilizer_le_iff b ∅ {j}).mp (show cutStabilizer b ∅ ≤ F from ht ▸ le_top)
    exact hh (Set.mem_singleton j)
  have hRlt : R < K := EquivariantLift.lift_lt K q hq hFproper
  have hPF : (P : Subgroup G) ≤ normalizer (R : Set G) := by
    apply EquivariantLift.normalizes_lift K q hnK α heq
    intro p
    obtain ⟨g,hg⟩ := hin p
    have hnPK : (P : Subgroup G) ≤ normalizer (((P : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
      (le_inf (P : Subgroup G).le_normalizer hnK).trans inf_normalizer_le_normalizer_inf
    have hs := EquivariantLift.map_invariant K q hnK α heq hnPK p
    have hsub : ((P : Subgroup G) ⊓ K).subgroupOf K = (P : Subgroup G).subgroupOf K := by
      rw [inf_subgroupOf_right]
    rw [hsub,hSyl,←hg] at hs
    rw [←hg]
    exact inner_fixes_cutStabilizer b g hs {j}
  have hAR : A ≤ R := by
    apply EquivariantLift.le_lift K q hAK
    apply (map_mono (subgroupOf_mono K (show A ≤ A ⊔ (P : Subgroup G) from le_sup_left))).trans
    rw [hbase]
    exact (cutStabilizer_le_iff b _ _).mpr (by simpa using hji.symm)
  have hPK : (P : Subgroup G) ⊓ K ≤ R := by
    apply EquivariantLift.le_lift K q inf_le_right
    rw [inf_subgroupOf_right,hSyl]
    exact (cutStabilizer_le_iff b _ _).mpr (Set.subset_univ _)
  refine ⟨R ⊔ (P : Subgroup G),sup_le (hAR.trans le_sup_left) le_sup_right,
    join_ne_top_of_intersection_le K R (P : Subgroup G) hRlt hPF hPK,?_⟩
  intro hXM
  have hRM : R ≤ M := le_sup_left.trans hXM
  have himage : (R.subgroupOf K).map q = F := by
    let D := (F.comap q).map K.subtype
    have hD : D ≤ K := map_subtype_le _
    have heD : D.subgroupOf K = F.comap q :=
      comap_map_eq_self_of_injective K.subtype_injective _
    have hkD : q.ker ≤ D.subgroupOf K := by
      rw [heD]
      exact F.ker_le_comap q
    have hd := EquivariantLift.lift_map_subgroupOf K q D hD hkD
    have hdimage : (D.subgroupOf K).map q = F := by
      rw [heD,map_comap_eq_self_of_surjective hq]
    rw [hdimage] at hd
    exact (congrArg (fun X : Subgroup G => (X.subgroupOf K).map q) hd).trans hdimage
  have hh := map_mono (f := q) (subgroupOf_mono K hRM)
  rw [himage,hM] at hh
  have hcj := (cutStabilizer_le_iff b {j} cuts).mp hh hc
  exact hjc hcj.symm


/-- The original rank-one base forces an outer Sylow actor in degrees four
and five. Its actual flag action leaves only the middle node in degree four. -/
theorem outer_middle_of_minimal_escape
    (K A M : Subgroup G) [K.Normal] (P : Sylow 2 G)
    (hPA : (P : Subgroup G) ≤ normalizer (A : Set G))
    (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hAK : A ≤ K) (hPM : (P : Subgroup G) ≤ M)
    (hout : ¬ K ≤ M)
    (hminimal : ∀ X : Subgroup G, A ⊔ (P : Subgroup G) ≤ X → X ≠ ⊤ → X ≤ M)
    {m : ℕ} (hm : m = 3 ∨ m = 4) (e : (K ⧸ pCore 2 K) ≃* SL(m+1,ZMod 2)) :
    ∃ (hnK : (P : Subgroup G) ≤ normalizer (K : Set G)) (b : Basis m) (i : Fin m),
      ((P : Subgroup G).subgroupOf K).map (coreFlagMap K e) = cutStabilizer b Set.univ ∧
      ((A ⊔ (P : Subgroup G)).subgroupOf K).map (coreFlagMap K e) = minimalParabolic b i ∧
      (A ⊔ (P : Subgroup G)).subgroupOf K = (minimalParabolic b i).comap (coreFlagMap K e) ∧
      (∃ p : (P : Subgroup G), coreFlagAction K (P : Subgroup G) hnK e p ∉
        MulAut.innerSubgroup _) ∧ m = 3 ∧ i.val + 1 = 2 := by
  let q := coreFlagMap K e
  have hq := coreFlagMap_surjective K e
  have hk : IsPGroup 2 q.ker := by rw [coreFlagMap_ker]; exact pCore_isPGroup
  have hnK : (P : Subgroup G) ≤ normalizer (K : Set G) := by simp [normalizer_eq_top]
  let α := coreFlagAction K (P : Subgroup G) hnK e
  have heq := coreFlagAction_equivariant K (P : Subgroup G) hnK e
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_normal K
  let B := A ⊔ (P : Subgroup G)
  have hSB : (S : Subgroup K) ≤ B.subgroupOf K := by
    rw [hS]
    exact subgroupOf_mono K le_sup_right
  have hSM : (S : Subgroup K) ≤ M.subgroupOf K := by
    rw [hS]
    exact subgroupOf_mono K hPM
  let S' := S.mapSurjective hq
  obtain ⟨b,cuts,hb,hM⟩ := BinaryLinear.SylowFlagOvergroups.exists_flag_of_sylow_le
    S' ((M.subgroupOf K).map q) (map_mono hSM)
  have hindex : (S : Subgroup K).relIndex (B.subgroupOf K) = 3 := by
    rw [hS,normal_intersection_relIndex (P : Subgroup G) B K le_sup_right
      (sup_le (hAK.trans le_sup_left) le_sup_right)]
    exact local_base_index P A hPA hc
  obtain ⟨i,hi,hpre⟩ := flag_node_of_index_three q hq hk S (B.subgroupOf K) hSB hindex b hb
  have hcuts : cuts.Nonempty := by
    by_contra hc
    have ht : (M.subgroupOf K).map q = ⊤ := by
      rw [hM,Set.not_nonempty_iff_eq_empty.mp hc,cutStabilizer]
      simp
    have hker := hk.le_sylow_of_normal S
    have hh := congrArg (comap q) ht
    rw [comap_map_eq_self (hker.trans hSM),comap_top] at hh
    exact hout (subgroupOf_eq_top.mp hh)
  have houter : ∃ p : (P : Subgroup G), α p ∉ MulAut.innerSubgroup _ := by
    by_contra! hinner
    obtain ⟨X,hBX,hX,hXM⟩ := inner_flag_escape K A M P hnK (by omega) q hq α heq
      b i cuts hcuts (hS ▸ hb) hi hM hAK hinner
    exact hXM (hminimal X hBX hX)
  have hPN : (P : Subgroup G) ≤ normalizer (B : Set G) :=
    (show (P : Subgroup G) ≤ B from le_sup_right).trans B.le_normalizer
  obtain ⟨p,hp⟩ := houter
  have hinv := EquivariantLift.map_invariant K q hnK α heq hPN p
  rw [hi] at hinv
  obtain ⟨hmiddle,hinode⟩ := outer_preserves_minimalParabolic_middle
    (by omega) (by omega) b i (α p) hp hinv
  exact ⟨hnK,b,i,hS ▸ hb,hi,hpre,⟨p,hp⟩,hmiddle,hinode⟩

/-- The quintic binary component has no middle node and is impossible in the
original minimal-escape configuration. -/
theorem no_five_of_minimal_escape
    (K A M : Subgroup G) [K.Normal] (P : Sylow 2 G)
    (hPA : (P : Subgroup G) ≤ normalizer (A : Set G))
    (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hAK : A ≤ K) (hPM : (P : Subgroup G) ≤ M)
    (hout : ¬ K ≤ M)
    (hminimal : ∀ X : Subgroup G, A ⊔ (P : Subgroup G) ≤ X → X ≠ ⊤ → X ≤ M) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* SL(5,ZMod 2)) := by
  rintro ⟨e⟩
  obtain ⟨_,_,_,_,_,_,_,he,_⟩ := outer_middle_of_minimal_escape K A M P hPA hc
    hAK hPM hout hminimal (Or.inr rfl) e
  omega

/-- The original local base is a marked middle-node parabolic in degree four;
the Sylow contains an actual outer actor. Degree five is excluded. -/
@[expose] def Conclusion (K A R : Subgroup G) : Prop :=
  (¬ Nonempty ((K ⧸ pCore 2 K) ≃* SL(5,ZMod 2))) ∧
  ∀ e : (K ⧸ pCore 2 K) ≃* SL(4,ZMod 2),
    ∃ (hn : R ≤ normalizer (K : Set G)) (b : Basis 3) (i : Fin 3),
      (R.subgroupOf K).map (coreFlagMap K e) = cutStabilizer b Set.univ ∧
      ((A ⊔ R).subgroupOf K).map (coreFlagMap K e) = minimalParabolic b i ∧
      (A ⊔ R).subgroupOf K = (minimalParabolic b i).comap (coreFlagMap K e) ∧
      (∃ r : R, coreFlagAction K R hn e r ∉ MulAut.innerSubgroup _) ∧ i.val + 1 = 2

theorem conclusion_of_minimal_escape
    (K A M : Subgroup G) [K.Normal] (P : Sylow 2 G)
    (hPA : (P : Subgroup G) ≤ normalizer (A : Set G))
    (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hAK : A ≤ K) (hPM : (P : Subgroup G) ≤ M)
    (hout : ¬ K ≤ M)
    (hminimal : ∀ X : Subgroup G, A ⊔ (P : Subgroup G) ≤ X → X ≠ ⊤ → X ≤ M) :
    Conclusion K A (P : Subgroup G) := by
  refine ⟨no_five_of_minimal_escape K A M P hPA hc hAK hPM hout hminimal,?_⟩
  intro e
  obtain ⟨hn,b,i,hS,hB,hpre,hout,_,hi⟩ := outer_middle_of_minimal_escape
    K A M P hPA hc hAK hPM hout hminimal (Or.inl rfl) e
  exact ⟨hn,b,i,hS,hB,hpre,hout,hi⟩


omit [Finite G] in
/-- The original central plane makes every intermediate local-base overgroup
a member of H(B); minimal escape therefore controls its proper subgroups. -/
theorem minimal_escape_internal (H B M U : Subgroup G)
    (hH : H ∈ Chapter3.HStar B M)
    (hU : U ≠ ⊥) (hp : IsPGroup 2 U) (hUB : U ≤ B)
    (hHC : H ≤ centralizer (U : Set G))
    (X : Subgroup H) (hBX : B.subgroupOf H ≤ X) (hX : X ≠ ⊤) :
    X ≤ M.subgroupOf H := by
  have hBH : B ≤ H := hH.1.1.2
  have hBY : B ≤ X.map H.subtype := by
    rw [←map_subgroupOf_eq_of_le hBH]
    exact map_mono hBX
  have hUY : U ≤ X.map H.subtype := hUB.trans hBY
  have hc : U ≤ (X.map H.subtype).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hp hUY
      (((map_subtype_le X).trans hHC).trans (Subgroup.centralizer_le_normalizer _))
  by_contra hXM
  have hYM : ¬ X.map H.subtype ≤ M := by
    intro hy
    exact hXM (fun x hx => hy (mem_map_of_mem H.subtype hx))
  have hHY := hH.2 ⟨⟨(fun he => hU (le_bot_iff.mp (he ▸ hc))),hBY⟩,hYM⟩
    (map_subtype_le X)
  apply hX
  apply map_injective H.subtype_injective
  rw [←MonoidHom.range_eq_map,range_subtype]
  exact le_antisymm (map_subtype_le X) hHY

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryMarkedParabolic
