module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Basic
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.SylowCore
public import Theory.GroupTheory.SylowNormalizerFrattini

/-!
# The Frattini factorization in the radical normalizer construction

For X = Ξ_p(L) and R = O₂(XT), A.4.2(4),(5) identify R as a Sylow
two-subgroup of C_LT(X/O₂(X)). Frattini's argument then supplies the
factorization of LT. Taking solvable residuals proves that Y = N_L(R)^∞
covers L modulo this section centralizer, hence has the same actual action
as L on X/O₂(X) and its Frattini quotient.

All normality here is relative to LT or N_LT(R). This module does not
identify the solvable residual with the two-residual. The component and
nonquasisimplicity assertions, and comparison with the other odd-prime
sections, require further structural arguments beyond this factorization.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Proposition 1.3.8, printed pp.512–513.
-/

open Subgroup
open CFSG.Quasithin.ChapterA.Section04
open CFSG.Quasithin.Chapter1
open scoped Pointwise commutatorElement

@[expose] public section
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers

/-- A.4.2(4),(5) put R in a Sylow subgroup of the section centralizer.
This does not use the extra normalizer-containment premise of A.4.2(7). -/
theorem sylow_radicalCore {G : Type*} [Group G] [Finite G] (p : ℕ) (L T : Subgroup G)
    (hSyl : IsSylowIn 2 T (L ⊔ T)) (hT : T ≤ normalizer (L : Set G)) :
    IsSylowIn 2 (radicalCore p L T) (twoSectionCentralizer (XiP p L) (L ⊔ T)) := by
  have hn : L ⊔ T ≤ normalizer (XiP p L : Set G) :=
    (sup_le L.le_normalizer hT).trans (normalizer_le_normalizer_XiP p L)
  have he : (L ⊔ T) ⊓ normalizer (XiP p L : Set G) = L ⊔ T := inf_of_le_left hn
  have hs : IsSylowIn 2 T ((L ⊔ T) ⊓ normalizer (XiP p L : Set G)) := he.symm ▸ hSyl
  obtain ⟨S, hS⟩ := hs
  have hnorm : ((XiP p L).subgroupOf (L ⊔ T)).Normal :=
    normal_subgroupOf_of_le_normalizer hn
  have hmax := sylow_normalizer_core_isMaximal (XiP p L) (L ⊔ T)
    ((XiP_le p L).trans le_sup_left) hnorm.isSubnormal (XiP_isPPerfect p L) S
  rw [hS] at hmax
  exact (maximal_signalizer_iff_sylow (XiP p L) (L ⊔ T) _
    ((XiP_le p L).trans le_sup_left) hnorm.isSubnormal (XiP_isPPerfect p L)).mp hmax

private theorem frattini_factorization_aux {G : Type*} [Group G] [Finite G]
    (C W R : Subgroup G) (hCW : C ≤ W) (hWC : W ≤ normalizer (C : Set G))
    (hs : IsSylowIn 2 R C) : C ⊔ (W ⊓ normalizer (R : Set G)) = W := by
  obtain ⟨S, hS⟩ := hs
  let C' := C.subgroupOf W
  let : C'.Normal := normal_subgroupOf_of_le_normalizer hWC
  let e : C ≃* C' := (subgroupOfEquivOfLe hCW).symm
  let S' : Sylow 2 C' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hm : ((S' : Subgroup C').map C'.subtype).map W.subtype = R := by
    change (((S : Subgroup C).map e.toMonoidHom).map C'.subtype).map W.subtype = R
    rw [map_map, map_map]
    exact hS
  have hfr := congrArg (fun K : Subgroup W => K.map W.subtype) S'.normalizer_sup_eq_top
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, W.range_subtype] at hfr
  change _ ⊔ (C.subgroupOf W).map W.subtype = W at hfr
  rw [map_subgroupOf_eq_of_le hCW] at hfr
  apply le_antisymm (sup_le hCW inf_le_left)
  apply hfr.symm.le.trans
  apply sup_le _ le_sup_left
  apply le_trans _ le_sup_right
  apply le_inf (map_subtype_le _)
  have hh := ((S' : Subgroup C').map C'.subtype).le_normalizer_map W.subtype
  rwa [hm] at hh

/-- The Frattini factorization (**) on printed p.512. The first factor is
normal in LT, so the displayed join is also its setwise product with N_LT(R). -/
theorem radical_frattini {G : Type*} [Group G] [Finite G] (p : ℕ) (L T : Subgroup G)
    (hSyl : IsSylowIn 2 T (L ⊔ T)) (hT : T ≤ normalizer (L : Set G)) :
    twoSectionCentralizer (XiP p L) (L ⊔ T) ⊔
      ((L ⊔ T) ⊓ normalizer (radicalCore p L T : Set G)) = L ⊔ T :=
  frattini_factorization_aux _ _ _ (twoSectionCentralizer_le _ _)
    (twoSectionCentralizer_normalized _ _
      ((sup_le L.le_normalizer hT).trans (normalizer_le_normalizer_XiP p L)))
    (sylow_radicalCore p L T hSyl hT)

private theorem quotient_surjective_of_supplement
    {A : Type*} [Group A] (C N : Subgroup A) [C.Normal]
    (hgen : C ⊔ N = ⊤) :
    Function.Surjective ((QuotientGroup.mk' C).comp N.subtype) := by
  intro z
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective C z
  have ha : a ∈ C ⊔ N := by rw [hgen]; trivial
  obtain ⟨c, hc, n, hn, rfl⟩ := mem_sup_of_normal_left.mp ha
  refine ⟨⟨n, hn⟩, ?_⟩
  change QuotientGroup.mk' C n = QuotientGroup.mk' C (c * n)
  have hqc : QuotientGroup.mk' C c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
  rw [map_mul, hqc, one_mul]

private theorem residual_le_of_solvable_supplement
    {A : Type*} [Group A] [Finite A] (D U : Subgroup A) [D.Normal]
    [Group.IsSolvable U] (hgen : D ⊔ U = ⊤) : solvableResidual A ≤ D := by
  let : Group.IsSolvable (A ⧸ D) := Group.isSolvable_of_surjective
    (quotient_surjective_of_supplement D U hgen)
  exact solvableResidual_le_of_solvable_quotient D

private theorem residual_cover
    {A : Type*} [Group A] [Finite A] (C N : Subgroup A) [C.Normal]
    (hgen : C ⊔ N = ⊤) :
    solvableResidual A ≤ C ⊔ (solvableResidual N).map N.subtype := by
  let q := QuotientGroup.mk' C
  have he : (solvableResidual A).map q = ((solvableResidual N).map N.subtype).map q := by
    rw [map_map, map_solvableResidual_eq q (QuotientGroup.mk'_surjective C),
      map_solvableResidual_eq (q.comp N.subtype) (quotient_surjective_of_supplement C N hgen)]
  have hc := congrArg (Subgroup.comap q) he
  rw [comap_map_eq, comap_map_eq, QuotientGroup.ker_mk'] at hc
  exact le_sup_left.trans (hc.le.trans_eq (sup_comm _ _))

private theorem map_embedded_residual
    {A B : Type*} [Group A] [Group B] [Finite A]
    (D : Subgroup A) (f : A →* B) (hf : Function.Injective f) :
    ((solvableResidual D).map D.subtype).map f =
      (solvableResidual (D.map f)).map (D.map f).subtype := by
  let e := D.equivMapOfInjective f hf
  have he := congrArg (map (D.map f).subtype)
    (map_solvableResidual_eq e.toMonoidHom e.surjective)
  have hc : (D.map f).subtype.comp e.toMonoidHom = f.comp D.subtype := by
    ext d
    simp [e]
  simpa only [map_map, hc] using he

private theorem residual_of_subgroup_containing_residual
    {A : Type*} [Group A] [Finite A] (N D : Subgroup A)
    (h : (solvableResidual N).map N.subtype ≤ D) :
    (solvableResidual N).map N.subtype = (solvableResidual (N ⊓ D : Subgroup A)).map
      (N ⊓ D).subtype := by
  apply le_antisymm _ (map_solvableResidual_mono inf_le_left)
  let : Group.IsPerfect ((solvableResidual N).map N.subtype) := Group.IsPerfect.map _
  exact le_map_solvableResidual_of_isPerfect _ _ (le_inf (map_subtype_le _) h)

private theorem residual_join_le
    {G : Type*} [Group G] [Finite G] (L T : Subgroup G)
    (hT : T ≤ normalizer (L : Set G)) (hsolv : Group.IsSolvable T) :
    (solvableResidual (L ⊔ T : Subgroup G)).map (L ⊔ T).subtype ≤ L := by
  let H := L ⊔ T
  let L' := L.subgroupOf H
  let T' := T.subgroupOf H
  let : L'.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hT)
  let : Group.IsSolvable T' := by
    let := hsolv
    exact Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show T ≤ H from le_sup_right)).toMonoidHom)
      (subgroupOfEquivOfLe (show T ≤ H from le_sup_right)).injective
  have he := residual_le_of_solvable_supplement L' T'
    (codisjoint_subgroupOf_sup L T).eq_top
  simpa only [L', map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left)] using
    map_mono (f := H.subtype) he

/-- For any D, the solvable residual of N_LT(D) is N_L(D)^∞.
The quotient contributed by the Sylow two-subgroup is solvable. -/
theorem localNormalizer_residual_eq
    {G : Type*} [Group G] [Finite G] (L T D : Subgroup G)
    (hSyl : IsSylowIn 2 T (L ⊔ T)) (hT : T ≤ normalizer (L : Set G)) :
    (solvableResidual ((L ⊔ T) ⊓ normalizer (D : Set G) : Subgroup G)).map
      ((L ⊔ T) ⊓ normalizer (D : Set G)).subtype =
        normalizerResidual L D := by
  have hpT : IsPGroup 2 T := by
    obtain ⟨S, hS⟩ := hSyl
    rw [← hS]
    exact S.isPGroup'.map _
  let : Group.IsNilpotent T := hpT.isNilpotent
  have he := residual_of_subgroup_containing_residual
    ((L ⊔ T) ⊓ normalizer (D : Set G)) L
    ((map_solvableResidual_mono inf_le_left).trans (residual_join_le L T hT inferInstance))
  have hNL : ((L ⊔ T) ⊓ normalizer (D : Set G)) ⊓ L =
      L ⊓ normalizer (D : Set G) := by
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
    · exact le_inf (le_inf (inf_le_left.trans le_sup_left) inf_le_right) inf_le_left
  change _ = (solvableResidual (L ⊓ normalizer (D : Set G) : Subgroup G)).map _
  rw [hNL] at he
  exact he

/-- The solvable residual of N_LT(R) is exactly the constructed Y. -/
theorem localNormalizer_residual
    {G : Type*} [Group G] [Finite G] (p : ℕ) (L T : Subgroup G)
    (hSyl : IsSylowIn 2 T (L ⊔ T)) (hT : T ≤ normalizer (L : Set G)) :
    (solvableResidual ((L ⊔ T) ⊓ normalizer (radicalCore p L T : Set G) : Subgroup G)).map
      ((L ⊔ T) ⊓ normalizer (radicalCore p L T : Set G)).subtype =
        normalizerResidual L (radicalCore p L T) :=
  localNormalizer_residual_eq L T (radicalCore p L T) hSyl hT

/-- Taking solvable residuals in the Frattini factorization shows that Y
covers the action of L on X/O₂(X). Further action information is needed to
infer that X itself lies in Y. -/
theorem L_covered_by_Y
    {G : Type*} [Group G] [Finite G] (p : ℕ) (L T : Subgroup G)
    (hL : L ∈ CFSG.Quasithin.Chapter1.L G T) (hT : T ≤ normalizer (L : Set G)) :
    L ≤ twoSectionCentralizer (XiP p L) (L ⊔ T) ⊔ normalizerResidual L (radicalCore p L T) := by
  let H := L ⊔ T
  let C := twoSectionCentralizer (XiP p L) H
  let N := H ⊓ normalizer (radicalCore p L T : Set G)
  have hC : C ≤ H := twoSectionCentralizer_le _ _
  have hN : N ≤ H := inf_le_left
  have hCN : C ⊔ N = H := radical_frattini p L T hL.2.1 hT
  let : (C.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (twoSectionCentralizer_normalized _ _
      ((sup_le L.le_normalizer hT).trans (normalizer_le_normalizer_XiP p L)))
  have hgen : C.subgroupOf H ⊔ N.subgroupOf H = ⊤ := by
    apply (map_injective H.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hC, map_subgroupOf_eq_of_le hN,
      ← MonoidHom.range_eq_map, H.range_subtype, hCN]
  have hh := map_mono (f := H.subtype) (residual_cover (C.subgroupOf H) (N.subgroupOf H) hgen)
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hC,
    map_embedded_residual _ _ H.subtype_injective, map_subgroupOf_eq_of_le hN,
    localNormalizer_residual p L T hL.2.1 hT] at hh
  let := mem_L_isPerfect hL
  exact (le_map_solvableResidual_of_isPerfect L H le_sup_left).trans hh

variable {G : Type*} [Group G] [Finite G]

/-- The literal set-product form of (**) on printed p.512. -/
theorem radical_frattini_mul (p : ℕ) (L T : Subgroup G)
    (hSyl : IsSylowIn 2 T (L ⊔ T)) (hT : T ≤ normalizer (L : Set G)) :
    ((L ⊔ T : Subgroup G) : Set G) = (twoSectionCentralizer (XiP p L) (L ⊔ T) : Set G) *
      ((((L ⊔ T) ⊓ normalizer (radicalCore p L T : Set G)) : Subgroup G) : Set G) := by
  rw [← coe_mul_of_right_le_normalizer_left _ _
    (inf_le_left.trans (twoSectionCentralizer_normalized _ _
      ((sup_le L.le_normalizer hT).trans (normalizer_le_normalizer_XiP p L)))),
    radical_frattini p L T hSyl hT]

/-- The actual conjugation action of LT on Ξ_p(L)/O₂(Ξ_p(L)). -/
def localXiQuotientAction (p : ℕ) (L T : Subgroup G)
    (hT : T ≤ normalizer (L : Set G)) :
    (L ⊔ T : Subgroup G) →* MulAut (XiQuotient (XiP p L)) :=
  let _ := conjMulDistribMulActionOfLeNormalizer (L ⊔ T) (XiP p L)
    ((sup_le L.le_normalizer hT).trans (normalizer_le_normalizer_XiP p L))
  (quotientAut (pCore 2 (XiP p L))).comp
    (MulDistribMulAction.toMulAut (L ⊔ T : Subgroup G) (XiP p L))

omit [Finite G] in
/-- The section centralizer acts trivially on the two-core quotient. -/
theorem sectionCentralizer_le_action_ker (p : ℕ) (L T : Subgroup G)
    (hT : T ≤ normalizer (L : Set G)) :
    (twoSectionCentralizer (XiP p L) (L ⊔ T)).subgroupOf (L ⊔ T) ≤
      (localXiQuotientAction p L T hT).ker := by
  let _ := conjMulDistribMulActionOfLeNormalizer (L ⊔ T) (XiP p L)
    ((sup_le L.le_normalizer hT).trans (normalizer_le_normalizer_XiP p L))
  intro c hc
  apply MulEquiv.ext
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (XiP p L)) z
  simp only [localXiQuotientAction, MonoidHom.comp_apply, quotientAut_apply_mk]
  change QuotientGroup.mk' (pCore 2 (XiP p L)) (c • x) = QuotientGroup.mk' (pCore 2 (XiP p L)) x
  have hm : ⁅(c : G), (x : G)⁆ ∈ (XiP p L).pCoreIn 2 := hc.2.2 x x.property
  have hk : (c • x) * x⁻¹ ∈ pCore 2 (XiP p L) := by
    obtain ⟨a, ha, he⟩ := mem_map.mp hm
    have hh : a = (c • x) * x⁻¹ := Subtype.ext he
    exact hh ▸ ha
  have hq := (QuotientGroup.eq_one_iff _).mpr hk
  change QuotientGroup.mk' (pCore 2 (XiP p L)) ((c • x) * x⁻¹) = 1 at hq
  rw [map_mul, map_inv] at hq
  exact mul_inv_eq_one.mp hq

/-- Y and L have the same image in any action killed by the section
centralizer. For a different odd prime, that kernel condition still needs proof. -/
theorem Y_covers_action {A : Type*} [Group A]
    (p : ℕ) (L T : Subgroup G)
    (hL : L ∈ CFSG.Quasithin.Chapter1.L G T) (hT : T ≤ normalizer (L : Set G))
    (f : (L ⊔ T : Subgroup G) →* A)
    (hker : (twoSectionCentralizer (XiP p L) (L ⊔ T)).subgroupOf (L ⊔ T) ≤ f.ker) :
    (L.subgroupOf (L ⊔ T)).map f =
      ((normalizerResidual L (radicalCore p L T)).subgroupOf (L ⊔ T)).map f := by
  let H := L ⊔ T
  let C := twoSectionCentralizer (XiP p L) H
  let Y := normalizerResidual L (radicalCore p L T)
  have hYH : Y ≤ H := (normalizerResidual_le _ _).trans le_sup_left
  have hC : C ≤ H := twoSectionCentralizer_le _ _
  have hcover : L.subgroupOf H ≤ C.subgroupOf H ⊔ Y.subgroupOf H := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le hC, map_subgroupOf_eq_of_le hYH]
    exact L_covered_by_Y p L T hL hT
  apply le_antisymm
  · have hm := map_mono (f := f) hcover
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr hker, bot_sup_eq] at hm
    exact hm
  · exact map_mono (comap_mono (normalizerResidual_le _ _))

/-- Y has the same action as L on X/O₂(X); the kernel condition is proved. -/
theorem Y_covers_quotientAction (p : ℕ) (L T : Subgroup G)
    (hL : L ∈ CFSG.Quasithin.Chapter1.L G T) (hT : T ≤ normalizer (L : Set G)) :
    (L.subgroupOf (L ⊔ T)).map (localXiQuotientAction p L T hT) =
      ((normalizerResidual L (radicalCore p L T)).subgroupOf (L ⊔ T)).map
        (localXiQuotientAction p L T hT) :=
  Y_covers_action p L T hL hT _ (sectionCentralizer_le_action_ker p L T hT)

/-- The same action comparison on X/O₂,Φ(X). -/
theorem Y_covers_frattiniAction (p : ℕ) (L T : Subgroup G)
    (hL : L ∈ CFSG.Quasithin.Chapter1.L G T) (hT : T ≤ normalizer (L : Set G)) :
    (L.subgroupOf (L ⊔ T)).map
      (xiFrattiniAction (L ⊔ T) (XiP p L)
        ((sup_le L.le_normalizer hT).trans (normalizer_le_normalizer_XiP p L))) =
      ((normalizerResidual L (radicalCore p L T)).subgroupOf (L ⊔ T)).map
        (xiFrattiniAction (L ⊔ T) (XiP p L)
          ((sup_le L.le_normalizer hT).trans (normalizer_le_normalizer_XiP p L))) := by
  have hh := congrArg (Subgroup.map (quotientAut (frattini (XiQuotient (XiP p L)))))
    (Y_covers_quotientAction p L T hL hT)
  simpa only [map_map, localXiQuotientAction, xiFrattiniAction] using hh

/-- Irreducibility of L on the radical Frattini section passes to Y.
The earlier L-action hypothesis is explicit; Y's action is deduced. -/
theorem Y_irreducible_of_L_irreducible (p : ℕ) (L T : Subgroup G)
    (hL : L ∈ CFSG.Quasithin.Chapter1.L G T) (hT : T ≤ normalizer (L : Set G))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
      (∀ l : L, ∀ a ∈ A,
        xiFrattiniAction L (XiP p L)
          (L.le_normalizer.trans (normalizer_le_normalizer_XiP p L)) l a ∈ A) →
        A = ⊥ ∨ A = ⊤) :
    ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
      (∀ y : normalizerResidual L (radicalCore p L T), ∀ a ∈ A,
        xiFrattiniAction (normalizerResidual L (radicalCore p L T)) (XiP p L)
          ((normalizerResidual_le _ _).trans
            (L.le_normalizer.trans (normalizer_le_normalizer_XiP p L))) y a ∈ A) →
        A = ⊥ ∨ A = ⊤ := by
  intro A hA
  apply hirr A
  intro l a ha
  let f := xiFrattiniAction (L ⊔ T) (XiP p L)
    ((sup_le L.le_normalizer hT).trans (normalizer_le_normalizer_XiP p L))
  have hl : f ⟨l, (show L ≤ L ⊔ T from le_sup_left) l.property⟩ ∈
      (L.subgroupOf (L ⊔ T)).map f := mem_map.mpr ⟨_, l.property, rfl⟩
  rw [Y_covers_frattiniAction p L T hL hT] at hl
  obtain ⟨y, hy, he⟩ := mem_map.mp hl
  have hya := hA ⟨y, hy⟩ a ha
  change f y a ∈ A at hya
  rw [he] at hya
  exact hya

/-- Restricting the residual cover to L removes the outer two-group action. -/
theorem L_covered_by_Y_inside (p : ℕ) (L T : Subgroup G)
    (hL : L ∈ CFSG.Quasithin.Chapter1.L G T) (hT : T ≤ normalizer (L : Set G)) :
    L ≤ (L ⊓ twoSectionCentralizer (XiP p L) (L ⊔ T)) ⊔
      normalizerResidual L (radicalCore p L T) := by
  let C := twoSectionCentralizer (XiP p L) (L ⊔ T)
  let Y := normalizerResidual L (radicalCore p L T)
  have hYC : Y ≤ normalizer (C : Set G) :=
    ((normalizerResidual_le _ _).trans le_sup_left).trans
      (twoSectionCentralizer_normalized _ _
        ((sup_le L.le_normalizer hT).trans (normalizer_le_normalizer_XiP p L)))
  intro l hl
  have hm : l ∈ ((C ⊔ Y : Subgroup G) : Set G) := (L_covered_by_Y p L T hL hT) hl
  rw [coe_mul_of_right_le_normalizer_left C Y hYC] at hm
  obtain ⟨c, hc, y, hy, he⟩ := hm
  have hcL : c ∈ L := by
    have hh := L.mul_mem hl (L.inv_mem (normalizerResidual_le _ _ hy))
    simpa only [← he, mul_inv_cancel_right] using hh
  rw [← he]
  exact ((L ⊓ C) ⊔ Y).mul_mem (mem_sup_left ⟨hcL, hc⟩) (mem_sup_right hy)

/-- Equality of action images only needs the centralizer inside L in the kernel.
This is the version suitable for actions on the other odd Fitting factors. -/
theorem Y_covers_L_action {A : Type*} [Group A]
    (p : ℕ) (L T : Subgroup G)
    (hL : L ∈ CFSG.Quasithin.Chapter1.L G T) (hT : T ≤ normalizer (L : Set G))
    (f : L →* A)
    (hker : (twoSectionCentralizer (XiP p L) (L ⊔ T)).subgroupOf L ≤ f.ker) :
    f.range = ((normalizerResidual L (radicalCore p L T)).subgroupOf L).map f := by
  let C := L ⊓ twoSectionCentralizer (XiP p L) (L ⊔ T)
  let Y := normalizerResidual L (radicalCore p L T)
  have hcover : C.subgroupOf L ⊔ Y.subgroupOf L = ⊤ := by
    apply map_injective L.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le inf_le_left,
      map_subgroupOf_eq_of_le (normalizerResidual_le _ _),
      ← MonoidHom.range_eq_map, range_subtype]
    exact le_antisymm (sup_le inf_le_left (normalizerResidual_le _ _))
      (L_covered_by_Y_inside p L T hL hT)
  have hc : C.subgroupOf L ≤ f.ker := (comap_mono inf_le_right).trans hker
  have hm := congrArg (map f) hcover
  rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr hc, bot_sup_eq,
    ← MonoidHom.range_eq_map] at hm
  exact hm.symm

end CFSG.Quasithin.Chapter1.RadicalNormalizers
