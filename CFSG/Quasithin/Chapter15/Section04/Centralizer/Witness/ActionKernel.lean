module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.SourceCubic.NineLift
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.NormalClosureCubic.OmegaEndgame
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupAction.FixedGeneratorCentralizer

/-!
# The kernel on the actual natural-nine residual in 15.4.10

Let P be the actual natural nine-group in M/O₂(M), and let Y be its
residual lift. For H=YXT and W=⟨Z^H⟩, the two-core of M centralizes W.
The image of C_Y(W) is invariant under the original Sylow image on P.
Irreducibility and [Z,Y]≠1 therefore give C_Y(W)=O₂(Y).

The resulting image P⁺ in H/C_H(W) retains the original quotient marking.
Since XT fixes Z pointwise, its image is a disjoint supplement to P⁺ and
C_(H/C_H(W))(P⁺)=P⁺, by the faithful action on the generators of W.

The supercritical choice of P, its actual irreducibility, and noncentrality
are preceding source outputs of A.1 and 15.4.2, retained with the original
15.4.10 owner. No action kernel or desired centralizer identity is assumed.
Source: Aschbacher--Smith, printed p. 1159.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.ActionKernel
open FamilySource CentralizerNormalClosureCubic CentralizerNormalClosureCubic.OmegaEndgame
open LocalSetup.TwoFactors.SourceFactors.Permutation
variable {G : Type*} [Group G]

private theorem normalizer_le_normalizer_centralizer (A : Subgroup G) :
    normalizer (A : Set G) ≤ normalizer (centralizer (A : Set G) : Set G) :=
  (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (A : Set G))).mp inferInstance

private theorem closure_le_of_normalizes (H A B : Subgroup G)
    (hAB : A ≤ B) (hHB : H ≤ normalizer (B : Set G)) : sourceClosure H A ≤ B := by
  let : (B.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHB
  have hh : normalClosure (A.subgroupOf H : Set H) ≤ B.subgroupOf H :=
    normalClosure_le_normal (fun _ ha => hAB ha)
  rintro x ⟨a, ha, rfl⟩
  exact hh ha

private theorem le_sourceClosure {H A : Subgroup G} (hAH : A ≤ H) : A ≤ sourceClosure H A := by
  intro a ha
  exact ⟨⟨a, hAH ha⟩, le_normalClosure ha, rfl⟩

private theorem image_normalized (M U V : Subgroup G)
    (hn : U ≤ normalizer (V : Set G)) :
    image M U ≤ normalizer (image M V : Set (CoreQuotient M)) := by
  have hh : U.subgroupOf M ≤ normalizer (V.subgroupOf M : Set M) := by
    intro u hu
    apply mem_normalizer_iff.mpr
    intro v
    exact mem_normalizer_iff.mp (hn hu) (v : G)
  exact (map_mono hh).trans ((V.subgroupOf M).le_normalizer_map (quotientMap M))

private theorem core_le_sylow (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) : M.pCoreIn 2 ≤ (T : Subgroup G) := by
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM] using
    pCoreIn_le_sylow M (T.subtype hTM)

/-- The original two-core centralizes the actual H-normal closure of Z,
because it is contained in T and its centralizer is M-invariant. -/
theorem twoCore_centralizes_closure (T : Sylow 2 G) (M H Z : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hHM : H ≤ M)
    (hTC : (T : Subgroup G) ≤ centralizer (Z : Set G)) :
    M.pCoreIn 2 ≤ centralizer (sourceClosure H Z : Set G) := by
  have hZQ : Z ≤ centralizer (M.pCoreIn 2 : Set G) :=
    le_centralizer_iff.mp ((core_le_sylow T M hTM).trans hTC)
  have hMQ : M ≤ normalizer (M.pCoreIn 2 : Set G) :=
    M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  exact le_centralizer_iff.mp (closure_le_of_normalizes H Z _ hZQ
    (hHM.trans (hMQ.trans (normalizer_le_normalizer_centralizer _))))

variable [Finite G]

omit [Finite G] in
/-- Irreducibility on the literal quotient image determines C_Y(W). All
normalizers and kernels are transported through the original map M→M/O₂(M). -/
theorem centralizer_closure_eq_core (T : Sylow 2 G) (M H Y Z : Subgroup G)
    (P : Subgroup (CoreQuotient M))
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    (hHM : H ≤ M) (hYH : Y ≤ H) (hZT : Z ≤ (T : Subgroup G))
    (hTC : (T : Subgroup G) ≤ centralizer (Z : Set G))
    (hMY : M ≤ normalizer (Y : Set G)) (hpY : IsPPerfect 2 Y)
    (hYP : image M Y = P)
    (hirr : ∀ B : Subgroup (CoreQuotient M), B ≤ P →
      image M (T : Subgroup G) ≤ normalizer (B : Set (CoreQuotient M)) → B = ⊥ ∨ B = P)
    (hnon : ¬ Y ≤ centralizer (Z : Set G)) :
    Y ⊓ centralizer (sourceClosure H Z : Set G) = Y.pCoreIn 2 := by
  let W := sourceClosure H Z
  let K := Y ⊓ centralizer (W : Set G)
  have hYM : Y ≤ M := hYH.trans hHM
  have hKM : K ≤ M := inf_le_left.trans hYM
  have hHW : H ≤ normalizer (W : Set G) := sourceClosure_normalized H Z
  have hHK : H ≤ normalizer (K : Set G) :=
    (le_inf (hHM.trans hMY) (hHW.trans (normalizer_le_normalizer_centralizer W))).trans
      inf_normalizer_le_normalizer_inf
  have hQW : Y.pCoreIn 2 ≤ centralizer (W : Set G) :=
    (pCoreIn_mono_of_normalizes (p := 2) (Y := Y) (L := M) hYM hMY).trans
      (twoCore_centralizes_closure T M H Z hTM hHM hTC)
  apply le_antisymm ?_ (le_inf (pCoreIn_le 2 Y) hQW)
  change K ≤ Y.pCoreIn 2
  have hKP : image M K ≤ P := hYP ▸ map_mono (comap_mono (show K ≤ Y from inf_le_left))
  rcases hirr (image M K) hKP (image_normalized M T K (hTH.trans hHK)) with hbot | htop
  · have hpre : K.subgroupOf M ≤ (quotientMap M).ker := (map_eq_bot_iff (K.subgroupOf M)).mp hbot
    rw [quotientMap, QuotientGroup.ker_mk'] at hpre
    have hKQ : K ≤ M.pCoreIn 2 := by
      intro k hk
      exact ⟨⟨k, hKM hk⟩, hpre hk, rfl⟩
    exact (le_inf inf_le_left hKQ).trans (inf_pCoreIn_le_of_le 2 hYM)
  · have hk : IsPGroup 2 (quotientMap M).ker := by
      rw [quotientMap, QuotientGroup.ker_mk']
      exact pCore_isPGroup
    have hp : IsPPerfect 2 (Y.subgroupOf M) := hpY.of_surjective
      (subgroupOfEquivOfLe hYM).symm.toMonoidHom (subgroupOfEquivOfLe hYM).symm.surjective
    have hn : Y.subgroupOf M ≤ normalizer (K.subgroupOf M : Set M) := by
      intro y hy
      apply mem_normalizer_iff.mpr
      intro k
      exact mem_normalizer_iff.mp ((hYH.trans hHK) hy) (k : G)
    have heq : K.subgroupOf M = Y.subgroupOf M := eq_of_perfect_of_map_eq
      (quotientMap M) hk hp (comap_mono (show K ≤ Y from inf_le_left)) hn (htop.trans hYP.symm)
    have he := congrArg (Subgroup.map M.subtype) heq
    rw [map_subgroupOf_eq_of_le hKM, map_subgroupOf_eq_of_le hYM] at he
    exfalso
    apply hnon
    exact he.symm.le.trans (inf_le_right.trans (centralizer_le (le_sourceClosure (hZT.trans hTH))))

private theorem nine_perfect {Q : Type*} [Group Q] (P : Subgroup Q)
    (hP : Nat.card P = 9) : IsPPerfect 2 P := by
  apply (pResidual_eq_top_iff 2 P).mp
  apply top_unique
  intro p _
  apply mem_pResidual_of_orderOf_coprime
  exact (by decide : Nat.Coprime 2 9).of_dvd_right (hP ▸ orderOf_dvd_natCard p)

/-- Actual application in 15.4.10: Y is the residual lift of the chosen
natural nine-group, H=YXT and W=⟨Z^H⟩. The source choice and its irreducibility
remain earlier A.1 outputs; the centralizer identity is proved here. -/
theorem residual_nine_centralizer_eq_core (T : Sylow 2 G) (M X Z : Subgroup G)
    (P : Subgroup (CoreQuotient M)) [P.Normal] (hP : Nat.card P = 9)
    (hTM : (T : Subgroup G) ≤ M) (hXM : X ≤ M)
    (hZT : Z ≤ (T : Subgroup G)) (hTC : (T : Subgroup G) ≤ centralizer (Z : Set G))
    (hirr : ∀ B : Subgroup (CoreQuotient M), B ≤ P →
      image M (T : Subgroup G) ≤ normalizer (B : Set (CoreQuotient M)) → B = ⊥ ∨ B = P)
    (hnon : ¬ lift M P ≤ centralizer (Z : Set G)) :
    lift M P ⊓ centralizer (sourceClosure ((lift M P ⊔ X) ⊔ (T : Subgroup G)) Z : Set G) =
      (lift M P).pCoreIn 2 := by
  let Y := lift M P
  let H := (Y ⊔ X) ⊔ (T : Subgroup G)
  have hMY : M ≤ normalizer (Y : Set G) :=
    lift_normalized M M le_rfl P (by rw [normalizer_eq_top]; exact le_top)
  exact centralizer_closure_eq_core T M H Y Z P hTM le_sup_right
    (sup_le (sup_le (lift_le M P) hXM) hTM) (le_sup_left.trans le_sup_left) hZT hTC hMY
    (lift_perfect M P) (image_lift M P (nine_perfect P hP)) hirr hnon

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.ActionKernel

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.ActionKernel
open FamilySource CentralizerNormalClosureCubic CentralizerNormalClosureCubic.OmegaEndgame
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem internal_closure_centralizer (H Z : Subgroup G) :
    centralizer (normalClosure (Z.subgroupOf H : Set H) : Set H) =
      (centralizer (sourceClosure H Z : Set G)).subgroupOf H := by
  ext h
  constructor
  · intro hc w hw
    obtain ⟨w, hw, rfl⟩ := hw
    exact congrArg Subtype.val (hc w hw)
  · intro hc w hw
    exact Subtype.ext (hc w (mem_map_of_mem H.subtype hw))

/-- The actual affine quotient has a marked natural nine-group, with the
original XT image as a disjoint supplement. Its centralizer is exactly that
nine-group. All kernel, image and complement conclusions are derived from
the original source normal closure and quotient maps. -/
theorem residual_nine_action_quotient (T : Sylow 2 G) (M X Z : Subgroup G)
    (P : Subgroup (CoreQuotient M)) [P.Normal] [IsElementaryAbelian 3 P]
    (hP : Nat.card P = 9) (hTM : (T : Subgroup G) ≤ M) (hXM : X ≤ M)
    (hZT : Z ≤ (T : Subgroup G)) (hTC : (T : Subgroup G) ≤ centralizer (Z : Set G))
    (hXC : X ≤ centralizer (Z : Set G))
    (hirr : ∀ B : Subgroup (CoreQuotient M), B ≤ P →
      image M (T : Subgroup G) ≤ normalizer (B : Set (CoreQuotient M)) → B = ⊥ ∨ B = P)
    (hnon : ¬ lift M P ≤ centralizer (Z : Set G)) :
    let Y := lift M P
    let S := X ⊔ (T : Subgroup G)
    let H := (Y ⊔ X) ⊔ (T : Subgroup G)
    let W := normalClosure (Z.subgroupOf H : Set H)
    let q := QuotientGroup.mk' (centralizer (W : Set H))
    let E := (Y.subgroupOf H).map q
    ∃ (eY : Y ⧸ pCore 2 Y ≃* P) (e : P ≃* E),
      (∀ y : Y,
        (eY (QuotientGroup.mk' (pCore 2 Y) y) : CoreQuotient M) =
          quotientMap M ⟨(y : G), lift_le M P y.property⟩ ∧
        (e (eY (QuotientGroup.mk' (pCore 2 Y) y)) : H ⧸ centralizer (W : Set H)) =
          q ⟨(y : G), (show Y ≤ H from le_sup_left.trans le_sup_left) y.property⟩) ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧ E.Normal ∧
      E ⊔ (S.subgroupOf H).map q = ⊤ ∧
      centralizer (E : Set (H ⧸ centralizer (W : Set H))) = E ∧
      Disjoint E ((S.subgroupOf H).map q) := by
  let Y := lift M P
  let S := X ⊔ (T : Subgroup G)
  let H := (Y ⊔ X) ⊔ (T : Subgroup G)
  let W := normalClosure (Z.subgroupOf H : Set H)
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let E := (Y.subgroupOf H).map q
  have hYH : Y ≤ H := le_sup_left.trans le_sup_left
  have hSH : S ≤ H := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hHM : H ≤ M := sup_le (sup_le (lift_le M P) hXM) hTM
  have hMY : M ≤ normalizer (Y : Set G) :=
    lift_normalized M M le_rfl P (by rw [normalizer_eq_top]; exact le_top)
  have hYC := residual_nine_centralizer_eq_core T M X Z P hP hTM hXM hZT hTC hirr hnon
  let f : Y →* E := (q.subgroupMap (Y.subgroupOf H)).comp
    (subgroupOfEquivOfLe hYH).symm.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hYH).symm.surjective
  have hkC : f.ker = (centralizer (sourceClosure H Z : Set G)).subgroupOf Y := by
    ext y
    change (f y = 1) ↔ _
    rw [Subtype.ext_iff]
    change (q ⟨(y : G), hYH y.property⟩ = 1) ↔ _
    have hq : q ⟨(y : G), hYH y.property⟩ = 1 ↔
        (⟨(y : G), hYH y.property⟩ : H) ∈ C :=
      QuotientGroup.eq_one_iff (N := C) _
    rw [hq, show C = (centralizer (sourceClosure H Z : Set G)).subgroupOf H
      from internal_closure_centralizer H Z]
    rfl
  have hk : f.ker = pCore 2 Y := by
    have he : f.ker = (Y ⊓ centralizer (sourceClosure H Z : Set G)).subgroupOf Y := by
      rw [hkC]
      ext y
      exact ⟨fun hy => ⟨y.property, hy⟩, fun hy => hy.2⟩
    rw [hYC] at he
    exact he.trans (comap_map_eq_self_of_injective Y.subtype_injective (pCore 2 Y))
  let eD : Y ⧸ pCore 2 Y ≃* E := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  obtain ⟨eY, heY⟩ := SourceCubic.nine_lift_quotient M P hP
  let e : P ≃* E := eY.symm.trans eD
  let hE : IsElementaryAbelian 3 E := IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  let := hE
  have hEc : Nat.card E = 9 := (Nat.card_congr e.symm.toEquiv).trans hP
  let : (Y.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hYH).mpr (hHM.trans hMY)
  have hgen : Y.subgroupOf H ⊔ S.subgroupOf H = ⊤ := by
    rw [← subgroupOf_sup hYH hSH]
    have he : Y ⊔ S = H := by simp only [S, H, sup_assoc]
    rw [he, subgroupOf_self]
  have hEn : E.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective C)
  have hjoin : E ⊔ (S.subgroupOf H).map q = ⊤ := by
    rw [← Subgroup.map_sup, hgen, map_top_of_surjective q (QuotientGroup.mk'_surjective C)]
  have hSC : S.subgroupOf H ≤ centralizer (Z.subgroupOf H : Set H) := by
    intro s hs z hz
    exact Subtype.ext ((sup_le hXC hTC) hs z hz)
  obtain ⟨hcent, hdis⟩ := centralizer_and_disjoint_quotient_images_of_fixed_normal_closure
    (Y.subgroupOf H) (S.subgroupOf H) (Z.subgroupOf H) hgen hSC
    (show IsMulCommutative E from inferInstance)
  refine ⟨eY, e, ?_, hE, hEc, hEn, hjoin, hcent, hdis⟩
  intro y
  refine ⟨heY y, ?_⟩
  change (eD (eY.symm (eY (QuotientGroup.mk' (pCore 2 Y) y))) : H ⧸ C) = _
  rw [eY.symm_apply_apply]
  rfl

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.ActionKernel
