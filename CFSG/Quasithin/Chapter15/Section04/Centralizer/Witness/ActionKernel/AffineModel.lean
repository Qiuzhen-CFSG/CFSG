module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.ActionKernel
public import Theory.Representation.AffineNine.SourceComparison
public import Theory.GroupTheory.ConjugateSpanKernel.CubicSupplement

/-!
# The actual affine model and centralizer core in 15.4.10

The original residual lift supplies the marked elementary nine-group and
the original XT complement. The genuine A.1 output is the order-24 image
of X acting on P in M/O₂(M), not an affine recognition premise. Quotient
markings transport this action to H/C_H(W); two-perfectness and determinant
give the natural special or full affine model. The original cubic quotient
of X and T-normalization then make C_H(W) a two-group, proving the literal
identity C_T(W)=O₂(C_H(W)).

Source: Aschbacher--Smith, 15.4.10, printed p. 1159. The preceding prime-five,
supercritical and extraspecial exclusions remain with the source witness
owner, as do the later q-hat estimates.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.ActionKernel.AffineModel
open FamilySource CentralizerNormalClosureCubic
open Representation.AffineNine
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem internal_centralizer (H Z : Subgroup G) :
    centralizer (normalClosure (Z.subgroupOf H : Set H) : Set H) =
      (centralizer (sourceClosure H Z : Set G)).subgroupOf H := by
  ext h
  constructor
  · intro hc w hw
    obtain ⟨w, hw, rfl⟩ := hw
    exact congrArg Subtype.val (hc w hw)
  · intro hc w hw
    exact Subtype.ext (hc w (mem_map_of_mem H.subtype hw))

/-- The original source configuration gives the natural affine-nine model
with both quotient markings and the original XT complement. The only new
earlier-source action input is the literal order-24 X-image on P. Xi supplies
two-perfectness and T-normalization; preceding 15.4.5 supplies the cubic core
quotient. In the same application the centralizer is proved to be a two-group and its intrinsic
two-core is identified with C_T(W). -/
theorem residual_nine_affine_model_and_core
    (T : Sylow 2 G) (M X Z : Subgroup G)
    (P : Subgroup (CoreQuotient M)) [P.Normal] [IsElementaryAbelian 3 P]
    (hP : Nat.card P = 9) (hTM : (T : Subgroup G) ≤ M) (hXM : X ≤ M)
    (hZT : Z ≤ (T : Subgroup G)) (hTC : (T : Subgroup G) ≤ centralizer (Z : Set G))
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G) Z)
    (hirr : ∀ B : Subgroup (CoreQuotient M), B ≤ P →
      image M (T : Subgroup G) ≤ normalizer (B : Set (CoreQuotient M)) → B = ⊥ ∨ B = P)
    (hnon : ¬ lift M P ≤ centralizer (Z : Set G))
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3)
    (hXaction : Nat.card
      (((MulAut.conjNormal : CoreQuotient M →* MulAut P).comp
        ((quotientMap M).comp (inclusion hXM))).range) = 24) :
    let Y := lift M P
    let S := X ⊔ (T : Subgroup G)
    let H := (Y ⊔ X) ⊔ (T : Subgroup G)
    let W := normalClosure (Z.subgroupOf H : Set H)
    let C := centralizer (W : Set H)
    let q := QuotientGroup.mk' C
    let B := (S.subgroupOf H).map q
    IsPGroup 2 C ∧
      (T : Subgroup G) ⊓ centralizer (sourceClosure H Z : Set G) =
        (H ⊓ centralizer (sourceClosure H Z : Set G)).pCoreIn 2 ∧
      ∃ (eY : Y ⧸ pCore 2 Y ≃* P) (c : P ≃* Translation),
        (∀ y : Y,
          (eY (QuotientGroup.mk' (pCore 2 Y) y) : CoreQuotient M) =
            quotientMap M ⟨(y : G), lift_le M P y.property⟩) ∧
        ((∃ (f : (H ⧸ C) ≃* Special) (b : B ≃* SpecialLinear),
          (∀ y : Y,
            f (q ⟨(y : G), (show Y ≤ H from le_sup_left.trans le_sup_left) y.property⟩) =
              SemidirectProduct.inl (c (eY (QuotientGroup.mk' (pCore 2 Y) y)))) ∧
          ∀ s : B, f s = SemidirectProduct.inr (b s)) ∨
        (∃ (f : (H ⧸ C) ≃* Full) (b : B ≃* LinearGroup),
          (∀ y : Y,
            f (q ⟨(y : G), (show Y ≤ H from le_sup_left.trans le_sup_left) y.property⟩) =
              SemidirectProduct.inl (c (eY (QuotientGroup.mk' (pCore 2 Y) y)))) ∧
          ∀ s : B, f s = SemidirectProduct.inr (b s))) := by
  have hpX : IsPPerfect 2 X := hX.1.2.1
  have hXC : X ≤ centralizer (Z : Set G) := hX.2.1
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) := hX.1.1
  let Y := lift M P
  let S := X ⊔ (T : Subgroup G)
  let H := (Y ⊔ X) ⊔ (T : Subgroup G)
  let W := normalClosure (Z.subgroupOf H : Set H)
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let E := (Y.subgroupOf H).map q
  let B := (S.subgroupOf H).map q
  have hYH : Y ≤ H := le_sup_left.trans le_sup_left
  have hXH : X ≤ H := le_sup_right.trans le_sup_left
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  have hSH : S ≤ H := sup_le hXH hTH
  have hHM : H ≤ M := sup_le (sup_le (lift_le M P) hXM) hTM
  have hMY : M ≤ normalizer (Y : Set G) :=
    lift_normalized M M le_rfl P (by rw [normalizer_eq_top]; exact le_top)
  let : (Y.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hYH).mpr (hHM.trans hMY)
  obtain ⟨eY, eP, hmark, hE, hEc, hEn, hjoin, hcent, hdis⟩ :=
    residual_nine_action_quotient T M X Z P hP hTM hXM hZT hTC hXC hirr hnon
  let : IsElementaryAbelian 3 E := hE
  let : E.Normal := hEn
  let aP : X →* MulAut P := (MulAut.conjNormal : CoreQuotient M →* MulAut P).comp
    ((quotientMap M).comp (inclusion hXM))
  let a : X →* (H ⧸ C) := q.comp (inclusion hXH)
  let aE : X →* MulAut E := (MulAut.conjNormal : (H ⧸ C) →* MulAut E).comp a
  have hequiv (h : H) (p : P) :
      eP (MulAut.conjNormal (quotientMap M (inclusion hHM h)) p) =
        MulAut.conjNormal (q h) (eP p) := by
    obtain ⟨v, rfl⟩ := eY.surjective p
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 Y) v
    let y' : Y := Y.normalizerMonoidHom ⟨(h : G), hMY (hHM h.property)⟩ y
    have hold : MulAut.conjNormal (quotientMap M (inclusion hHM h))
        (eY (QuotientGroup.mk' (pCore 2 Y) y)) =
          eY (QuotientGroup.mk' (pCore 2 Y) y') := by
      apply Subtype.ext
      change quotientMap M (inclusion hHM h) *
        (eY (QuotientGroup.mk' (pCore 2 Y) y) : CoreQuotient M) *
          (quotientMap M (inclusion hHM h))⁻¹ = _
      rw [(hmark y).1, (hmark y').1]
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [hold]
    apply Subtype.ext
    change (eP (eY (QuotientGroup.mk' (pCore 2 Y) y')) : H ⧸ C) =
      q h * (eP (eY (QuotientGroup.mk' (pCore 2 Y) y)) : H ⧸ C) * (q h)⁻¹
    rw [(hmark y').2, (hmark y).2, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hconj : (MulAut.congr eP).toMonoidHom.comp aP = aE := by
    apply MonoidHom.ext
    intro x
    apply MulEquiv.ext
    intro v
    obtain ⟨p, rfl⟩ := eP.surjective v
    change eP (aP x (eP.symm (eP p))) = aE x (eP p)
    rw [eP.symm_apply_apply]
    exact hequiv (inclusion hXH x) p
  have hcardE : Nat.card aE.range = 24 := by
    rw [← hconj, MonoidHom.range_comp]
    calc
      Nat.card (aP.range.map (MulAut.congr eP).toMonoidHom) = Nat.card aP.range :=
        (Nat.card_congr (aP.range.equivMapOfInjective (MulAut.congr eP).toMonoidHom
          (MulAut.congr eP).injective).toEquiv).symm
      _ = 24 := hXaction
  have haB : a.range ≤ B := by
    rintro d ⟨x, rfl⟩
    exact mem_map_of_mem q (show (inclusion hXH x) ∈ S.subgroupOf H from
      (le_sup_left : X ≤ S) x.property)
  obtain ⟨cE, hmodel⟩ := Representation.AffineNine.SourceComparison.special_or_full_of_marked_complement
    E B hEc hjoin hdis hcent a haB hpX hcardE
  have hinternal : C = (centralizer (sourceClosure H Z : Set G)).subgroupOf H :=
    internal_centralizer H Z
  have hYC : Y ⊓ centralizer (sourceClosure H Z : Set G) = Y.pCoreIn 2 :=
    residual_nine_centralizer_eq_core T M X Z P hP hTM hXM hZT hTC hirr hnon
  have hYtwo : IsPGroup 2 ((Y.subgroupOf H) ⊓ C : Subgroup H) := by
    have he : (Y.subgroupOf H) ⊓ C =
        (Y ⊓ centralizer (sourceClosure H Z : Set G)).subgroupOf H := by
      rw [hinternal]
      rfl
    rw [he, hYC]
    exact (isPGroup_pCoreIn 2 Y).comap_subtype
  have hXproper : ¬ X.subgroupOf H ≤ C := by
    intro hc
    have hbot : aE.range = ⊥ := by
      apply (Subgroup.eq_bot_iff_forall _).mpr
      rintro d ⟨x, rfl⟩
      have hx : a x = 1 := (QuotientGroup.eq_one_iff (N := C) _).mpr
        (hc (show (inclusion hXH x) ∈ X.subgroupOf H from x.property))
      change MulAut.conjNormal (a x) = 1
      rw [hx, map_one]
    have hc := card_eq_one.mpr hbot
    omega
  let eX := subgroupOfEquivOfLe hXH
  have hpXH : IsPPerfect 2 (X.subgroupOf H) :=
    hpX.of_surjective eX.symm.toMonoidHom eX.symm.surjective
  have hcXH : Nat.card (X.subgroupOf H ⧸ pCore 2 (X.subgroupOf H)) = 3 :=
    (Nat.card_congr (QuotientGroup.congr _ _ eX (pCore_map_iso 2 eX)).toEquiv).trans hX3
  have hTXH : (T : Subgroup G).subgroupOf H ≤ normalizer (X.subgroupOf H : Set H) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hTX ht) (x : G)
  have hSjoin : X.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = S.subgroupOf H :=
    (subgroupOf_sup hXH hTH).symm
  have hSsubtwo : IsPGroup 2 (C.subgroupOf (S.subgroupOf H)) := by
    rw [← hSjoin]
    exact twoGroup_kernel_on_cubic_residual_join (X.subgroupOf H)
      ((T : Subgroup G).subgroupOf H) C hpXH hcXH T.isPGroup'.comap_subtype hTXH hXproper
  have hStwo : IsPGroup 2 ((S.subgroupOf H) ⊓ C : Subgroup H) := by
    have hh : IsPGroup 2 (((S.subgroupOf H) ⊓ C).subgroupOf (S.subgroupOf H)) := by
      rwa [inf_subgroupOf_left]
    exact hh.of_equiv (subgroupOfEquivOfLe (show
      (S.subgroupOf H) ⊓ C ≤ S.subgroupOf H from inf_le_left))
  have hgen : Y.subgroupOf H ⊔ S.subgroupOf H = ⊤ := by
    rw [← subgroupOf_sup hYH hSH]
    have he : Y ⊔ S = H := by simp only [S, H, sup_assoc]
    rw [he, subgroupOf_self]
  have hCtwo : IsPGroup 2 C := twoGroup_kernel_of_disjoint_supplement_images
    (Y.subgroupOf H) (S.subgroupOf H) C hgen hdis hYtwo hStwo
  have hCmap : C.map H.subtype = H ⊓ centralizer (sourceClosure H Z : Set G) := by
    rw [hinternal, subgroupOf_map_subtype, inf_comm]
  have hCambtwo : IsPGroup 2 (H ⊓ centralizer (sourceClosure H Z : Set G) : Subgroup G) := by
    rw [← hCmap]
    exact hCtwo.map H.subtype
  have hCT : H ⊓ centralizer (sourceClosure H Z : Set G) ≤ (T : Subgroup G) := by
    intro x hx
    have hxC : (⟨x, hx.1⟩ : H) ∈ C := by
      rw [hinternal]
      exact hx.2
    exact hCtwo.le_sylow_of_normal (T.subtype hTH) hxC
  have hcore : (T : Subgroup G) ⊓ centralizer (sourceClosure H Z : Set G) =
      (H ⊓ centralizer (sourceClosure H Z : Set G)).pCoreIn 2 := by
    rw [pCoreIn_eq_self_of_isPGroup 2 _ hCambtwo]
    exact le_antisymm (le_inf (inf_le_left.trans hTH) inf_le_right)
      (le_inf hCT inf_le_right)
  refine ⟨hCtwo, hcore, eY, eP.trans cE, fun y => (hmark y).1, ?_⟩
  rcases hmodel with ⟨f, b, hfE, hfB, _⟩ | ⟨f, b, hfE, hfB, _⟩
  · left
    refine ⟨f, b, ?_, hfB⟩
    intro y
    rw [← (hmark y).2]
    exact hfE (eP (eY (QuotientGroup.mk' (pCore 2 Y) y)))
  · right
    refine ⟨f, b, ?_, hfB⟩
    intro y
    rw [← (hmark y).2]
    exact hfE (eP (eY (QuotientGroup.mk' (pCore 2 Y) y)))

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.ActionKernel.AffineModel
