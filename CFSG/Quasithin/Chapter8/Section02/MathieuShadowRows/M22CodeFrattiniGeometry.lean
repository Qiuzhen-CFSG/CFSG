module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeNormalClosure
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFrattiniGeometry
public import Theory.GroupTheory.RelativeQuotientMaps
import all Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFrattiniGeometry

/-!
# The original M22 moved four-space survives in E/Φ(E)

The literal inclusion B/U into the image J of RH in N(U)/U identifies its
moved space with W=[B/U,R]. The original selected-pair construction places
E, the normal closure of W, in O₂(J) and makes W survive Φ(E). The native
four-space theorem constructs an injective map of W into E/Φ(E), with image
of dimension four, and normal generation proves semisimplicity under R.
Both the section map and residual actor retain their original quotient formulas.

Source: Aschbacher--Smith 8.2.9, printed p.721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement MonoidAlgebra
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE HermitianSource Offenders.Parabolic.Construction
  Normalizer.SmallOvergroups Normalizer.ParabolicReduction.RankSieve
open MathieuCode.NormalizedShadowRows.M22CodeSection
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G]

private theorem literal_section_embedding
    (B R U L : Subgroup G)
    (hRB : R ≤ normalizer (B : Set G)) (hRU : R ≤ normalizer (U : Set G))
    [(U.subgroupOf B).Normal]
    (hBL : B ≤ L) (hRL : R ≤ L) (hLU : L ≤ normalizer (U : Set G)) :
    let N := normalizer (U : Set G)
    let J := SmallRows.localImage U L
    ∃ (j : (B ⧸ U.subgroupOf B) →* J) (a : R →* J),
      Function.Injective j ∧
      j.range = (SmallRows.localImage U B).subgroupOf J ∧
      a.range = (SmallRows.localImage U R).subgroupOf J ∧
      (∀ b : B, (j (QuotientGroup.mk' (U.subgroupOf B) b) : N ⧸ U.subgroupOf N) =
        QuotientGroup.mk' (U.subgroupOf N) ⟨b.val,hLU (hBL b.property)⟩) ∧
      (∀ r, (a r : N ⧸ U.subgroupOf N) =
        QuotientGroup.mk' (U.subgroupOf N) ⟨r.val,hRU r.property⟩) ∧
      (∀ r x, j (sectionAction R B U hRB hRU r x) = a r * j x * (a r)⁻¹) := by
  let N := normalizer (U : Set G)
  let q := QuotientGroup.mk' (U.subgroupOf N)
  let J := SmallRows.localImage U L
  let t := QuotientGroup.quotientMapSubgroupOfOfLe (le_refl U) (hBL.trans hLU)
  have ht (x : B ⧸ U.subgroupOf B) : t x ∈ J := by
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B) x
    exact ⟨inclusion (hBL.trans hLU) b,hBL b.property,rfl⟩
  let j := t.codRestrict J ht
  let a := (q.comp (inclusion hRU)).codRestrict J (fun r =>
    ⟨inclusion hRU r,hRL r.property,rfl⟩)
  refine ⟨j,a,?_,?_,?_,fun _ => rfl,fun _ => rfl,?_⟩
  · intro x y hxy
    exact QuotientGroup.quotientMapSubgroupOfOfLe_injective B N U
      (hBL.trans hLU) (congrArg Subtype.val hxy)
  · ext x
    constructor
    · rintro ⟨y,rfl⟩
      obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B) y
      exact ⟨inclusion (hBL.trans hLU) b,b.property,rfl⟩
    · rintro ⟨b,hb,hbx⟩
      refine ⟨QuotientGroup.mk' (U.subgroupOf B) ⟨b.val,hb⟩,?_⟩
      exact Subtype.ext hbx
  · ext x
    constructor
    · rintro ⟨r,rfl⟩
      exact ⟨inclusion hRU r,r.property,rfl⟩
    · rintro ⟨r,hr,hrx⟩
      exact ⟨⟨r.val,hr⟩,Subtype.ext hrx⟩
  · intro r x
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B) x
    apply Subtype.ext
    change q (inclusion (hBL.trans hLU)
      (B.normalizerMonoidHom (inclusion hRB r) b)) =
        q (inclusion hRU r) * q (inclusion (hBL.trans hLU) b) *
          (q (inclusion hRU r))⁻¹
    rw [←map_inv,←map_mul,←map_mul]
    rfl


private theorem m22_frattini_geometry [Finite G]
    (B R U L : Subgroup G) (f : R →* MathieuCode.M22Quintet.Q)
    (hs : M22FiveSection R B U f)
    (hRB : R ≤ normalizer (B : Set G)) (hRU : R ≤ normalizer (U : Set G))
    [(U.subgroupOf B).Normal] [IsElementaryAbelian 2 (B ⧸ U.subgroupOf B)]
    (σ : Representation (ZMod 2) R (Additive (B ⧸ U.subgroupOf B)))
    (hσ : ∀ x b, σ x (Additive.ofMul b) = Additive.ofMul (sectionAction R B U hRB hRU x b))
    (hBL : B ≤ L) (hRL : R ≤ L) (hLU : L ≤ normalizer (U : Set G))
    (hLR : L ≤ normalizer (R : Set G))
    (hE : IsPGroup 2 (normalClosure
      ((⁅(SmallRows.localImage U B).subgroupOf (SmallRows.localImage U L),
        (SmallRows.localImage U R).subgroupOf (SmallRows.localImage U L)⁆ :
          Subgroup (SmallRows.localImage U L)) : Set (SmallRows.localImage U L))))
    (hphi : let J := SmallRows.localImage U L
      let W := ⁅(SmallRows.localImage U B).subgroupOf J,(SmallRows.localImage U R).subgroupOf J⁆
      ¬ W ≤ (frattini (normalClosure (W : Set J))).map (normalClosure (W : Set J)).subtype) :
    let N := normalizer (U : Set G)
    let J := SmallRows.localImage U L
    let D := (SmallRows.localImage U R).subgroupOf J
    let W := ⁅(SmallRows.localImage U B).subgroupOf J,D⁆
    ∃ (j : (B ⧸ U.subgroupOf B) →* J) (a : R →* J),
      Function.Injective j ∧
      j.range = (SmallRows.localImage U B).subgroupOf J ∧ a.range = D ∧
      (∀ b : B, (j (QuotientGroup.mk' (U.subgroupOf B) b) : N ⧸ U.subgroupOf N) =
        QuotientGroup.mk' (U.subgroupOf N) ⟨b.val,hLU (hBL b.property)⟩) ∧
      (∀ r, (a r : N ⧸ U.subgroupOf N) =
        QuotientGroup.mk' (U.subgroupOf N) ⟨r.val,hRU r.property⟩) ∧
      (∀ r x, j (sectionAction R B U hRB hRU r x) = a r * j x * (a r)⁻¹) ∧
      M22MovedFrattiniGeometry σ j a W hE := by
  let N := normalizer (U : Set G)
  let J := SmallRows.localImage U L
  let Dq := SmallRows.localImage U R
  let D := Dq.subgroupOf J
  let W := ⁅(SmallRows.localImage U B).subgroupOf J,D⁆
  obtain ⟨j,a,hji,hjr,har,hjq,haq,hja⟩ :=
    literal_section_embedding B R U L hRB hRU hBL hRL hLU
  have hjσ (r : R) (x : B ⧸ U.subgroupOf B) :
      j ((σ r (Additive.ofMul x)).toMul) = a r * j x * (a r)⁻¹ := by
    rw [hσ]
    exact hja r x
  have hW : (Coinvariants.ker σ).toAddSubgroup.toSubgroup'.map j = W := by
    rw [moved_image_commutator σ j a hjσ,hjr,har]
  change ∃ j a, _
  refine ⟨j,a,hji,hjr,har,hjq,haq,hja,?_⟩
  have hDJ : Dq ≤ J := map_mono (subgroupOf_mono N hRL)
  have hLN : L.subgroupOf N ≤ normalizer (R.subgroupOf N : Set N) :=
    (subgroupOf_mono N hLR).trans (le_normalizer_comap N.subtype)
  have hJD : J ≤ normalizer (Dq : Set (N ⧸ U.subgroupOf N)) :=
    (map_mono hLN).trans (le_normalizer_map (QuotientGroup.mk' (U.subgroupOf N)))
  let : D.Normal := (normal_subgroupOf_iff_le_normalizer hDJ).mpr hJD
  obtain ⟨_,_,_,r,eB,hrs,_,_,hact,_⟩ := hs
  let e : Additive (B ⧸ U.subgroupOf B) ≃ₗ[ZMod 2] Additive MathieuCode.M22Quintet.K :=
    LinearEquiv.ofBijective (eB.toAdditive.toAddMonoidHom.toZModLinearMap 2) eB.bijective
  have he (r' : R) (v : Additive (B ⧸ U.subgroupOf B)) :
      e (σ r' v) = MathieuCode.NormalizedShadowRows.M22CodeSection.fiveAction (r r') (e v) :=
    (congrArg (fun w => Additive.ofMul (eB w.toMul)) (hσ r' v.toMul)).trans (hact r' v.toMul)
  exact normalClosure_moved_geometry σ r hrs e he j a hjσ D W har hW hE hphi

/-- The original selected M22 pair supplies a surviving natural four-space
inside its normal-closure Frattini module. The full module is semisimple under
R, and both the section and actor maps retain their original quotient formulas. -/
theorem selected_m22_normalClosure_geometry [Finite G]
    {V H M I R U : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 U]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (hTH : (T : Subgroup G) ≤ H)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hHR : H ≤ normalizer (R : Set G))
    (hRP : R ≤ normalizer (I.pCoreIn 2 : Set G))
    (hPH : I.pCoreIn 2 ≤ H.pCoreIn 2)
    (hHU : H ≤ normalizer (U : Set G))
    {f : R →* MathieuCode.M22Quintet.Q}
    (hs : M22FiveSection R (V ⊓ I.pCoreIn 2) U f) :
    let N := normalizer (U : Set G)
    let J := SmallRows.localImage U (R ⊔ H)
    let B := V ⊓ I.pCoreIn 2
    let Bq := SmallRows.localImage U B
    let D := (SmallRows.localImage U R).subgroupOf J
    let W := ⁅Bq.subgroupOf J,D⁆
    let E := normalClosure (W : Set J)
    ∃ hE : IsPGroup 2 E,
      ∃ hRB : R ≤ normalizer (B : Set G),
        ∃ hRU : R ≤ normalizer (U : Set G),
          ∃ hBU : (U.subgroupOf B).Normal, letI := hBU
            ∃ hEl : IsElementaryAbelian 2 (B ⧸ U.subgroupOf B), letI := hEl
              ∃ σ : Representation (ZMod 2) R (Additive (B ⧸ U.subgroupOf B)),
                (∀ x b, σ x (Additive.ofMul b) =
                  Additive.ofMul (sectionAction R B U hRB hRU x b)) ∧
                ∃ (j : (B ⧸ U.subgroupOf B) →* J) (a : R →* J),
                  Function.Injective j ∧ j.range = Bq.subgroupOf J ∧ a.range = D ∧
                  (∀ b : B, (j (QuotientGroup.mk' (U.subgroupOf B) b) :
                      N ⧸ U.subgroupOf N) = QuotientGroup.mk' (U.subgroupOf N)
                    ⟨b.val,hHU ((pCoreIn_le 2 H) (hPH b.property.2))⟩) ∧
                  (∀ r, (a r : N ⧸ U.subgroupOf N) = QuotientGroup.mk' (U.subgroupOf N)
                    ⟨r.val,hRU r.property⟩) ∧
                  (∀ r x, j (sectionAction R B U hRB hRU r x) = a r * j x * (a r)⁻¹) ∧
                  M22MovedFrattiniGeometry σ j a W hE := by
  obtain ⟨hEcore,hE,hW,hphi⟩ := selected_m22_moved_normalClosure
    s hTH hTV hHR hRP hPH hHU hs
  have hs' := hs
  obtain ⟨hRB,hRU,hBU,_,_,_,_,_,_,_,hEl,σ,hσ,_,_,_⟩ := hs'
  let := hBU
  let := hEl
  have hBL : V ⊓ I.pCoreIn 2 ≤ R ⊔ H :=
    inf_le_right.trans ((pCoreIn_le 2 I).trans (s.family.le_ambient.trans le_sup_right))
  obtain ⟨j,a,hji,hjr,har,hjq,haq,hja,hgeom⟩ :=
    m22_frattini_geometry (V ⊓ I.pCoreIn 2) R U (R ⊔ H) f hs hRB hRU σ hσ
      hBL le_sup_left (sup_le hRU hHU) (sup_le R.le_normalizer hHR) hE hphi
  exact ⟨hE,hRB,hRU,hBU,hEl,σ,hσ,j,a,hji,hjr,har,hjq,haq,hja,hgeom⟩

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
