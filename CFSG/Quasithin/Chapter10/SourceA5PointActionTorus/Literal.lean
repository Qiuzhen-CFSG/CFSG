module
public import CFSG.Quasithin.Chapter10.SourceA5PointActionTorus
public import CFSG.Quasithin.Chapter10.SourceA5PointActionModels
public import CFSG.Quasithin.Chapter10.SourceA5PointSmallImage

/-!
# The cubic contradiction on the literal point-action module

The original point component maps onto its actual image in the centralizer
quotient. Its solvable kernel normalizes the original smaller component,
and its restriction there is a two-group. Both facts come from the source
point-action producers. We identify the smaller image literally, lift a
model cubic through this map, and use conjugation equivariance on the
original orbit module to contradict movement of an original moved vector.

Source: Aschbacher–Smith, 10.2.9, printed pp.750–751.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- A cubic centralizing the actual smaller A5 section cannot move a vector
of the original moved module under the literal point-quotient action. -/
theorem source_a5_point_no_moving_action_cubic
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t v : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (I : Subgroup G) (hLI : L ≤ I) (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hout : ¬ I ≤ D.maximalLocal)
    (hCW : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hspan : ⁅D.fullModule,L⁆ ≤ conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I)
    (hr : IsPReduced 2 ((conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))))) :
    let P := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
    let H := I ⊔ P
    let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) I).subgroupOf H
    letI := hr.normal
    letI := hr.elementary
    let K := I.subgroupOf H
    let q := actionMk U
    let B := ((L.subgroupOf H).map q).subgroupOf (K.map q)
    ∀ (x : K.map q), orderOf x = 3 → x ∈ sectionCentralizer B →
      ∀ z : U, ((z : H) : G) ∈ ⁅D.fullModule,L⁆ →
        action U (x : ActionQuotient U) (Additive.ofMul z) ≠ Additive.ofMul z → False := by
  let P := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  let H := I ⊔ P
  let V := conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) I
  let U := V.subgroupOf H
  let := hr.normal
  let := hr.elementary
  let K := I.subgroupOf H
  let A := L.subgroupOf H
  let q := actionMk U
  let B := (A.map q).subgroupOf (K.map q)
  change ∀ (x : K.map q), orderOf x = 3 → x ∈ sectionCentralizer B →
    ∀ z : U, ((z : H) : G) ∈ ⁅D.fullModule,L⁆ →
      action U (x : ActionQuotient U) (Additive.ofMul z) ≠ Additive.ofMul z → False
  intro x hx3 hxB z hz hmove
  let i : I ≃* K := (subgroupOfEquivOfLe (show I ≤ H from le_sup_left)).symm
  let g := q.subgroupMap K
  let f : I →* K.map q := g.comp i.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective K).comp i.surjective
  have hLH : L ≤ H := hLI.trans le_sup_left
  let a : L.subgroupOf I ≃* A :=
    (subgroupOfEquivOfLe hLI).trans (subgroupOfEquivOfLe hLH).symm
  let : Group.IsSolvable g.ker := source_a5_point_component_action_kernel_solvable
    D I hLI hIX hI hout hCW hspan hr
  let j : f.ker →* g.ker :=
    (i.toMonoidHom.comp f.ker.subtype).codRestrict g.ker (fun y => y.property)
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective (f := j) (by
    intro y y' he
    apply Subtype.ext
    exact i.injective (congrArg Subtype.val he))
  have hV : V ≤ H := (conjugateSpanBy_le_self
    (inf_le_left.trans ((source_full_moved_le_component D).trans hLI))).trans le_sup_left
  have hkn : f.ker ≤ normalizer (L.subgroupOf I : Set I) := by
    intro y hy
    have hyq : q ((i y : K) : H) = 1 := congrArg Subtype.val hy
    have hyC : ((i y : K) : H) ∈ centralizer (U : Set H) :=
      (QuotientGroup.eq_one_iff _).mp hyq
    have hyVG : (y : G) ∈ centralizer (V : Set G) := by
      intro w hw
      exact congrArg H.subtype (hyC ⟨w,hV hw⟩ hw)
    have hyN := source_a5_point_action_centralizer_normalizes_component
      D ht htn hcross V hspan hCW hyVG
    intro l
    exact hyN (l : G)
  have hkA := (source_a5_point_small_image_twoCore D e I hLI hout hCW hspan hr).1
  let fL := f.subgroupMap (L.subgroupOf I)
  let gL := q.subgroupMap A
  let ja : fL.ker →* gL.ker := (a.toMonoidHom.comp fL.ker.subtype).codRestrict gL.ker (by
    intro y
    apply Subtype.ext
    exact congrArg (fun b : (L.subgroupOf I).map f => ((b : K.map q) : ActionQuotient U)) y.property)
  have hk : IsPGroup 2 fL.ker := hkA.of_injective ja (by
    intro y y' he
    apply Subtype.ext
    exact a.injective (congrArg Subtype.val he))
  have hB : (L.subgroupOf I).map f = B := by
    ext b
    constructor
    · rintro ⟨l,hl,rfl⟩
      exact mem_map.mpr ⟨⟨l,hLH hl⟩,hl,rfl⟩
    · rintro ⟨l,hl,he⟩
      exact ⟨⟨l,hLI hl⟩,hl,Subtype.ext he⟩
  have hxL : x ∈ sectionCentralizer ((L.subgroupOf I).map f) := by
    rwa [hB]
  obtain ⟨y,hy,hyC⟩ := source_a5_image_cubic_lifts_to_moved_centralizer
    D e hn ht htn hsep hNL I hLI f hf hkn hk hx3 hxL
  apply hmove
  have hyq : q ((i y : K) : H) = (x : ActionQuotient U) := congrArg Subtype.val hy
  rw [←hyq]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  have ha := congrArg H.subtype (action_apply U ((i y : K) : H) (Additive.ofMul z))
  exact ha.trans (by
    change (y : G) * ((z : H) : G) * (y : G)⁻¹ = ((z : H) : G)
    rw [←hyC _ hz,mul_inv_cancel_right])

end CFSG.Quasithin.Chapter10
