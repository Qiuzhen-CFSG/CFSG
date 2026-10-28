module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearChiefCentralizer
public import Theory.GroupTheory.NoncentralChiefRefinement.FixedCover
public import Theory.GroupTheory.QuotientCommonImage

/-!
# The original star image on the selected cubic-fixed chief section

For the SAME selected section W = A/B, take the two literal maps from
C_A(X₁): the section projection q and the LT/O₂(LT) projection p. The
kernel of q is C_B(X₁); the kernel of p is the intersection with O₂(LT).
In the central-core branch, Z = q(ker p) is pointwise fixed by L-plus.
The two-projection isomorphism identifies C_W(X₁)/Z with p(C_A(X₁))
modulo p(C_B(X₁)). The actual star image has order dividing sixteen.
Both projections intertwine conjugation by the original L-plus.

The final application retains the selected endpoints, faithful irreducible
KX/O₂(KX) representation, original quotient action and surviving X_K
commutator. Thus this is a comparison on the actual selected section,
stronger than a numerical fixed-index bound. It is not yet the marked
natural-plane identification or the comparison of every L-plus constituent
of W. Those steps, selection of the adjoint extension, the other centralizer
branch, common-normal existence and both triangle orientations remain open.
No positivity of either ambient natural/dual multiplicity is assumed.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.763--764, using G.2.5 and coprime fixed-point lifting.
-/

open Subgroup Theory.GroupTheory Representation NoncentralChiefRefinement
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- The original LT/two-core map on the selected section's fixed representatives. -/
def pointFixedStarProjection (f : InvariantFlag (.sl3 m)) {K X : Subgroup G} :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let J := (K ⊔ X) ⊔ U
    ∀ A : NormalNode J, A.val ≤ U.subgroupOf J →
      fixedRepresentatives A (E.subgroupOf J) →*
        ((L ⊔ (T : Subgroup G) : Subgroup G) ⧸ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) := by
  intro E U J A hAU
  exact (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))).comp
    { toFun := fun a => ⟨((a.val : J) : G),
        ((linear_point_centralizer_span D S m f).2.1.trans le_sup_right) (hAU a.val.property)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }

/-- Its kernel is the original O₂(LT), intersected with the fixed representatives. -/
theorem pointFixedStarProjection_eq_one (f : InvariantFlag (.sl3 m)) {K X : Subgroup G} :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let J := (K ⊔ X) ⊔ U
    ∀ (A : NormalNode J) (hAU : A.val ≤ U.subgroupOf J)
      (a : fixedRepresentatives A (E.subgroupOf J)),
      pointFixedStarProjection D S m f A hAU a = 1 ↔
        ((a.val : J) : G) ∈ (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 := by
  intro E U J A hAU a
  change QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) ⟨_,_⟩ = 1 ↔ _
  rw [QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
  constructor
  · intro ha
    exact mem_map_of_mem (L ⊔ (T : Subgroup G) : Subgroup G).subtype ha
  · rintro ⟨x,hx,he⟩
    have hh : x = ⟨((a.val : J) : G),
        ((linear_point_centralizer_span D S m f).2.1.trans le_sup_right) (hAU a.val.property)⟩ :=
      Subtype.ext he
    exact hh ▸ hx

/-- Conjugation uses the actual star projection of the original actor. -/
theorem pointFixedStarProjection_conjugate (f : InvariantFlag (.sl3 m)) {K X : Subgroup G} :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let J := (K ⊔ X) ⊔ U
    ∀ (A : NormalNode J) (hAU : A.val ≤ U.subgroupOf J)
      (j : J) (hj : j ∈ normalizer (centralizer (E.subgroupOf J : Set J) : Set J))
      (hjLT : (j : G) ∈ L ⊔ (T : Subgroup G))
      (a : fixedRepresentatives A (E.subgroupOf J)),
      pointFixedStarProjection D S m f A hAU (conjugateFixed A (E.subgroupOf J) j hj a) =
        QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) ⟨j,hjLT⟩ *
          pointFixedStarProjection D S m f A hAU a *
          (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) ⟨j,hjLT⟩)⁻¹ := by
  intro E U J A hAU j hj hjLT a
  let q := QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
  let b : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨((a.val : J) : G),
    ((linear_point_centralizer_span D S m f).2.1.trans le_sup_right) (hAU a.val.property)⟩
  change q (⟨j,hjLT⟩ * b * (⟨j,hjLT⟩ : (L ⊔ (T : Subgroup G) : Subgroup G))⁻¹) =
    q ⟨j,hjLT⟩ * q b * (q ⟨j,hjLT⟩)⁻¹
  rw [map_mul,map_mul,map_inv]

/-- The actual image of the star kernel is L-plus central on the same section. -/
theorem linear_point_section_star_kernel_fixed
    (f : InvariantFlag (.sl3 m)) {K X : Subgroup G}
    (hzero : let H := localResidual L (X ⊓ Closure.coreQuotientCentralizer (f.Li 0))
      ⁅H.pCoreIn 2,H⁆ = ⊥) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := localResidual (f.Li 0) E
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let J := (K ⊔ X) ⊔ U
    ∀ (B A : NormalNode J) (hAU : A.val ≤ U.subgroupOf J),
      (pointFixedStarProjection D S m f A hAU).ker.map (fixedProjection B A (E.subgroupOf J)) ≤
        (sectionFixed B A (H.subgroupOf J)).subgroupOf (sectionFixed B A (E.subgroupOf J)) := by
  intro E H U J B A hAU
  apply fixedProjection_image_fixed
  intro a ha
  have har : ((a.val : J) : G) ∈ (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 :=
    (pointFixedStarProjection_eq_one D S m f A hAU a).mp ha
  have hae : ((a.val : J) : G) ∈ centralizer (E : Set G) := by
    intro e he
    have hEJ : E ≤ J := inf_le_left.trans (le_sup_right.trans le_sup_left)
    have heJ : e ∈ J := hEJ he
    exact congrArg Subtype.val (a.property (⟨e,heJ⟩ : J) he)
  have hc := linear_cubic_core_fixed_centralizes_point D S m f E hzero ⟨har,hae⟩
  intro h hh
  exact Subtype.ext (hc h hh)

/-- L-plus acts on both original projections, through its literal inclusion
and its actual LT/two-core image. No action matching premise is supplied. -/
theorem linear_point_fixed_star_plus_action
    (f : InvariantFlag (.sl3 m)) {K X : Subgroup G}
    (hLK : f.Li 0 ≤ K)
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := localResidual (f.Li 0) E
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let J := (K ⊔ X) ⊔ U
    let hHJ : H ≤ J := ((localResidual_le E).trans inf_le_left).trans
      (hLK.trans (le_sup_left.trans le_sup_left))
    let hHLT : H ≤ L ⊔ (T : Subgroup G) :=
      (((localResidual_le E).trans inf_le_left).trans
        ((localResidual_le _).trans inf_le_left)).trans le_sup_left
    ∀ (B A : NormalNode J) (hAU : A.val ≤ U.subgroupOf J) (h : H),
      ∃ hn : inclusion hHJ h ∈ normalizer (centralizer (E.subgroupOf J : Set J) : Set J),
      ∀ a : fixedRepresentatives A (E.subgroupOf J),
        (fixedProjection B A (E.subgroupOf J)
          (conjugateFixed A (E.subgroupOf J) (inclusion hHJ h) hn a)).val =
            sectionAction B A (inclusion hHJ h) (fixedProjection B A (E.subgroupOf J) a).val ∧
        pointFixedStarProjection D S m f A hAU
          (conjugateFixed A (E.subgroupOf J) (inclusion hHJ h) hn a) =
          QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) (inclusion hHLT h) *
            pointFixedStarProjection D S m f A hAU a *
            (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
              (inclusion hHLT h))⁻¹ := by
  intro E H U J hHJ hHLT B A hAU h
  have hc : inclusion hHJ h ∈ centralizer (E.subgroupOf J : Set J) := by
    intro e he
    exact Subtype.ext ((linear_point_cubic_residual_cover D S m f hcard).1 h.property e he)
  let hn := (centralizer (E.subgroupOf J : Set J)).le_normalizer hc
  refine ⟨hn,fun a => ⟨fixedProjection_conjugate B A (E.subgroupOf J) _ hn a,?_⟩⟩
  exact pointFixedStarProjection_conjugate D S m f A hAU (inclusion hHJ h) hn (hHLT h.property) a

open ChapterG.Section02.LinearThree

/-- A central cover of the selected cubic-fixed section by a subquotient of
its original star image. The image has order dividing sixteen. -/
theorem linear_point_section_cubic_central_cover
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤ centralizer (f.Vi 0 : Set G))
    (hzero : let H := localResidual L (X ⊓ Closure.coreQuotientCentralizer (f.Li 0))
      ⁅H.pCoreIn 2,H⁆ = ⊥) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := localResidual (f.Li 0) E
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let J := (K ⊔ X) ⊔ U
    ∀ (B A : NormalNode J), B ≤ A → ∀ hAU : A.val ≤ U.subgroupOf J,
    ∀ he : IsElementaryAbelian 2 (Section B A), let _ := he
    let p := pointFixedStarProjection D S m f A hAU
    let q := fixedProjection B A (E.subgroupOf J)
    Function.Surjective q ∧
    (q.ker = (B.val.subgroupOf A.val).subgroupOf (fixedRepresentatives A (E.subgroupOf J))) ∧
    (p.ker.map q ≤ (sectionFixed B A (H.subgroupOf J)).subgroupOf
      (sectionFixed B A (E.subgroupOf J))) ∧
    Nat.card p.range ∣ 16 ∧
    Function.Surjective (QuotientGroup.CommonImage.map p q) ∧
    (QuotientGroup.CommonImage.map p q).ker = q.ker.map p.rangeRestrict ∧
    Nonempty ((p.range ⧸ q.ker.map p.rangeRestrict) ≃*
      ((sectionFixed B A (E.subgroupOf J)) ⧸ QuotientGroup.CommonImage.kernelImage p q)) := by
  intro E H U J B A hBA hAU he _ p q
  let _ := he
  have hqs : Function.Surjective q := by
    intro w
    obtain ⟨a,ha,heq⟩ := linear_point_section_fixed_lift D S m f hcard B A hBA hAU w.val
      (fun e => w.property ⟨inclusion (show E ≤ J from
        inf_le_left.trans (le_sup_right.trans le_sup_left)) e,e.property⟩)
    have hfixa : a ∈ fixedRepresentatives A (E.subgroupOf J) := by
      intro e he
      exact Subtype.ext (ha.2 e he)
    exact ⟨⟨a,hfixa⟩,Subtype.ext heq⟩
  have hdiv : Nat.card p.range ∣ 16 := by
    obtain ⟨g,h,d,hUT,hf,_,_,_,hUeq,_⟩ :=
      linear_point_original_layers D S m f hd hfix hX hK hLK hk hp hcard hmove hzero
    let F := linearPointSetup D S m f
    have hle : p.range ≤ F.star F.U := by
      rintro _ ⟨a,rfl⟩
      refine ⟨⟨((a.val : J) : G),
        ((linear_point_centralizer_span D S m f).2.1.trans le_sup_right) (hAU a.val.property)⟩,?_,rfl⟩
      change ((a.val : J) : G) ∈ F.U
      rw [hUeq]
      exact hAU a.val.property
    have hc : Nat.card (F.star F.U) = 16 := by
      rw [d.card_star_U hUT hf,hd]
      decide
    exact hc ▸ card_dvd_of_le hle
  exact ⟨hqs,fixedProjection_ker B A (E.subgroupOf J),
    linear_point_section_star_kernel_fixed D S m f hzero B A hAU,hdiv,
    QuotientGroup.CommonImage.map_surjective p q hqs,QuotientGroup.CommonImage.map_ker p q,
    ⟨QuotientGroup.CommonImage.equiv p q hqs⟩⟩

/-- The selected faithful chief section itself carries the central cover,
with the original surviving inner-cubic commutator and both endpoints. -/
theorem linear_point_chief_cubic_central_cover
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤ centralizer (f.Vi 0 : Set G))
    (hzero : let H := localResidual L (X ⊓ Closure.coreQuotientCentralizer (f.Li 0))
      ⁅H.pCoreIn 2,H⁆ = ⊥) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := localResidual (f.Li 0) E
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let J := (K ⊔ X) ⊔ U
    U ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 ∧
    ∃ B A : NormalNode J,
      (f.Vi 0).subgroupOf J ≤ B.val ∧ B ⋖ A ∧
      ∃ hAU : A.val ≤ U.subgroupOf J,
      ∃ he : IsElementaryAbelian 2 (Section B A), let _ := he
      ∃ ρ : Representation (ZMod 2)
        ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)) (Additive (Section B A)),
        Representation.IsIrreducible ρ ∧ Function.Injective ρ ∧
        ρ.comp (QuotientGroup.mk' (pCore 2 (K ⊔ X : Subgroup G))) =
          (binarySectionRepresentation B A).comp
            (inclusion (show K ⊔ X ≤ J from le_sup_left)) ∧
        (let p := pointFixedStarProjection D S m f A hAU
         let q := fixedProjection B A (E.subgroupOf J)
         let Z := QuotientGroup.CommonImage.kernelImage p q
         Function.Surjective q ∧
         Z ≤ (sectionFixed B A (H.subgroupOf J)).subgroupOf (sectionFixed B A (E.subgroupOf J)) ∧
         Nat.card ((sectionFixed B A (E.subgroupOf J)) ⧸ Z) ∣ 16 ∧
         Nonempty ((p.range ⧸ q.ker.map p.rangeRestrict) ≃*
           ((sectionFixed B A (E.subgroupOf J)) ⧸ Z))) ∧
        ∃ a : A.val, ((a : J) : G) ∈ U ⊓ centralizer (E : Set G) ∧
          ∃ z : (X ⊓ K : Subgroup G),
            ⁅inclusion (show X ⊓ K ≤ J from
              inf_le_left.trans (le_sup_right.trans le_sup_left)) z,(a : J)⁆ ∉ B.val := by
  intro E H U J
  obtain ⟨hU,B,A,hZB,hBA,hAU,he,ρ,hirr,hfaith,hρ,_,hsurv⟩ :=
    linear_point_chief_with_cubic_fixed_index D S m f hd hfix hX hK hLK hk hp hcard hmove hzero
  let _ := he
  obtain ⟨hqs,_,hZ,hdiv,_,_,heq⟩ := linear_point_section_cubic_central_cover D S m f hd hfix
    hX hK hLK hk hp hcard hmove hzero B A hBA.le hAU he
  exact ⟨hU,B,A,hZB,hBA,hAU,he,ρ,hirr,hfaith,hρ,
    ⟨hqs,hZ,(QuotientGroup.CommonImage.card_quotient_dvd _ _ hqs).trans hdiv,heq⟩,hsurv⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
