module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearStarNatural
public import Theory.Representation.SL2NaturalCommonQuotient

/-!
# The marked natural quotient of the same cubic-fixed chief section

Let C = C_(A/B)(X₁), for the original normal section A/B inside U. The
image Z in C of the original star kernel is exactly C_C(L⁺). The quotient
C/Z is trivial or the natural plane through the SAME point SL₂ projection
used on V/V₁ and on the dual annihilator. In the natural case, its
coordinates send the class of every original fixed representative to its
original star coordinates.

The star image and the image of the lower-endpoint kernel are invariant
under the original L⁺. Natural irreducibility therefore identifies their
common quotient; the natural plane has no fixed vectors, giving equality
of the full fixed subgroup with Z. Coprime lifting and both projections
are reused without changing either section endpoint. The final application
retains the selected faithful irreducible KX/O₂(KX) action and the surviving
original inner-cubic commutator.

This compares the cubic-fixed quotient, not every L⁺ constituent of W.
The full constituent comparison and adjoint-extension selection, the other
centralizer branch, common-normal existence and both triangle orientations
remain required. Ambient natural/dual multiplicities may still be zero.
Source: Aschbacher--Smith 11.1.2, printed pp.763--764, using G.2.5.
-/

open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
open SL3 SL3.PlaneAction ChapterG.Section02.LinearThree Matrix.PSL3.LinearThree

open NoncentralChiefRefinement
open scoped commutatorElement

/-- The original star projection, restricted only in its codomain to the
full original U-image. -/
def pointFixedStarImage {K X : Subgroup G} :
    let f := flag D S m
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let J := (K ⊔ X) ⊔ U
    ∀ (A : NormalNode J) (_hAU : A.val ≤ U.subgroupOf J),
      fixedRepresentatives A (E.subgroupOf J) →* (linearPointSetup D S m f).star U := by
  intro f E U J A hAU
  exact (pointFixedStarProjection D S m f A hAU).codRestrict _ (by
    intro a
    exact mem_map_of_mem _ (hAU a.val.property))

private theorem span_natural_coordinates
    (hd : S.field.degree = 2)
    (hfix : (flag D S m).Li 0 ≤ centralizer ((flag D S m).Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer ((flag D S m).Vi 0 : Set G)) K)
    (hLK : (flag D S m).Li 0 ≤ K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0) ≤
      centralizer ((flag D S m).Vi 0 : Set G))
    (hzero : let H := localResidual L (X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0))
      ⁅H.pCoreIn 2,H⁆ = ⊥) :
    let f := flag D S m
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    ∃ eStar : (linearPointSetup D S m f).star U ≃* Multiplicative (Fin 2 → S.field.Carrier),
        (∀ (l : f.Li 0) (u v : (linearPointSetup D S m f).star U),
          (v : (linearPointSetup D S m f).Star) =
            (starProjection (linearPointSetup D S m f) ⟨l,(localResidual_le _ l.property).1⟩ :
              (linearPointSetup D S m f).Star) * u *
            (starProjection (linearPointSetup D S m f) ⟨l,(localResidual_le _ l.property).1⟩ :
              (linearPointSetup D S m f).Star)⁻¹ →
          eStar v = Matrix.SL2.naturalAction S.field.Carrier
            (pointConstituentProjection D S m l) (eStar u)) := by
  intro f U
  obtain ⟨g,h,d,hUT,hf,hmodel,_,hpoint,hUeq,_⟩ :=
    linear_point_original_layers D S m f hd hfix hX hK hLK hk hp hcard hmove hzero
  obtain ⟨e0,he0⟩ := linear_point_star_natural_coordinates D S m d hmodel hpoint hUT hf
  let F := linearPointSetup D S m f
  let eStar : F.star U ≃* Multiplicative (Fin 2 → S.field.Carrier) :=
    (MulEquiv.subgroupCongr (congrArg F.star hUeq.symm)).trans e0
  have hstar (l : f.Li 0) (u v : F.star U)
      (hv : (v : F.Star) = (starProjection F ⟨l,(localResidual_le _ l.property).1⟩ : F.Star) *
        (u : F.Star) * (starProjection F ⟨l,(localResidual_le _ l.property).1⟩ : F.Star)⁻¹) :
      eStar v = Matrix.SL2.naturalAction S.field.Carrier
        (pointConstituentProjection D S m l) (eStar u) := he0 l _ _ hv
  exact ⟨eStar,hstar⟩

/-- On every original normal section in U, the star-kernel image is exactly
the L-plus fixed subgroup of its cubic-fixed part. The quotient is zero or
the natural plane with the ORIGINAL point marking; its coordinate equation
uses every original fixed representative and both original projections. -/
theorem linear_point_section_marked_natural_quotient
    (hd : S.field.degree = 2)
    (hfix : (flag D S m).Li 0 ≤ centralizer ((flag D S m).Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer ((flag D S m).Vi 0 : Set G)) K)
    (hLK : (flag D S m).Li 0 ≤ K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0) ≤
      centralizer ((flag D S m).Vi 0 : Set G))
    (hzero : let H := localResidual L (X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0))
      ⁅H.pCoreIn 2,H⁆ = ⊥) :
    let f := flag D S m
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := localResidual (f.Li 0) E
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let J := (K ⊔ X) ⊔ U
    ∀ (B A : NormalNode J) (_hBA : B ≤ A) (hAU : A.val ≤ U.subgroupOf J)
      (he : IsElementaryAbelian 2 (Section B A)), let _ := he
      let _ : CommGroup (Section B A) :=
        { (inferInstance : Group (Section B A)) with mul_comm := mul_comm' }
      let q := fixedProjection B A (E.subgroupOf J)
      let Z := QuotientGroup.CommonImage.kernelImage
        (pointFixedStarProjection D S m f A hAU) q
      Z = (sectionFixed B A (H.subgroupOf J)).subgroupOf (sectionFixed B A (E.subgroupOf J)) ∧
      ∃ eStar : (linearPointSetup D S m f).star U ≃* Multiplicative (Fin 2 → S.field.Carrier),
        (∀ (l : f.Li 0) (u v : (linearPointSetup D S m f).star U),
          (v : (linearPointSetup D S m f).Star) =
            (starProjection (linearPointSetup D S m f) ⟨l,(localResidual_le _ l.property).1⟩ :
              (linearPointSetup D S m f).Star) * u *
            (starProjection (linearPointSetup D S m f) ⟨l,(localResidual_le _ l.property).1⟩ :
              (linearPointSetup D S m f).Star)⁻¹ →
          eStar v = Matrix.SL2.naturalAction S.field.Carrier
            (pointConstituentProjection D S m l) (eStar u)) ∧
        (Z = ⊤ ∨ ∃ e : (sectionFixed B A (E.subgroupOf J) ⧸ Z) ≃*
          Multiplicative (Fin 2 → S.field.Carrier),
          ∀ a, e (QuotientGroup.mk' Z (q a)) = eStar (pointFixedStarImage D S m A hAU a)) := by
  intro f E H U J B A hBA hAU he
  let _ := he
  let _ : CommGroup (Section B A) :=
    { (inferInstance : Group (Section B A)) with mul_comm := mul_comm' }
  intro _ _ q Z
  obtain ⟨eStar,hstar⟩ := span_natural_coordinates D S m
    hd hfix hX hK hLK hk hp hcard hmove hzero
  let p := eStar.toMonoidHom.comp (pointFixedStarImage D S m A hAU)
  have hker : p.ker = (pointFixedStarProjection D S m f A hAU).ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ eStar.injective]
    exact MonoidHom.ker_codRestrict _ _ _
  have hZeq : QuotientGroup.CommonImage.kernelImage p q = Z := congrArg (Subgroup.map q) hker
  obtain ⟨hqs,_,hZle,_,_,_,_⟩ := linear_point_section_cubic_central_cover D S m f hd hfix
    hX hK hLK hk hp hcard hmove hzero B A hBA hAU he
  let hHJ : H ≤ J := ((localResidual_le E).trans inf_le_left).trans
    (hLK.trans (le_sup_left.trans le_sup_left))
  let r := (pointConstituentProjection D S m).comp
    (inclusion (show H ≤ f.Li 0 from (localResidual_le E).trans inf_le_left))
  have hrs : Function.Surjective r := linear_point_cubic_constituent_surjective D S m hcard
  have hact (h : H) (a : fixedRepresentatives A (E.subgroupOf J)) :
      ∃ b, (q b).val = sectionAction B A (inclusion hHJ h) (q a).val ∧
        p b = Matrix.SL2.naturalAction S.field.Carrier (r h) (p a) := by
    obtain ⟨hn,hh⟩ := linear_point_fixed_star_plus_action D S m f hLK hcard B A hAU h
    let b := conjugateFixed A (E.subgroupOf J) (inclusion hHJ h) hn a
    refine ⟨b,(hh a).1,?_⟩
    apply hstar (inclusion (show H ≤ f.Li 0 from (localResidual_le E).trans inf_le_left) h)
      (pointFixedStarImage D S m A hAU a) (pointFixedStarImage D S m A hAU b)
    exact (hh a).2
  obtain ⟨hZ,hquot⟩ := QuotientGroup.CommonImage.natural_quotient_fixed_kernel p q hqs r hrs Z
    ((sectionFixed B A (H.subgroupOf J)).subgroupOf (sectionFixed B A (E.subgroupOf J))) hZeq hZle
    (by intro h a; obtain ⟨b,_,hb⟩ := hact h a; exact ⟨b,hb⟩)
    (by
      intro h a ha
      obtain ⟨b,hb,hp⟩ := hact h a
      refine ⟨b,?_,hp⟩
      apply Subtype.ext
      rw [hb,ha]
      exact map_one _)
    (by
      intro h a ha
      obtain ⟨b,hb,hp⟩ := hact h a
      refine ⟨b,Subtype.ext (hb.trans ?_),hp⟩
      exact ha ⟨inclusion hHJ h,h.property⟩)
  exact ⟨hZ,eStar,hstar,hquot⟩

/-- The literal selected faithful chief section, retaining both endpoints,
its quotient representation and its surviving original cubic commutator. -/
theorem linear_point_chief_marked_natural_cover
    (hd : S.field.degree = 2)
    (hfix : (flag D S m).Li 0 ≤ centralizer ((flag D S m).Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer ((flag D S m).Vi 0 : Set G)) K)
    (hLK : (flag D S m).Li 0 ≤ K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0) ≤
      centralizer ((flag D S m).Vi 0 : Set G))
    (hzero : let H := localResidual L (X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0))
      ⁅H.pCoreIn 2,H⁆ = ⊥) :
    let f := flag D S m
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := localResidual (f.Li 0) E
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let J := (K ⊔ X) ⊔ U
    U ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 ∧
    ∃ B A : NormalNode J,
      (f.Vi 0).subgroupOf J ≤ B.val ∧ B ⋖ A ∧
      ∃ hAU : A.val ≤ U.subgroupOf J,
      ∃ he : IsElementaryAbelian 2 (Section B A), let _ := he
      let _ : CommGroup (Section B A) :=
        { (inferInstance : Group (Section B A)) with mul_comm := mul_comm' }
      ∃ ρ : Representation (ZMod 2)
        ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)) (Additive (Section B A)),
        Representation.IsIrreducible ρ ∧ Function.Injective ρ ∧
        ρ.comp (QuotientGroup.mk' (pCore 2 (K ⊔ X : Subgroup G))) =
          (binarySectionRepresentation B A).comp
            (inclusion (show K ⊔ X ≤ J from le_sup_left)) ∧
        (let q := fixedProjection B A (E.subgroupOf J)
         let Z := QuotientGroup.CommonImage.kernelImage
           (pointFixedStarProjection D S m f A hAU) q
         Function.Surjective q ∧
         Z = (sectionFixed B A (H.subgroupOf J)).subgroupOf (sectionFixed B A (E.subgroupOf J)) ∧
         ∃ eStar : (linearPointSetup D S m f).star U ≃* Multiplicative (Fin 2 → S.field.Carrier),
           (∀ (l : f.Li 0) (u v : (linearPointSetup D S m f).star U),
             (v : (linearPointSetup D S m f).Star) =
               (starProjection (linearPointSetup D S m f) ⟨l,(localResidual_le _ l.property).1⟩ :
                 (linearPointSetup D S m f).Star) * u *
               (starProjection (linearPointSetup D S m f) ⟨l,(localResidual_le _ l.property).1⟩ :
                 (linearPointSetup D S m f).Star)⁻¹ →
             eStar v = Matrix.SL2.naturalAction S.field.Carrier
               (pointConstituentProjection D S m l) (eStar u)) ∧
           (Z = ⊤ ∨ ∃ e : (sectionFixed B A (E.subgroupOf J) ⧸ Z) ≃*
             Multiplicative (Fin 2 → S.field.Carrier),
             ∀ a, e (QuotientGroup.mk' Z (q a)) = eStar (pointFixedStarImage D S m A hAU a))) ∧
        ∃ a : A.val, ((a : J) : G) ∈ U ⊓ centralizer (E : Set G) ∧
          ∃ z : (X ⊓ K : Subgroup G),
            ⁅inclusion (show X ⊓ K ≤ J from
              inf_le_left.trans (le_sup_right.trans le_sup_left)) z,(a : J)⁆ ∉ B.val := by
  intro f E H U J
  obtain ⟨hU,B,A,hZB,hBA,hAU,he,ρ,hirr,hfaith,hρ,hcover,hsurv⟩ :=
    linear_point_chief_cubic_central_cover D S m f hd hfix hX hK hLK hk hp hcard hmove hzero
  let _ := he
  let _ : CommGroup (Section B A) :=
    { (inferInstance : Group (Section B A)) with mul_comm := mul_comm' }
  obtain ⟨hZ,eStar,hact,hquot⟩ := linear_point_section_marked_natural_quotient D S m
    hd hfix hX hK hLK hk hp hcard hmove hzero B A hBA.le hAU he
  exact ⟨hU,B,A,hZB,hBA,hAU,he,ρ,hirr,hfaith,hρ,⟨hcover.1,hZ,eStar,hact,hquot⟩,hsurv⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
