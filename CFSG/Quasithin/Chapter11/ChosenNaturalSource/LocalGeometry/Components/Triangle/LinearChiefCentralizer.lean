module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearChiefLayers
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearChiefFixed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearLocalConstituents
public import Theory.GroupTheory.Commutator.SimpleSubnormal
public import Theory.GroupTheory.NoncentralChiefRefinement.FixedIndex
public import Theory.Representation.SL3.AdjointCubicCentralizer.FixedIndex

/-!
# The original chief section has a small cubic-fixed index

In the branch [O₂(L_X₁),L_X₁]=1, perfectness and a second-commutator
argument force C_{O₂(LT)}(X₁) to centralize L_X₁, hence L-plus.
The original G.2.5 star map has kernel U intersect O₂(LT) and image of
order sixteen. Therefore L-plus has fixed index at most sixteen on
C_U(X₁). Coprime fixed-point lifting carries this bound to the SAME
selected KX-chief section, with both endpoints, the faithful quotient
action and a surviving original X_K commutator retained.

The ordinary adjoint cubic-fixed action has index 64, so it is excluded
by an actual intertwining equation on this section. This proves the
terminal numerical contradiction conditional on that marked action;
it does not recognize or select the projective adjoint extension.
The natural/dual constituent comparison, determinant-twisted extension,
other centralizer branch, common-normal existence, both triangle
orientations and final source assembly remain required. No positive
multiplicity is assumed for either ambient marked layer.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.763--764, using G.2.5 and B.4.14.
-/

open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
@[expose] public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

include D in
/-- Centralization in the original two-core, before passing to any section. -/
theorem linear_cubic_core_fixed_centralizes (E : Subgroup G)
    (hzero : ⁅(localResidual L E).pCoreIn 2,localResidual L E⁆ = ⊥) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (E : Set G) ≤
      centralizer (localResidual L E : Set G) := by
  let J := L ⊔ (T : Subgroup G)
  let R := J.pCoreIn 2
  let H := localResidual L E
  let C := R ⊓ centralizer (E : Set G)
  let _ : Group.IsPerfect H := localResidual_perfect E
  have hHL : H ≤ L := (localResidual_le E).trans inf_le_left
  have hHJ : H ≤ J := hHL.trans le_sup_left
  have hJL : J ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer D.sylow_normalizes_component
  have hCH : C ≤ normalizer (H : Set G) :=
    ((le_inf ((inf_le_left.trans (pCoreIn_le 2 J)).trans hJL)
      ((inf_le_right.trans (Subgroup.centralizer_le_normalizer _)).trans
        (normalizer _).le_normalizer)).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have hHR : H ≤ normalizer (R : Set G) :=
    hHJ.trans (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 J)))
  have hcH : ⁅C,H⁆ ≤ H := le_normalizer_iff_commutator_le_right.mp hCH
  have hcR : ⁅C,H⁆ ≤ R := (commutator_mono inf_le_left le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp hHR)
  have hcore : ⁅C,H⁆ ≤ H.pCoreIn 2 := (le_inf hcH hcR).trans (inf_pCoreIn_le_of_le 2 hHJ)
  exact commutator_eq_bot_iff_le_centralizer.mp
    (commutator_eq_bot_of_iterated_eq_bot C H
      (bot_unique ((commutator_mono hcore le_rfl).trans hzero.le)))

/-- The same bound holds for the original L-plus, with its actual inclusion. -/
theorem linear_cubic_core_fixed_centralizes_point
    (f : InvariantFlag (.sl3 m)) (E : Subgroup G)
    (hzero : ⁅(localResidual L E).pCoreIn 2,localResidual L E⁆ = ⊥) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (E : Set G) ≤
      centralizer (localResidual (f.Li 0) E : Set G) := by
  have hle : localResidual (f.Li 0) E ≤ localResidual L E :=
    map_solvableResidual_mono (inf_le_inf ((localResidual_le _).trans inf_le_left) le_rfl)
  exact (linear_cubic_core_fixed_centralizes D E hzero).trans (centralizer_le hle)

open ChapterG.Section02.LinearThree

/-- The original cubic-fixed subgroup has L-plus fixed-point index at most
sixteen in the central-core branch. The bound uses the literal star map. -/
theorem linear_point_cubic_fixed_index
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
    (centralizer (H : Set G)).relIndex (U ⊓ centralizer (E : Set G)) ≤ 16 := by
  intro E H U
  obtain ⟨g,h,d,hUT,hf,_,_,_,hUeq,_⟩ :=
    linear_point_original_layers D S m f hd hfix hX hK hLK hk hp hcard hmove hzero
  let B := linearPointSetup D S m f
  let R := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let p := Hypothesis.UStarProjection B hUT
  have hpker : p.ker = R.subgroupOf B.U := by
    ext u
    change p u = 1 ↔ (u : G) ∈ R
    rw [Subtype.ext_iff]
    change QuotientGroup.mk' (pCore 2 B.LT)
      (inclusion (hUT.trans le_sup_right) u) = 1 ↔ _
    constructor
    · intro hu
      exact ⟨_,(QuotientGroup.eq_one_iff _).mp hu,rfl⟩
    · rintro ⟨v,hv,he⟩
      apply (QuotientGroup.eq_one_iff _).mpr
      have hh : v = inclusion (hUT.trans le_sup_right) u := Subtype.ext he
      rwa [←hh]
  have hi : R.relIndex U = 16 := by
    have hUeq' : B.U = U := hUeq
    rw [←hUeq']
    change (R.subgroupOf B.U).index = 16
    rw [←hpker,index_ker,p.range_eq_top_of_surjective (Hypothesis.UStarProjection_surjective hUT),
      Nat.card_congr (topEquiv : (⊤ : Subgroup (B.star B.U)) ≃* B.star B.U).toEquiv,
      d.card_star_U hUT hf,hd]
    decide
  let C := U ⊓ centralizer (E : Set G)
  have hc : R.subgroupOf C ≤ (centralizer (H : Set G)).subgroupOf C := by
    intro u hu
    exact linear_cubic_core_fixed_centralizes_point D S m f E hzero ⟨hu,u.property.2⟩
  exact (index_antitone hc).trans
    ((relIndex_le_of_le_right (show C ≤ U from inf_le_left) index_ne_zero_of_finite).trans_eq hi)

open NoncentralChiefRefinement

/-- The L-plus fixed index on the cubic-fixed part of any original normal
section inside U is at most sixteen. This includes the selected KX-chief
section without changing its endpoints, action or quotient map. -/
theorem linear_point_section_cubic_fixed_index
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
    ∀ B A : NormalNode J, B ≤ A → A.val ≤ U.subgroupOf J →
      (sectionFixed B A (H.subgroupOf J)).relIndex
        (sectionFixed B A (E.subgroupOf J)) ≤ 16 := by
  intro E H U J B A hBA hAU
  have hEJ : E ≤ J := inf_le_left.trans (le_sup_right.trans le_sup_left)
  have hHJ : H ≤ J := ((localResidual_le E).trans inf_le_left).trans
    (hLK.trans (le_sup_left.trans le_sup_left))
  have hUT : U ≤ (T : Subgroup G) := (linear_point_centralizer_span D S m f).2.1
  have hA : IsPGroup 2 A.val := ((T.isPGroup'.to_le hUT).comap_subtype).to_le hAU
  let _ := hA.isNilpotent
  have hEc : Nat.card (E.subgroupOf J) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEJ).toEquiv]
    exact hcard
  have hE : IsPGroup 3 (E.subgroupOf J) := IsPGroup.of_card (n := 1) (by simpa using hEc)
  have hc := IsPGroup.coprime_card_of_ne 3 2 (by decide) (E.subgroupOf J) A.val hE hA
  exact (sectionFixed_relIndex_le_ambient J U E H hEJ hHJ B A hBA hAU inferInstance hc).trans
    (linear_point_cubic_fixed_index D S m f hd hfix hX hK hLK hk hp hcard hmove hzero)

/-- The same selected faithful KX-chief section has both a surviving original
cubic commutator and the L-plus fixed-index bound. The quotient marking and
both section endpoints are retained. -/
theorem linear_point_chief_with_cubic_fixed_index
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
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let J := (K ⊔ X) ⊔ U
    U ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 ∧
    ∃ B A : NormalNode J,
      (f.Vi 0).subgroupOf J ≤ B.val ∧ B ⋖ A ∧ A.val ≤ U.subgroupOf J ∧
      ∃ he : IsElementaryAbelian 2 (Section B A),
      let _ := he
      ∃ ρ : Representation (ZMod 2)
        ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)) (Additive (Section B A)),
        Representation.IsIrreducible ρ ∧ Function.Injective ρ ∧
        ρ.comp (QuotientGroup.mk' (pCore 2 (K ⊔ X : Subgroup G))) =
          (binarySectionRepresentation B A).comp
            (inclusion (show K ⊔ X ≤ J from le_sup_left)) ∧
        (sectionFixed B A ((localResidual (f.Li 0) E).subgroupOf J)).relIndex
          (sectionFixed B A (E.subgroupOf J)) ≤ 16 ∧
        ∃ a : A.val, ((a : J) : G) ∈ U ⊓ centralizer (E : Set G) ∧
          ∃ z : (X ⊓ K : Subgroup G),
            ⁅inclusion (show X ⊓ K ≤ J from
              inf_le_left.trans (le_sup_right.trans le_sup_left)) z,(a : J)⁆ ∉ B.val := by
  intro E U J
  obtain ⟨hU,B,A,hZB,hBA,hAU,he,ρ,hirr,hfaith,hρ,hsurv⟩ :=
    linear_point_chief_with_surviving_cubic_commutator D S m f hd hfix hX hK hLK
      hk hp hcard hmove
  exact ⟨hU,B,A,hZB,hBA,hAU,he,ρ,hirr,hfaith,hρ,
    linear_point_section_cubic_fixed_index D S m f hd hfix hX hK hLK hk hp hcard hmove hzero
      B A hBA.le hAU,hsurv⟩

open Matrix Representation.SL3.AdjointCubicCentralizer

/-- The original section cannot have the ordinary adjoint cubic-fixed action:
its SL-two endomorphism model would have fixed index 64, against the bound 16.
This excludes that marked model; it does not select it from the SL-three
restriction and does not exclude the determinant-twisted extension. -/
theorem linear_point_section_not_adjoint_fixed_model
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
    let hHJ : H ≤ J := ((localResidual_le E).trans inf_le_left).trans
      (hLK.trans (le_sup_left.trans le_sup_left))
    ∀ B A : NormalNode J, B ≤ A → A.val ≤ U.subgroupOf J →
      ¬ ∃ (p : H →* Matrix.SpecialLinearGroup (Fin 2) S.field.Carrier)
        (e : sectionFixed B A (E.subgroupOf J) ≃*
          Multiplicative (Mat2 S.field.Carrier)),
        Function.Surjective p ∧
        ∀ (h : H) (w : sectionFixed B A (E.subgroupOf J)),
          sectionAction B A (inclusion hHJ h) w.val =
            (e.symm (Multiplicative.ofAdd
              (twoAction S.field.Carrier (p h) (e w).toAdd))).val := by
  intro E H U J hHJ B A hBA hAU
  rintro ⟨p,e,hps,he⟩
  let C := sectionFixed B A (E.subgroupOf J)
  let Z := sectionFixed B A (H.subgroupOf J)
  have hZ : Z.subgroupOf C = (twoFixed S.field.Carrier).comap e.toMonoidHom := by
    ext w
    constructor
    · intro hw
      change ∀ g, twoAction S.field.Carrier g (e w).toAdd = (e w).toAdd
      intro g
      obtain ⟨h,rfl⟩ := hps g
      have hz := hw (⟨inclusion hHJ h,h.property⟩ : H.subgroupOf J)
      have hh := (he h w).symm.trans hz
      have hh' : e.symm (Multiplicative.ofAdd
          (twoAction S.field.Carrier (p h) (e w).toAdd)) = w := Subtype.ext hh
      have hr := congrArg e hh'
      simpa only [e.apply_symm_apply,toAdd_ofAdd] using
        congrArg Multiplicative.toAdd hr
    · intro hw h
      have hh := he (⟨h,h.property⟩ : H) w
      have hz : Multiplicative.ofAdd
          (twoAction S.field.Carrier (p ⟨h,h.property⟩) (e w).toAdd) = e w :=
        Multiplicative.toAdd.injective (hw (p ⟨h,h.property⟩))
      rw [hz,e.symm_apply_apply] at hh
      exact hh
  have hi : Z.relIndex C = 64 := by
    change (Z.subgroupOf C).index = 64
    rw [hZ,index_comap,e.toMonoidHom.range_eq_top_of_surjective e.surjective,
      relIndex_top_right,twoFixed_index]
    have hF : Nat.card S.field.Carrier = 4 := by simpa [hd] using S.field.card_eq
    rw [hF]
    decide
  have hb := linear_point_section_cubic_fixed_index D S m f hd hfix hX hK hLK
    hk hp hcard hmove hzero B A hBA hAU
  change Z.relIndex C ≤ 16 at hb
  rw [hi] at hb
  omega

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
