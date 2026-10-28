module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearChiefFaithfulness
public import Theory.GroupTheory.NoncentralChiefRefinement.CoprimeFixed
public import Theory.GroupAction.ExtraspecialCubicFixedMovement

/-!
# Original cubic-fixed vectors on the faithful chief section

Coprime fixed-point lifting puts every cubic-fixed section vector under
the literal quotient map of the original C_U(X₁). Faithfulness of the
selected KX/O₂(KX) action also makes the marked extraspecial Sylow act
faithfully on that same section. Its fixed-point detection theorem supplies
an X₁-fixed vector moved by X_K. Lifting this vector gives an actual element
of C_U(X₁) whose commutator with an element of X_K survives above the lower
endpoint of the selected chief section.

The final theorem constructs the endpoints, faithful irreducible quotient
representation, and original surviving commutator together. No selected
chief-factor, fixed-lift or movement premise is added to the source input.
This prepares the natural/dual comparison; it does not identify the
projective adjoint extension or settle the centralizer exclusions.
Common-normal existence and the full triangle assembly remain open.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.763--764, the cubic displacement and chief-factor steps.
-/

open Subgroup Theory.GroupTheory Representation NoncentralChiefRefinement
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- Every fixed vector of a normal section inside U lifts to the original
cubic centralizer under the literal quotient map. -/
theorem linear_point_section_fixed_lift
    (f : InvariantFlag (.sl3 m)) {K X : Subgroup G}
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let J := (K ⊔ X) ⊔ U
    ∀ B A : NormalNode J, B ≤ A → A.val ≤ U.subgroupOf J →
    ∀ w : Section B A,
      (∀ e : E, sectionAction B A
        (inclusion (show E ≤ J from inf_le_left.trans (le_sup_right.trans le_sup_left)) e) w = w) →
    ∃ a : A.val, ((a : J) : G) ∈ U ⊓ centralizer (E : Set G) ∧
      QuotientGroup.mk' (B.val.subgroupOf A.val) a = w := by
  intro E U J B A hBA hAU w hw
  have hEJ : E ≤ J := inf_le_left.trans (le_sup_right.trans le_sup_left)
  let E' := E.subgroupOf J
  have hUT : U ≤ (T : Subgroup G) := (linear_point_centralizer_span D S m f).2.1
  have hA : IsPGroup 2 A.val := ((T.isPGroup'.to_le hUT).comap_subtype).to_le hAU
  have hEc : Nat.card E' = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEJ).toEquiv]
    exact hcard
  have hE3 : IsPGroup 3 E' := IsPGroup.of_card (n := 1) (by simpa using hEc)
  have hc : Nat.Coprime (Nat.card E') (Nat.card A.val) :=
    IsPGroup.coprime_card_of_ne 3 2 (by decide) E' A.val hE3 hA
  let _ := hA.isNilpotent
  obtain ⟨a,ha,he⟩ := section_fixed_lift B A hBA E' inferInstance hc w
    (fun e => hw ⟨e,e.property⟩)
  refine ⟨a,⟨hAU a.property,?_⟩,he⟩
  intro e he
  exact congrArg Subtype.val (ha (⟨e,hEJ he⟩ : J) he)

/-- Fixed vectors of the selected faithful irreducible quotient representation
lift to the original C_U(X₁), preserving its representation marking. -/
theorem linear_point_chief_faithful_fixed_lifts
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤ centralizer (f.Vi 0 : Set G)) :
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
        ((binarySectionRepresentation B A).comp
          (inclusion (show K ⊔ X ≤ J from le_sup_left))).ker =
            pCore 2 (K ⊔ X : Subgroup G) ∧
        (∃ k : K, ρ (QuotientGroup.mk' (pCore 2 (K ⊔ X : Subgroup G))
          (inclusion (show K ≤ K ⊔ X from le_sup_left) k)) ≠ 1) ∧
        ∀ w : Additive (Section B A),
          (∀ e : E, ρ (QuotientGroup.mk' (pCore 2 (K ⊔ X : Subgroup G))
            (inclusion (show E ≤ K ⊔ X from inf_le_left.trans le_sup_right) e)) w = w) →
          ∃ a : A.val, ((a : J) : G) ∈ U ⊓ centralizer (E : Set G) ∧
            QuotientGroup.mk' (B.val.subgroupOf A.val) a = w.toMul := by
  intro E U J
  obtain ⟨hU,B,A,hZB,hBA,hAU,he,ρ,hirr,hfaith,hρ,hker,hkρ⟩ :=
    linear_point_chief_faithful_representation D S m f hd hfix hX hK hLK hk hp hcard hmove
  let _ := he
  refine ⟨hU,B,A,hZB,hBA,hAU,he,ρ,hirr,hfaith,hρ,hker,hkρ,?_⟩
  intro w hw
  apply linear_point_section_fixed_lift D S m f hcard B A hBA.le hAU w.toMul
  intro e
  have hh := congrArg
    (fun τ : Representation (ZMod 2) (K ⊔ X : Subgroup G) (Additive (Section B A)) =>
      (τ (inclusion (show E ≤ K ⊔ X from inf_le_left.trans le_sup_right) e) w).toMul) hρ
  exact hh.symm.trans (congrArg Additive.toMul (hw e))


/-- On a section with the established two-core kernel, the original cubic
fixed group is moved by the original X_K. -/
theorem linear_point_faithful_section_cubic_movement
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤ centralizer (f.Vi 0 : Set G)) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let J := (K ⊔ X) ⊔ U
    ∀ B A : NormalNode J, ∀ he : IsElementaryAbelian 2 (Section B A),
    let _ := he
    ((binarySectionRepresentation B A).comp
      (inclusion (show K ⊔ X ≤ J from le_sup_left))).ker = pCore 2 (K ⊔ X : Subgroup G) →
    ∃ w : Section B A,
      (∀ e : E, sectionAction B A
        (inclusion (show E ≤ J from inf_le_left.trans (le_sup_right.trans le_sup_left)) e) w = w) ∧
      ∃ z : (X ⊓ K : Subgroup G), sectionAction B A
        (inclusion (show X ⊓ K ≤ J from inf_le_left.trans (le_sup_right.trans le_sup_left)) z) w ≠ w := by
  intro E U J B A he _ hker
  let _ := he
  obtain ⟨P,hP,hXP,hPex,hPc,hZ,_⟩ := linear_marked_extraspecial_sylow D S m f hd hX hK hk hp
  let _ := hPex
  have hPJ : P ≤ J := hP.trans le_sup_left
  let σ : P →* MulAut (Section B A) := (sectionAction B A).comp (inclusion hPJ)
  let τ := (binarySectionRepresentation B A).comp
    (inclusion (show K ⊔ X ≤ J from le_sup_left))
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by simpa using hPc)
  have hp3 : IsPGroup 3 (P.subgroupOf (K ⊔ X)) := hP3.comap_subtype
  have hdis : Disjoint (P.subgroupOf (K ⊔ X)) (pCore 2 (K ⊔ X : Subgroup G)) :=
    hp3.disjoint_of_coprime pCore_isPGroup (by decide : Nat.Coprime 3 2)
  have hinj : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff σ).mp
    apply bot_unique
    intro p hp
    have ht : inclusion hP p ∈ τ.ker := by
      change τ (inclusion hP p) = 1
      apply LinearMap.ext
      intro w
      exact congrArg Additive.ofMul (MulEquiv.congr_fun hp w.toMul)
    have hc : inclusion hP p ∈ pCore 2 (K ⊔ X : Subgroup G) := hker ▸ ht
    have hh : inclusion hP p = 1 := hdis.le_bot ⟨p.property,hc⟩
    change p = 1
    apply Subtype.ext
    exact congrArg (fun q : (K ⊔ X : Subgroup G) => (q : G)) hh
  let X' := X.subgroupOf P
  let E' := E.subgroupOf P
  let : IsElementaryAbelian 3 X := by
    let e := (Coordinates.sl3 m).cartanTorusEquiv hX
    have hF : Nat.card S.field.Carrier = 4 := by simpa [hd] using S.field.card_eq
    have hunit : Nat.card S.field.Carrierˣ = 3 := by rw [Nat.card_units,hF]
    refine { toIsMulCommutative := .of_comm fun a b => e.injective (by simp [mul_comm])
             exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    intro x
    apply e.injective
    rw [map_pow,map_one]
    exact Prod.ext (hunit ▸ pow_card_eq_one' (x := (e x).1))
      (hunit ▸ pow_card_eq_one' (x := (e x).2))
  let : IsElementaryAbelian 3 X' := IsElementaryAbelian.subgroupOf hXP
  have hEP : E ≤ P := inf_le_left.trans hXP
  have hXC : Nat.card X' = 9 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hXP).toEquiv,
      (Coordinates.sl3 m).cartan_card hX,hd]
    norm_num
  have hEC : Nat.card E' = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv]
    exact hcard
  have hZX : center P ≤ X' := fun z hz => (hZ.le (mem_map_of_mem P.subtype hz)).1
  have hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,
      ⟨SL3.flagLocalCoreEquiv S m f 0⟩⟩
  have hKC := subspace_containing_component_centralizes D S f (f.Vi 0)
    le_rfl hm hfix hK.1 hLK
  have hEZ : E' ≠ center P := by
    intro heq
    have heq' : E = X ⊓ K := by
      have hh := congrArg (map P.subtype) heq
      simpa only [E',map_subgroupOf_eq_of_le hEP,hZ] using hh
    exact hmove (heq'.le.trans (inf_le_right.trans hKC))
  obtain ⟨w,hw,z,hz⟩ := IsExtraspecial.exists_moved_cubic_fixed_of_faithful σ hinj
    (IsElementaryAbelian.isPGroup 2 (Section B A)) X' E' hXC hEC
    (fun e he => he.1) hZX hEZ
  refine ⟨w,?_,⟨⟨z,hZ.le (mem_map_of_mem P.subtype z.property)⟩,hz⟩⟩
  intro e
  exact hw ⟨⟨e,hEP e.property⟩,e.property⟩


/-- The original section can be chosen so that a vector of C_U(X₁) has
nonzero X_K-displacement on this same faithful irreducible chief section.
The literal quotient and a surviving original commutator are both retained. -/
theorem linear_point_chief_with_surviving_cubic_commutator
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤ centralizer (f.Vi 0 : Set G)) :
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
        ∃ a : A.val, ((a : J) : G) ∈ U ⊓ centralizer (E : Set G) ∧
          ∃ z : (X ⊓ K : Subgroup G),
            ⁅inclusion (show X ⊓ K ≤ J from
              inf_le_left.trans (le_sup_right.trans le_sup_left)) z,(a : J)⁆ ∉ B.val := by
  intro E U J
  obtain ⟨hU,B,A,hZB,hBA,hAU,he,ρ,hirr,hfaith,hρ,hker,_⟩ :=
    linear_point_chief_faithful_representation D S m f hd hfix hX hK hLK hk hp hcard hmove
  let _ := he
  obtain ⟨w,hw,z,hz⟩ := linear_point_faithful_section_cubic_movement D S m f hd hfix hX
    hK hLK hk hp hcard hmove B A he hker
  obtain ⟨a,ha,haeq⟩ := linear_point_section_fixed_lift D S m f hcard B A hBA.le hAU w hw
  refine ⟨hU,B,A,hZB,hBA,hAU,he,ρ,hirr,hfaith,hρ,a,ha,z,?_⟩
  intro hcomm
  apply hz
  rw [←haeq,sectionAction_mk]
  apply QuotientGroup.eq_iff_div_mem.mpr
  let j : J := inclusion (show X ⊓ K ≤ J from
    inf_le_left.trans (le_sup_right.trans le_sup_left)) z
  change j * (a : J) * j⁻¹ / (a : J) ∈ B.val
  simpa only [commutatorElement_def,div_eq_mul_inv] using hcomm

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
