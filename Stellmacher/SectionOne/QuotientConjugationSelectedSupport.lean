module
public import Stellmacher.SectionOne.OneSevenConjugateDerivedSupport
public import Theory.GroupAction.SubgroupQuotientSupportLift

/-!
# Detecting a selected factor support in a literal conjugation quotient

For a supplied conjugation action of P on U/Z, let W≤U be normalized by
F. Suppose that the image of R is the closure of conjugates of a selected
factor's derived subgroup under B, with the factor and B contained in the
image of F. Nontrivial [W,R] modulo Z then forces the factor support into
the image of W in U/Z. The exact normality and elementary-module instances
are retained throughout.

The formula for conjugation transports F-invariance to the quotient image.
If the residual image fixed that image pointwise, the same formula and the
quotient equality criterion would place every ambient commutator in Z.
The nontrivial conjugate-derived-action theorem then fills the selected
four-element support inside the quotient image of W.

This is the literal quotient transfer for V₁≤V_a in the noncentral case of
Stellmacher (9.4), printed p.51/PDF p.41 of
`refs/files/stellmacher-n-group.pdf`. All source geometry and residual
identification remain inputs supplied by the Section Nine producers.
-/

open scoped commutatorElement
namespace Stellmacher.SectionOne
universe u

public theorem quotient_conjugation_selected_support_le
    {G : Type u} [Group G] [Finite G]
    (P U Z F R W : Subgroup G)
    (hRP : R ≤ P) (hWU : W ≤ U)
    (hPU : P ≤ Subgroup.normalizer U)
    (hFW : F ≤ Subgroup.normalizer W)
    (hN : (Z.subgroupOf U).Normal)
    (hW : let _ := hN; IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U))
    (action : let _ := hN; P →* MulAut (U ⧸ Z.subgroupOf U))
    (hact : let _ := hN; ∀ mover : P, ∀ point : U,
      action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
        QuotientGroup.mk' (Z.subgroupOf U)
          ⟨(mover:G)*(point:G)*(mover:G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hPU mover.property) point).mp point.property⟩)
    (D B : Subgroup action.range)
    (hD : let _ := hN; let _ := hW; IsOneSevenFactor (V := U ⧸ Z.subgroupOf U) D)
    (hDF : D ≤ (F.subgroupOf P).map action.rangeRestrict)
    (hBF : B ≤ (F.subgroupOf P).map action.rangeRestrict)
    (hclosure : (R.subgroupOf P).map action.rangeRestrict =
      conjugateClosure ((commutator D).map D.subtype) B)
    (hactive : ¬ ⁅W,R⁆ ≤ Z) :
    let _ := hN
    commutatorAction D (U ⧸ Z.subgroupOf U) ≤
      (W.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
  let _ := hN
  let _ := hW
  let V := U ⧸ Z.subgroupOf U
  let q : U →* V := QuotientGroup.mk' (Z.subgroupOf U)
  let M : Subgroup V := (W.subgroupOf U).map q
  have hstable : ∀ d ∈ (F.subgroupOf P).map action.rangeRestrict,
      ∀ v ∈ M, d • v ∈ M := by
    rintro d ⟨f,hf,rfl⟩ v ⟨w,hw,rfl⟩
    let moved : U := ⟨(f:G)*(w:G)*(f:G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hPU f.property) w).mp w.property⟩
    have hmoved : moved ∈ W.subgroupOf U :=
      (Subgroup.mem_normalizer_iff.mp (hFW hf) w).mp hw
    refine ⟨moved,hmoved,?_⟩
    change q moved = (action f) (q w)
    exact (hact f w).symm
  apply oneSevenFactor_support_le_of_conjugate_derived_action D B hD M
    (fun d hd => hstable d (hDF hd)) (fun d hd => hstable d (hBF hd))
  intro hfix
  apply hactive
  apply Subgroup.commutator_le.mpr
  intro w hw r hr
  let rP : P := ⟨r,hRP hr⟩
  let wU : U := ⟨w,hWU hw⟩
  have hrimage : action.rangeRestrict rP ∈ conjugateClosure ((commutator D).map D.subtype) B := by
    rw [← hclosure]
    exact Subgroup.mem_map_of_mem action.rangeRestrict hr
  have hwm : q wU ∈ M := Subgroup.mem_map_of_mem q hw
  have heq := (mem_fixingSubgroup_iff action.range).mp (hfix hrimage) (q wU) hwm
  change action rP (q wU) = q wU at heq
  rw [hact rP wU] at heq
  have hdiv := QuotientGroup.eq_iff_div_mem.mp heq
  have hcomm : ⁅r,w⁆ ∈ Z := by
    change r*w*r⁻¹/w ∈ Z at hdiv
    simpa only [div_eq_mul_inv,commutatorElement_def] using hdiv
  rw [← commutatorElement_inv]
  exact Z.inv_mem hcomm

end Stellmacher.SectionOne
