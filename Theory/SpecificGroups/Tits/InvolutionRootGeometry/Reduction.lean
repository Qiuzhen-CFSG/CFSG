module

public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.Geometry
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.BinaryAutomorphisms.DerivedAction

/-!
# Reduction of the Tits automorphism table to concrete binary Ree calculations

Bijectivity of the full group's derived action turns an involutory automorphism
into an actual involution of the binary Ree group. An involution enumeration
inside that group can then prove both innerness and the two root alternatives.
The root centralizer calculations for the two representatives transport by
conjugation, giving proper parabolic containment and equality of embedded O².

The full binary involution coverage and the two representative parabolic
calculations are explicit premises here, not claimed source results.
Source: Aschbacher–Smith 16.1.4, printed p.1171.
-/

public section
noncomputable section
namespace Tits.InvolutionRootGeometry
open Subgroup ReeF4 ReeF4.Parabolics.OuterLocal

/-- The concrete finite-group calculation needed from the full binary Ree
carrier. In particular every involution lies in its derived subgroup. -/
@[expose] def BinaryInvolutionCoverage : Prop :=
  ∀ g : Model 0, g ^ 2 = 1 → g ≠ 1 →
    ∃ x : commutator (Model 0), (x : Model 0) = g ∧
      (IsConj longRoot x ∨ IsConj shortRoot x)

/-- Conjugation by an element of the derived subgroup is intrinsically inner. -/
theorem binaryDerivedAction_coe (x : commutator (Model 0)) :
    binaryDerivedAction (x : Model 0) = MulAut.conj x := by
  ext y
  rfl

/-- A concrete involution table for the full Ree carrier excludes non-inner
involutory automorphisms and supplies the actual root class of every involution. -/
theorem involution_inner_root_of_binary_coverage
    (hbij : Function.Bijective binaryDerivedAction) (hcover : BinaryInvolutionCoverage)
    (a : MulAut ParrottGroup) (ha : a ^ 2 = 1) (hne : a ≠ 1) :
    ∃ x : ParrottGroup, a = MulAut.conj x ∧ (IsLongRoot x ∨ IsShortRoot x) := by
  let e := binaryTitsAutEquiv derivedEquiv.symm hbij
  let g := e.symm a
  have hg : g ^ 2 = 1 := by
    change (e.symm a) ^ 2 = 1
    rw [← map_pow, ha, map_one]
  have hn : g ≠ 1 := by
    intro h
    apply hne
    have he := congrArg e h
    simpa only [g, MulEquiv.apply_symm_apply, map_one] using he
  obtain ⟨x, hx, hc⟩ := hcover g hg hn
  refine ⟨derivedEquiv.symm x, ?_, ?_⟩
  · have he : e g = a := e.apply_symm_apply a
    rw [← he, ← hx]
    change binaryTitsAutEquiv derivedEquiv.symm hbij (x : Model 0) = _
    rw [binaryTitsAutEquiv_apply, binaryDerivedAction_coe, MulAut.congr_conj]
  · simpa only [IsLongRoot, IsShortRoot, MulEquiv.apply_symm_apply] using hc

private theorem map_centralizer (e : ParrottGroup ≃* ParrottGroup) (x : ParrottGroup) :
    (centralizer {x}).map e.toMonoidHom = centralizer {e x} := by
  apply le_antisymm
  · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
      map_centralizer_le_centralizer_image {x} e.toMonoidHom
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change e.symm y ∈ centralizer {x}
    rw [mem_centralizer_singleton_iff]
    apply e.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using
      mem_centralizer_singleton_iff.mp hy

private theorem parabolic_conjugate (P : Subgroup ParrottGroup)
    (hP : IsRootParabolic P) (g : ParrottGroup) :
    IsRootParabolic (P.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨s, k, rfl⟩ := hP
  refine ⟨s, g * k, ?_⟩
  rw [map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

private theorem conjugate_containment {r x : ParrottGroup} (hx : IsConj r x)
    (h : ∃ P : Subgroup ParrottGroup,
      IsRootParabolic P ∧ P < ⊤ ∧ centralizer {r} ≤ P) :
    ∃ P : Subgroup ParrottGroup, IsRootParabolic P ∧ P < ⊤ ∧ centralizer {x} ≤ P := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hx
  obtain ⟨P, hP, hp, hc⟩ := h
  refine ⟨P.map (MulAut.conj g).toMonoidHom, parabolic_conjugate P hP g, ?_, ?_⟩
  · simpa using (MulAut.conj g).mapSubgroup.strictMono hp
  · have hm := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hc
    rw [map_centralizer] at hm
    exact hg ▸ hm

/-- The final table reduction. The three concrete premises concern the full
binary Ree involutions and the two root representatives; none assumes a table
for arbitrary automorphisms. The O² identity is an equality of ambient subgroups. -/
theorem involution_table_of_representatives
    (hbij : Function.Bijective binaryDerivedAction) (hcover : BinaryInvolutionCoverage)
    (hlong : ∃ P : Subgroup ParrottGroup, IsRootParabolic P ∧ P < ⊤ ∧
      centralizer {parrottGenerator .s1} ≤ P)
    (hshort : ∃ P : Subgroup ParrottGroup, IsRootParabolic P ∧ P < ⊤ ∧
      centralizer {parrottGenerator .s4} ≤ P)
    (a : MulAut ParrottGroup) (ha : a ^ 2 = 1) (hne : a ≠ 1) :
    ∃ (x : ParrottGroup) (P : Subgroup ParrottGroup),
      a = MulAut.conj x ∧ (IsLongRoot x ∨ IsShortRoot x) ∧
      IsRootParabolic P ∧ P < ⊤ ∧ a.fixedSubgroup ≤ P ∧
      fixedResidual a = parabolicFixedResidual a P := by
  obtain ⟨x, he, hc⟩ := involution_inner_root_of_binary_coverage hbij hcover a ha hne
  have hp : ∃ P : Subgroup ParrottGroup,
      IsRootParabolic P ∧ P < ⊤ ∧ centralizer {x} ≤ P := by
    rcases hc with hl | hs
    · exact conjugate_containment ((isLongRoot_iff x).mp hl) hlong
    · exact conjugate_containment ((isShortRoot_iff x).mp hs) hshort
  obtain ⟨P, hP, hp, hC⟩ := hp
  have hfix : a.fixedSubgroup ≤ P := by rwa [he, MulAut.fixedSubgroup_conj]
  exact ⟨x, P, he, hc, hP, hp, hfix, fixedResidual_eq_of_le a P hfix⟩

end Tits.InvolutionRootGeometry
