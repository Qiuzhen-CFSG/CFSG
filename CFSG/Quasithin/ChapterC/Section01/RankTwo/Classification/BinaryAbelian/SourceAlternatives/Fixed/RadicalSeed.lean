module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.SourceAlternatives.Fixed.Omega
/-!
# A radical-fixed vector outside the central line

MS3 prevents Ω₁Z(R) from centralizing the component. Split its elements
inside Ω₁Z(O₂(J)) using the four-dimensional cover's vanishing first
cohomology. For an element not centralizing L, its core component lies
outside C_D(L). Each element of R acts on D as an element of R∩L, because
the ambient action has kernel O₂(J)≤R; hence that core component is fixed
by R. This is an actual fixed vector in the nonsplit cover, stronger than
a fixed point in its natural quotient.

Source: Aschbacher–Smith C.1.31(MS3), C.1.34(5), printed pp.135–137;
Meierfrankenfeld–Stellmacher (1993), Main Theorem (8), printed p.830.
-/

public section

open Subgroup Representation Representation.OneCohomology Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R) [IsElementaryAbelian 2 (commutatorCore L)]
namespace AbelianCore.NaturalQuotient
variable (q : NaturalQuotient h 1)

omit [IsElementaryAbelian 2 (commutatorCore L)] in
include h in
private theorem radicalOmega_not_le_fixed :
    ¬ omegaOneCenterAmbient R ≤ centralizer (L : Set J) := by
  intro hfix
  let C : Subgroup R := (omega₁ (center R) (p := 2)).map (center R).subtype
  let : (omega₁ (center R) (p := 2)).Characteristic := omega₁_characteristic _
  let : C.Characteristic := inferInstance
  let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr h.radical_ne_bot
  have hne : C ≠ ⊥ := omega_center_ne_bot h.radical.isPGroup
  have hc : C.map R.subtype ≤ center J := by
    intro z hz
    have hzR : z ∈ omegaOneCenterAmbient R := hz
    have hzfix := (mem_omegaOneCenterAmbient_iff R z).mp hzR |>.2.2
    apply mem_center_iff.mpr
    intro j
    obtain ⟨l,hl,r,hr,rfl⟩ := h.product j
    calc
      l*r*z = l*(r*z) := mul_assoc _ _ _
      _ = l*(z*r) := by rw [hzfix r hr]
      _ = (l*z)*r := (mul_assoc _ _ _).symm
      _ = (z*l)*r := by rw [hfix hzR l hl]
      _ = z*(l*r) := mul_assoc _ _ _
  apply h.characteristic C inferInstance hne
  constructor
  intro z hz j
  rw [mem_center_iff.mp (hc hz) j,mul_inv_cancel_right]
  exact hz

include h q in
/-- MS3 supplies an R-fixed vector in the actual four-dimensional cover outside
its fixed line. The quotient alone would not distinguish the two parabolics. -/
theorem exists_radical_fixed_core (hd : Nat.card (commutatorCore L) = 16) :
    ∃ d : commutatorCore L, d ∉ coreFixed L ∧
      ∀ r ∈ R, h.coreAmbientConjugation r d = d := by
  let := h.component_normal
  obtain ⟨z,hz,hzne⟩ := SetLike.not_le_iff_exists.mp (radicalOmega_not_le_fixed h)
  have hzM := h.radicalOmega_le_centralModule hz
  rw [q.centralModule_split h hd] at hzM
  obtain ⟨d,hdD,c,hc,he⟩ := mem_sup_of_normal_left.mp hzM
  refine ⟨⟨d,hdD⟩,?_,?_⟩
  · intro hdC
    apply hzne
    rw [← he]
    exact (centralizer (L : Set J)).mul_mem hdC hc.2
  · intro r hr
    obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L)
      (q.quotientEquiv.symm (q.ambientActor h r))
    have hal : q.ambientActor h l = q.ambientActor h r := by
      rw [q.ambientActor_component,hl,MulEquiv.apply_symm_apply]
    have hn : r * (l : J)⁻¹ ∈ pCore 2 J := by
      rw [← q.ambientActor_kernel]
      change q.ambientActor h (r * (l : J)⁻¹) = 1
      rw [map_mul,map_inv,hal,mul_inv_cancel]
    have hlR : (l : J) ∈ R := by
      have hh := R.mul_mem (R.inv_mem (h.radical.twoCore_le hn)) hr
      simpa only [mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one] using hh
    have hzl := (mem_omegaOneCenterAmbient_iff R z).mp hz |>.2.2 l hlR
    have hcl : (l : J) * c = c * (l : J) := hc.2 l l.property
    have hdl : (l : J) * d = d * (l : J) := by
      rw [← he] at hzl
      apply mul_right_cancel (b := c)
      calc
        (l : J) * d * c = (l : J) * (d*c) := mul_assoc _ _ _
        _ = (d*c) * (l : J) := hzl
        _ = d * ((l : J) * c) := by rw [hcl]; group
        _ = (d * (l : J)) * c := (mul_assoc _ _ _).symm
    have hact : h.coreAmbientConjugation r = h.coreAmbientConjugation l := by
      rw [← q.ambientActor_action,← q.ambientActor_action,hal]
    rw [hact]
    apply Subtype.ext
    rw [h.coreAmbientConjugation_apply,hdl,mul_inv_cancel_right]

end AbelianCore.NaturalQuotient
end CFSG.Quasithin.ChapterC.BinaryMS
