module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFamily.Colors.Basic

/-!
# Canonical transport of the original colored parabolics

Conjugation by an element normalizing ⟨z,u⟩ carries the family on v to
the family on its conjugate. The inverse is conjugation by the inverse
actor, and the induced action on the full three-color union has exactly
the original ambient conjugation maps. Source: J.4.7, printed p.443.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
open Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (p : Plane d) (B5 : Sylow 5 d.toTypeRuSetup.H) (z u : G)

/-- The original ambient conjugation transports both the color and the pair containment. -/
theorem color_conjugate_mem (n : G) (hn : n ∈ normalizer (pairSpan z u : Set G))
    {v : G} {E : Subgroup G} (hE : E ∈ colorFamily p B5 z u v) :
    E.conjBy n ∈ colorFamily p B5 z u (n*v*n⁻¹) := by
  obtain ⟨g,rfl,hg,hV⟩ := hE
  refine ⟨n*g,conjBy_conjBy _ _ _,?_,?_⟩
  · have hh := congrArg (MulAut.conj n) hg
    simpa only [MulAut.conj_apply,mul_inv_rev,mul_assoc] using hh
  · have hh := map_mono (f := (MulAut.conj n).toMonoidHom) hV
    have he : (pairSpan z u).map (MulAut.conj n).toMonoidHom=pairSpan z u :=
      mem_normalizer_iff_map_conj_eq.mp hn
    rw [he] at hh
    exact hh

/-- The actual conjugation equivalence between two color families. -/
def colorConjugationEquiv (n : G) (hn : n ∈ normalizer (pairSpan z u : Set G)) (v : G) :
    colorFamily p B5 z u v ≃ colorFamily p B5 z u (n*v*n⁻¹) where
  toFun E := ⟨E.val.conjBy n,color_conjugate_mem p B5 z u n hn E.property⟩
  invFun E := ⟨E.val.conjBy n⁻¹,by
    have hh := color_conjugate_mem p B5 z u n⁻¹ ((normalizer (pairSpan z u : Set G)).inv_mem hn) E.property
    simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hh⟩
  left_inv E := Subtype.ext (conjBy_inv E.val n)
  right_inv E := Subtype.ext (conjBy_inv' E.val n)

theorem colorConjugationEquiv_apply (n : G) (hn : n ∈ normalizer (pairSpan z u : Set G))
    (v : G) (E : colorFamily p B5 z u v) :
    (colorConjugationEquiv p B5 z u n hn v E : Subgroup G)=E.val.conjBy n := rfl

variable (c : Choices d) (e : first ≃* p.F₁ B5) (hz : (e modelZ : G)=c.z)
include hz

/-- Every normalizer actor permutes the literal three involution labels. -/
theorem conjugate_mem_colors (n : G)
    (hn : n ∈ normalizer (pairSpan c.z (sourceU e) : Set G)) {v : G}
    (hv : v ∈ colors c.z (sourceU e)) : n*v*n⁻¹ ∈ colors c.z (sourceU e) := by
  obtain ⟨hV,hv1⟩ := (colors_iff p B5 c e hz v).mp hv
  apply (colors_iff p B5 c e hz _).mpr
  refine ⟨(mem_normalizer_iff.mp hn v).mp hV,?_⟩
  intro hh
  exact hv1 ((MulAut.conj n).injective (hh.trans (MulAut.conj n).map_one.symm))

/-- The union of all three actual colored families is preserved by its pair normalizer. -/
theorem global_conjugate_mem (n : G)
    (hn : n ∈ normalizer (pairSpan c.z (sourceU e) : Set G)) {E : Subgroup G}
    (hE : E ∈ globalFamily p B5 c.z (sourceU e)) :
    E.conjBy n ∈ globalFamily p B5 c.z (sourceU e) := by
  obtain ⟨v,hv,hEv⟩ := hE
  exact ⟨n*v*n⁻¹,conjugate_mem_colors p B5 c e hz n hn hv,
    color_conjugate_mem p B5 c.z (sourceU e) n hn hEv⟩

/-- The canonical action is the literal original conjugation action. -/
@[instance_reducible] def normalizerAction : MulAction (normalizer (pairSpan c.z (sourceU e) : Set G))
    (globalFamily p B5 c.z (sourceU e)) where
  smul n E := ⟨E.val.conjBy (n : G),global_conjugate_mem p B5 c e hz n n.property E.property⟩
  one_smul E := Subtype.ext (conjBy_one E.val)
  mul_smul n m E := Subtype.ext (conjBy_mul E.val (n : G) (m : G))

theorem normalizerAction_apply (n : normalizer (pairSpan c.z (sourceU e) : Set G))
    (E : globalFamily p B5 c.z (sourceU e)) :
    (((normalizerAction p B5 c e hz).smul n E) : Subgroup G)=E.val.conjBy (n : G) := rfl

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
