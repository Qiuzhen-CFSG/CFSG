module
public import CFSG.Quasithin.ChapterD.Section02.StarredConjugacy
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowOffenderTransport
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowOffenderGeometry
public import Theory.Representation.NormalConstituentDisplacement

/-!
# Exhaustion by a stable non-FF constituent

An irreducible constituent of a normal subgroup exhausts an irreducible
ambient module when every minimum cubic actor preserves it and acts
faithfully on it, and its stabilizer image is non-FF. Conjugation transfers
these properties to every translate. Two distinct translates are disjoint,
so the same actor's fixed-codimension budget forces an FF offender on one,
contradicting transport to the original constituent.

Only pairwise disjointness is used. The Chapter10 quiet rank-one application
constructs stability and faithfulness for its unchanged seed and full action.
Source: Aschbacher--Smith D.3.21 and 3.2.6, pp.205--207,581,
with the common-actor budget from D.2.9, pp.180--182, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD
open Chapter3.Section02

/-- Stable faithful minimum cubic actors force a non-FF irreducible
constituent to fill the whole irreducible ambient module. -/
theorem stable_nonFF_constituent_eq_top
    {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (hirr : ρ.IsIrreducible)
    (X : Subgroup H) [X.Normal] (I : Subrepresentation (ρ.comp X.subtype))
    (hI : I.toRepresentation.IsIrreducible) (hb : cubicRatio ρ ≤ 2)
    (hnff : ¬ IsFFModule (subspaceImageRepresentation ρ I.toSubmodule))
    (hs : ∀ A ∈ QhatStar ρ, A ≤ subspaceStabilizer ρ I.toSubmodule)
    (hk : ∀ A ∈ QhatStar ρ, subspaceKernel ρ I.toSubmodule A = ⊥) :
    I.toSubmodule = ⊤ := by
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr hb
  have hbound := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp
    (hA.1.2.2.2.le.trans hA.1.1)
  have hstable (t : H) : I.toSubmodule.map (ρ t) = I.toSubmodule := by
    let B := A.map (MulAut.conj t⁻¹).toMonoidHom
    have hB : B ∈ QhatStar ρ := QhatStar.map_conj ρ hA t⁻¹
    have hBI := hs B hB
    have hkerB := hk B hB
    have hAI : A ≤ subspaceStabilizer ρ (I.toSubmodule.map (ρ t)) := by
      apply le_subspaceStabilizer
      intro a ha v hv
      obtain ⟨w,hw,rfl⟩ := hv
      have hba : t⁻¹*a*t ∈ B := by
        change t⁻¹*a*t ∈ A.map (MulAut.conj t⁻¹).toMonoidHom
        exact ⟨a,ha,by simp⟩
      have hh := (hBI hba w).2 hw
      refine ⟨ρ (t⁻¹*a*t) w,hh,?_⟩
      simp only [←Module.End.mul_apply,←map_mul]
      congr 2
      group
    have hker : subspaceKernel ρ (I.toSubmodule.map (ρ t)) A = ⊥ := by
      apply bot_unique
      rintro a ⟨ha,hfix⟩
      have hba : t⁻¹*a*t ∈ subspaceKernel ρ I.toSubmodule B := by
        refine ⟨?_,?_⟩
        · change t⁻¹*a*t ∈ A.map (MulAut.conj t⁻¹).toMonoidHom
          exact ⟨a,ha,by simp⟩
        · intro w hw
          have he := hfix (ρ t w) (Submodule.mem_map_of_mem hw)
          calc
            ρ (t⁻¹*a*t) w = ρ t⁻¹ (ρ a (ρ t w)) := by simp only [map_mul,Module.End.mul_apply]
            _ = w := by rw [he,←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
      have he := mem_bot.mp (hkerB.le hba)
      exact mem_bot.mpr (calc
        a = t*(t⁻¹*a*t)*t⁻¹ := by group
        _ = 1 := by rw [he]; group)
    by_contra hne
    let J := conjugateSubrepresentationOrderIso ρ X t I
    have hi : IsAtom I := (Subrepresentation.irreducible_iff_isAtom I).mp hI
    have hj : IsAtom J := ((conjugateSubrepresentationOrderIso ρ X t).isAtom_iff I).mpr hi
    have hd : Disjoint I.toSubmodule (I.toSubmodule.map (ρ t)) := by
      have hh : I ≠ J := by
        intro he
        apply hne
        exact (conjugateSubrepresentationOrderIso_toSubmodule ρ X t I).symm.trans
          (congrArg Subrepresentation.toSubmodule he.symm)
      have hh' := congrArg Subrepresentation.toSubmodule (hi.disjoint_of_ne hj hh).eq_bot
      change I.toSubmodule ⊓ J.toSubmodule = ⊥ at hh'
      rw [show J.toSubmodule = I.toSubmodule.map (ρ t) from
        conjugateSubrepresentationOrderIso_toSubmodule ρ X t I] at hh'
      exact disjoint_iff.mpr hh'
    rcases ChosenSource325.common_actor_offends_one_of_pair ρ I.toSubmodule
      (I.toSubmodule.map (ρ t)) hA.1.2.1 (hs A hA) hAI hd (hk A hA) hker hbound
      with hoff | hoff
    · exact hnff ⟨_,hoff⟩
    · exact hnff (ChosenSource325.isFFModule_of_conjugate_image ρ I.toSubmodule t ⟨_,hoff⟩)
  let J : Subrepresentation ρ := {
    toSubmodule := I.toSubmodule
    apply_mem_toSubmodule g v hv := by
      rw [←hstable g]
      exact Submodule.mem_map_of_mem hv }
  have hne : J ≠ ⊥ := by
    intro he
    apply (Subrepresentation.irreducible_iff_isAtom I).mp hI |>.ne_bot
    apply Subrepresentation.toSubmodule_injective
    exact (congrArg Subrepresentation.toSubmodule he : J.toSubmodule = (⊥ : Subrepresentation ρ).toSubmodule)
  exact congrArg Subrepresentation.toSubmodule ((hirr.eq_bot_or_eq_top J).resolve_left hne)

end CFSG.Quasithin.ChapterD
