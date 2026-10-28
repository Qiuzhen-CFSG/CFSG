module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.MathieuTwentyTwo
public import Theory.Representation.BinaryOffender.TwoSectionBudget
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.SubrepresentationLattice
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer

/-!
# Recognition of a whole triple-Mathieu module

The central cubic's polynomial makes every nonzero invariant section faithful.
The native no-FF theorem applies first to an irreducible submodule, and hence
to every nonzero section. Two such sections would each displace more than the
same elementary actor's rank, contradicting its ratio-two bound. The whole
module is therefore irreducible. The proved source degree bound and James
uniqueness identify it with the concrete twelve-dimensional module.

This is the triple-cover specialization of F.9.18(7) and B.4.2/B.4.5 used
in Aschbacher–Smith 14.7.36, printed p.1059; refs/quasithin.pdf. The original
local application is in SourceConstruction.LocalReduction.TripleMathieuModule.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification.Sporadic
open ComponentRecognition.KnownFFTypes.Sporadic
universe u v
section Abstract
variable {D : Type u} [Group D] [Finite D]
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

private theorem triple_polynomial_faithful [Nontrivial W]
    (e : D ≃* Sporadic.Mathieu.M22TripleCover)
    (σ : Representation (ZMod 2) D W)
    (hp : σ (e.symm Sporadic.Mathieu.M22TripleCover.scalar) ^ 2 +
      σ (e.symm Sporadic.Mathieu.M22TripleCover.scalar) + 1 = 0) :
    Function.Injective σ := by
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv e.symm
  let z := e.symm Sporadic.Mathieu.M22TripleCover.scalar
  have hn : z ∉ σ.ker := by
    intro hz
    have he : σ z = 1 := hz
    rw [show σ (e.symm Sporadic.Mathieu.M22TripleCover.scalar) = 1 from he] at hp
    have hzero (v : W) : v = 0 := by
      have hh := LinearMap.congr_fun hp v
      have htwo : v + v = 0 := by
        simpa only [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul, one_smul]
          using (add_smul (1 : ZMod 2) 1 v).symm
      simpa only [one_pow, LinearMap.add_apply, Module.End.one_apply,
        LinearMap.zero_apply, htwo, zero_add] using hh
    exact not_subsingleton W ⟨fun x y => (hzero x).trans (hzero y).symm⟩
  have hk : σ.ker ≤ center D :=
    (IsQuasisimple.normal_le_center_or_eq_top σ.ker).resolve_right
      (fun ht => hn (ht.symm ▸ mem_top z))
  have hc : Nat.card (center D) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans Sporadic.Mathieu.M22TripleCover.center_card
  have hd : Nat.card σ.ker ∣ 3 := hc ▸ card_dvd_of_le hk
  apply (MonoidHom.ker_eq_bot_iff σ).mp
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with hb | hb
  · exact (eq_bot_iff_card _).mpr hb
  · have he : σ.ker = center D := eq_of_le_of_card_ge hk (by omega)
    exact (hn (he.symm ▸ Sporadic.Mathieu.M22TripleCover.scalar_mem_center_of_equiv e)).elim

omit [Finite D] in
private theorem triple_source_hypotheses [Finite W]
    (e : D ≃* Sporadic.Mathieu.M22TripleCover)
    (hD : IsSQTK KnownSimple.IsKnownSimple D)
    (σ : Representation (ZMod 2) D W) [IsIrreducible σ]
    (hf : Function.Injective σ) (hc : cubicRatio σ ≤ 2) :
    M22Source.SourceHypotheses σ ⊤ := by
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv e.symm
  let : IsQuasisimple (⊤ : Subgroup D) := IsQuasisimple.of_mulEquiv topEquiv.symm
  refine ⟨hD,generalizedFitting_eq_top_of_quasisimple.symm,inferInstance,hf,?_,hc,?_⟩
  · exact (irreducible_comp_surjective_iff _ topEquiv.surjective σ).mpr inferInstance
  · let c : (⊤ : Subgroup D) ≃* Sporadic.Mathieu.M22TripleCover := topEquiv.trans e
    have hm : (center (⊤ : Subgroup D)).map c.toMonoidHom =
        center Sporadic.Mathieu.M22TripleCover := by
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact (centerCongr c ⟨x,hx⟩).property
      · intro hy
        exact ⟨c.symm y,(centerCongr c.symm ⟨y,hy⟩).property,c.apply_symm_apply y⟩
    let f : ((⊤ : Subgroup D) ⧸ center (⊤ : Subgroup D)) ≃*
        (Sporadic.Mathieu.M22TripleCover ⧸ center Sporadic.Mathieu.M22TripleCover) :=
      QuotientGroup.congr (center (⊤ : Subgroup D))
        (center Sporadic.Mathieu.M22TripleCover) c hm
    exact ⟨f.trans Sporadic.Mathieu.M22TripleCover.centralQuotientEquiv⟩

private theorem triple_irreducible_not_ff [Finite W]
    (e : D ≃* Sporadic.Mathieu.M22TripleCover)
    (hD : IsSQTK KnownSimple.IsKnownSimple D)
    (σ : Representation (ZMod 2) D W) [IsIrreducible σ]
    (hf : Function.Injective σ) : ¬ IsFFModule σ := by
  let : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  intro hff
  have hc : cubicRatio σ ≤ 2 :=
    ((isFFModule_iff_cubicRatio_le_one σ).mp hff).trans (by norm_num)
  have hs := triple_source_hypotheses e hD σ hf hc
  exact ChapterK.SporadicCatalogue.SourceFF.not_ff_m22
    ⟨hs.sqtk,hs.component.symm,hs.quasisimple,hs.faithful,hs.irreducible,hs.cubic⟩
    hs.quotient hff

private theorem triple_polynomial_not_ff [Finite W] [Nontrivial W]
    (e : D ≃* Sporadic.Mathieu.M22TripleCover)
    (hD : IsSQTK KnownSimple.IsKnownSimple D)
    (σ : Representation (ZMod 2) D W)
    (hp : σ (e.symm Sporadic.Mathieu.M22TripleCover.scalar) ^ 2 +
      σ (e.symm Sporadic.Mathieu.M22TripleCover.scalar) + 1 = 0) :
    ¬ IsFFModule σ := by
  let : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  obtain ⟨U,hU,_⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation σ)).resolve_left top_ne_bot
  let hi := (Subrepresentation.irreducible_iff_isAtom U).mpr hU
  let := Subrepresentation.irreducible_module_nontrivial U.toRepresentation
  have hpU : U.toRepresentation (e.symm Sporadic.Mathieu.M22TripleCover.scalar) ^ 2 +
      U.toRepresentation (e.symm Sporadic.Mathieu.M22TripleCover.scalar) + 1 = 0 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun hp v
  intro hff
  obtain ⟨A,hA,hb⟩ := hff
  exact triple_irreducible_not_ff e hD U.toRepresentation
    (triple_polynomial_faithful e U.toRepresentation hpU)
    ⟨A,hA,(fixedCodim_subrepresentation_le σ U A).trans hb⟩

private theorem triple_polynomial_irreducible [Finite W] [Nontrivial W]
    (e : D ≃* Sporadic.Mathieu.M22TripleCover)
    (hD : IsSQTK KnownSimple.IsKnownSimple D)
    (σ : Representation (ZMod 2) D W)
    (hp : σ (e.symm Sporadic.Mathieu.M22TripleCover.scalar) ^ 2 +
      σ (e.symm Sporadic.Mathieu.M22TripleCover.scalar) + 1 = 0)
    (A : Subgroup D) (hA : IsElementaryTwo A)
    (hb : fixedCodim σ A ≤ 2 * rank A) : IsIrreducible σ := by
  let : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  obtain ⟨U,hU,_⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation σ)).resolve_left top_ne_bot
  let hi := (Subrepresentation.irreducible_iff_isAtom U).mpr hU
  let := Subrepresentation.irreducible_module_nontrivial U.toRepresentation
  have hpU : U.toRepresentation (e.symm Sporadic.Mathieu.M22TripleCover.scalar) ^ 2 +
      U.toRepresentation (e.symm Sporadic.Mathieu.M22TripleCover.scalar) + 1 = 0 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun hp v
  have htop : U = ⊤ := by
    by_contra hn
    let : Finite (W ⧸ U.toSubmodule) := Finite.of_surjective _ U.toSubmodule.mkQ_surjective
    let : Nontrivial (W ⧸ U.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr
      (fun he => hn (Subrepresentation.toSubmodule_injective he))
    have hpQ : U.quotientRepresentation (e.symm Sporadic.Mathieu.M22TripleCover.scalar) ^ 2 +
        U.quotientRepresentation (e.symm Sporadic.Mathieu.M22TripleCover.scalar) + 1 = 0 := by
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := U.toSubmodule.mkQ_surjective v
      simpa only [pow_two, Module.End.mul_apply, LinearMap.add_apply,
        Module.End.one_apply, LinearMap.zero_apply, map_add, map_zero,
        Subrepresentation.quotientRepresentation_mk] using
        congrArg U.toSubmodule.mkQ (LinearMap.congr_fun hp w)
    have h₁ : rank A < fixedCodim U.toRepresentation A := lt_of_not_ge
      (fun hh => triple_polynomial_not_ff e hD U.toRepresentation hpU ⟨A,hA,hh⟩)
    have h₂ : rank A < fixedCodim U.quotientRepresentation A := lt_of_not_ge
      (fun hh => triple_polynomial_not_ff e hD U.quotientRepresentation hpQ ⟨A,hA,hh⟩)
    have hh := fixedCodim_quotient_add_subrepresentation_le σ U A
    omega
  subst U
  let E : (⊤ : Subrepresentation σ).toRepresentation ≃ₗ σ :=
    { Submodule.topEquiv with isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }
  exact E.irreducible_euqiv.mp hi

/-- A fixed-free central cubic and a quadratic actor of ratio at most two
identify the entire binary module, without assuming irreducibility or degree. -/
theorem triple_polynomial_recognition [Finite W] [Nontrivial W]
    (e : D ≃* Sporadic.Mathieu.M22TripleCover)
    (hD : IsSQTK KnownSimple.IsKnownSimple D)
    (σ : Representation (ZMod 2) D W)
    (hp : σ (e.symm Sporadic.Mathieu.M22TripleCover.scalar) ^ 2 +
      σ (e.symm Sporadic.Mathieu.M22TripleCover.scalar) + 1 = 0)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hq : IsQuadratic σ A)
    (hb : fixedCodim σ A ≤ 2 * rank A) :
    IsIrreducible σ ∧ Module.finrank (ZMod 2) W = 12 ∧
      Nonempty (Representation.Equiv σ
        (Sporadic.Mathieu.M22TripleCover.representationOfEquiv e)) := by
  let : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  let hi := triple_polynomial_irreducible e hD σ hp A hA hb
  have hf := triple_polynomial_faithful e σ hp
  have hc : cubicRatio σ ≤ 2 := cubicRatio_le_quadraticRatio σ |>.trans
    ((quadraticRatio_le_two_iff σ).mpr ⟨A,hA,hq,hb⟩)
  have hs := triple_source_hypotheses e hD σ hf hc
  have hd : Module.finrank (ZMod 2) W = 12 := Nat.le_antisymm
    (M22Source.source_finrank_le_twelve σ ⊤ hs)
    (Sporadic.Mathieu.M22TripleCover.faithful_irreducible_finrank_ge_twelve_of_equiv e σ hf)
  exact ⟨hi,hd,Sporadic.Mathieu.M22TripleCover.equiv_representationOfEquiv_of_finrank_twelve
    e σ hf hd⟩

end Abstract
end CFSG.Quasithin.ChapterB.SmallRatioClassification.Sporadic
