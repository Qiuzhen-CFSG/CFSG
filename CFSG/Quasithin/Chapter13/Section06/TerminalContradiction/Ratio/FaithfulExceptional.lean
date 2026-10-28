module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.SourceStrictBound
import all CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Sections
import all CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Constituents
import all CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.ConstituentGeometry

/-!
# Faithful exceptional actions in the Suzuki centralizer

A faithful binary action whose generalized Fitting subgroup is PSL₃(4),
M₂₃ or J₂ has quadratic ratio greater than two. Choose a faithful irreducible
section and retain its original quadratic actor. The exceptional outer-group
bound and constituent-degree bound force that actor to preserve a faithful
component constituent, where the proved source strict bound applies.

The actual consumer restricts the original U_H/V₁ action to the centralizer
of an extra Suzuki component after proving the same actor centralizes it.
Thus neither quotienting the actor nor assuming faithfulness on one direct
factor is needed. Source: Aschbacher–Smith B.4.2–5 and13.6, printed p.935.

The three `import all` edges deliberately extend the existing ratio
implementation inside this package: only their section and constituent proof
helpers and the body of the existing public restricted representation are
used. No private name occurs in this module's public interface, and those
helpers are neither copied nor exposed as new public API.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSections
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.FaithfulExceptional
open StrictBound
universe u v

/-- A small quadratic actor in a faithful irreducible action stabilizes a
faithful component constituent, under the actual outer-rank and degree bounds. -/
private theorem component_action_of_faithful_irreducible
    {𝒦 : GroupClass} {X : Type u} [Group X] [Finite X]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) X W)
    (hL : IsQuasisimple (generalizedFitting X))
    (hz : center (generalizedFitting X) = ⊥)
    (hsqtk : IsSQTK 𝒦 X)
    (hrank : ∀ B : Subgroup X, IsElementaryTwo B →
      Disjoint B (generalizedFitting X) → rank B ≤ 2)
    (hdegree : ∀ I : Subrepresentation (ρ.comp (generalizedFitting X).subtype),
      Function.Injective I.toRepresentation → IsIrreducible I.toRepresentation →
        4 < Module.finrank (ZMod 2) I.toSubmodule)
    (A : Subgroup X) (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) :
    ∃ I : Subrepresentation (ρ.comp (generalizedFitting X).subtype),
      IsIrreducible I.toRepresentation ∧ Function.Injective I.toRepresentation ∧
      ∃ (D : Subgroup X) (hD : D ≤ subspaceStabilizer ρ I.toSubmodule),
        D = generalizedFitting X ⊔ A ∧
        Function.Injective (restrictedRepresentation ρ D I.toSubmodule hD) ∧
        IsIrreducible (restrictedRepresentation ρ D I.toSubmodule hD) ∧
        B4Hypotheses 𝒦 (restrictedRepresentation ρ D I.toSubmodule hD) ∧
        quadraticRatio (restrictedRepresentation ρ D I.toSubmodule hD) ≤ 2 ∧
        Nonempty (generalizedFitting D ≃* generalizedFitting X) := by
  let L := generalizedFitting X
  have hLn0 : (generalizedFitting X).Normal := by
    infer_instance
  have hLn : L.Normal := hLn0
  let : L.Normal := hLn
  obtain ⟨I, hI, hIfaith⟩ := exists_faithful_component_constituent
    ρ hi hf L hL hz
  have hKI : L ≤ subspaceStabilizer ρ I.toSubmodule := by
    apply le_subspaceStabilizer
    intro l hl v hv
    exact I.apply_mem_toSubmodule ⟨l, hl⟩ hv
  have hIfaith' : Function.Injective
      (invariantSubspace ρ L I.toSubmodule hKI).toRepresentation := by
    have heq : invariantSubspace ρ L I.toSubmodule hKI = I := by
      apply Subrepresentation.toSubmodule_injective
      rfl
    intro x y hxy
    apply hIfaith
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact congrArg Subtype.val (congrArg (fun f => f v) hxy)
  have hstab : A ≤ subspaceStabilizer ρ I.toSubmodule := by
    intro a ha
    apply (subspace_map_eq_iff ρ I.toSubmodule a).mp
    by_contra hne
    let J := conjugateSubrepresentationOrderIso ρ L a I
    have hJsub : J.toSubmodule = I.toSubmodule.map (ρ a) := by
      exact conjugateSubrepresentationOrderIso_toSubmodule ρ L a I
    have hIJ : I ≠ J := by
      intro he
      apply hne
      rw [← hJsub, he]
    have hIatom : IsAtom I := (Subrepresentation.irreducible_iff_isAtom I).mp hI
    have hJatom : IsAtom J :=
      (conjugateSubrepresentationOrderIso ρ L a).isAtom_iff I |>.mpr hIatom
    have hdis : Disjoint I.toSubmodule (I.toSubmodule.map (ρ a)) := by
      rw [← hJsub]
      apply disjoint_iff_inf_le.mpr
      intro v hv
      have hvIJ : v ∈ I ⊓ J := ⟨hv.1, hv.2⟩
      have hbot := congrArg Subrepresentation.toSubmodule
        (hIatom.disjoint_of_ne hJatom hIJ).eq_bot
      have hvIJ' : v ∈ (I ⊓ J).toSubmodule := hvIJ
      have hz : v ∈ (⊥ : Submodule (ZMod 2) W) :=
        by rw [hbot] at hvIJ'; exact hvIJ'
      exact hz
    have hdim := moved_space_finrank ρ I.toSubmodule A a ha hdis
    have hdim2 := hdim.trans hsmall
    have hdisA := moved_space_disjoint_actor ρ L A I.toSubmodule hKI hIfaith' hA hq a ha hdis
    have hR := hrank A hA hdisA
    have hdeg := hdegree I hIfaith hI
    have hle4 : Module.finrank (ZMod 2) I.toSubmodule ≤ 4 := by
      calc
        Module.finrank (ZMod 2) I.toSubmodule ≤ 2 * rank A := hdim2
        _ ≤ 2 * 2 := Nat.mul_le_mul_left 2 hR
        _ = 4 := by norm_num
    exact (Nat.not_lt_of_ge hle4) hdeg
  let D : Subgroup (X) := L ⊔ A
  have hDinv : D ≤ subspaceStabilizer ρ I.toSubmodule := by
    exact sup_le hKI hstab
  let σ : Representation (ZMod 2) D I.toSubmodule :=
    restrictedRepresentation ρ D I.toSubmodule hDinv
  let Ld : Subgroup D := L.subgroupOf D
  let : Ld.Normal := hLn.subgroupOf D
  let eLd : Ld ≃* L := subgroupOfEquivOfLe (show L ≤ D from le_sup_left)
  have hσres : (σ.comp Ld.subtype).comp eLd.symm.toMonoidHom = I.toRepresentation := by
    apply MonoidHom.ext
    intro l
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change (ρ (l : X)) (v : _) = (ρ (l : X)) (v : _)
    rfl
  have hσirr : Representation.IsIrreducible σ := by
    have hLdI : Representation.IsIrreducible (σ.comp Ld.subtype) := by
      apply (irreducible_comp_surjective_iff eLd.symm.toMonoidHom eLd.symm.surjective
        (σ.comp Ld.subtype)).mp
      rw [hσres]
      exact hI
    let : Representation.IsIrreducible (σ.comp Ld.subtype) := hLdI
    exact irreducible_of_component_restriction σ Ld
  have hcent : centralizer (L : Set (X)) ≤ L := by
    have hcent0 := Theory.GroupTheory.centralizer_generalizedFitting_le X
    exact hcent0
  have hσfaith : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff σ).mp
    apply le_bot_iff.mp
    intro d hd
    have hd1 : σ d = 1 := MonoidHom.mem_ker.mp hd
    have hcomm : (d : X) ∈ centralizer (L : Set (X)) := by
      rw [mem_centralizer_iff]
      intro l hl
      have hconj : (d : X) * l * (d : X)⁻¹ ∈ L :=
        (inferInstance : L.Normal).conj_mem l hl (d : X)
      have hc : (d : X) * l * (d : X)⁻¹ * l⁻¹ ∈ L :=
        L.mul_mem hconj (L.inv_mem hl)
      let c : L := ⟨(d : X) * l * (d : X)⁻¹ * l⁻¹, hc⟩
      let lD : D := ⟨l, (le_sup_left : L ≤ D) hl⟩
      have hd1' : ∀ v : I.toSubmodule, σ d v = v := by
        intro v
        exact congrArg (fun f : Module.End (ZMod 2) I.toSubmodule => f v) hd1
      have hdi' : ∀ v : I.toSubmodule, σ d⁻¹ v = v := by
        intro v
        have hv := congrArg (fun f : Module.End (ZMod 2) I.toSubmodule => f v)
          (show σ d * σ d⁻¹ = 1 by simpa using (map_mul σ d d⁻¹).symm)
        simpa [hd1] using hv
      let cD : D := ⟨(c : X), (le_sup_left : L ≤ D) c.property⟩
      have hcc : σ cD = I.toRepresentation c := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        rfl
      have hσc : σ cD = 1 := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        have hcD : cD = d * lD * d⁻¹ * lD⁻¹ := by
          apply Subtype.ext
          rfl
        rw [hcD]
        have hgoal : (σ (d * lD * d⁻¹ * lD⁻¹) v : _) = (v : _) := by
          rw [map_mul, map_mul, map_mul]
          simp only [Module.End.mul_apply]
          rw [hd1', hdi']
          simp
        exact congrArg Subtype.val hgoal
      have hc1 : I.toRepresentation c = 1 := by
        rw [← hcc]
        exact hσc
      have hcval : (d : X) * l * (d : X)⁻¹ * l⁻¹ = 1 :=
        congrArg Subtype.val (hIfaith (by
          have hc1' : I.toRepresentation c = I.toRepresentation (1 : L) := by
            simpa only [map_one] using hc1
          exact hc1'))
      have hconj' : (d : X) * l * (d : X)⁻¹ = l :=
        mul_inv_eq_one.mp hcval
      have hdl : (d : X) * l = l * (d : X) := by
        calc
          (d : X) * l =
              ((d : X) * l * (d : X)⁻¹) * d := by simp
          _ = l * (d : X) := by rw [hconj']
      exact hdl.symm
    have hdL : (d : X) ∈ L := hcent hcomm
    have hdI : I.toRepresentation ⟨(d : X), hdL⟩ = 1 := by
      apply LinearMap.ext
      intro v
      have hv := congrArg (fun f : Module.End (ZMod 2) I.toSubmodule => f v) hd1
      exact hv
    have hdL1 : (⟨(d : X), hdL⟩ : L) = 1 :=
      hIfaith (by simpa using hdI)
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    exact congrArg (fun z : L => (z : X)) hdL1
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsQuasisimple Ld := IsQuasisimple.of_mulEquiv eLd.symm
  have hsup' : Ld ⊔ A.subgroupOf D = ⊤ := by
    have he := Subgroup.subgroupOf_sup (show L ≤ D from le_sup_left)
      (show A ≤ D from le_sup_right)
    rw [← he]
    change D.subgroupOf D = ⊤
    simp
  have hsup : A.subgroupOf D ⊔ Ld = ⊤ := by simpa [sup_comm] using hsup'
  let : IsElementaryAbelian 2 A := hA.2
  have hEA : IsElementaryAbelian 2 (A.subgroupOf D) :=
    IsElementaryAbelian.subgroupOf (show A ≤ D from le_sup_right)
  have hP : IsPGroup 2 (A.subgroupOf D) := IsElementaryAbelian.isPGroup 2 _
  have hquot : IsPGroup 2 (D ⧸ Ld) :=
    quotient_isPGroup_of_sup_eq_top (A.subgroupOf D) Ld hP hsup
  let : Representation.IsIrreducible σ := hσirr
  have hcore := Representation.QuadraticFourGroup.twoCore_eq_bot_of_faithful_irreducible
    σ hσfaith
  have hfitD : generalizedFitting D = Ld :=
    generalizedFitting_eq_of_quasisimple_two_quotient Ld hquot hcore
  refine ⟨I, hI, hIfaith, D, hDinv, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [σ] using hσfaith
  · simpa [σ] using hσirr
  · refine ⟨hsqtk.subgroup D, hσfaith, ?_, ?_⟩
    · rw [hfitD]
      infer_instance
    · rw [hfitD]
      apply (irreducible_comp_surjective_iff eLd.symm.toMonoidHom eLd.symm.surjective
        (σ.comp Ld.subtype)).mp
      rw [hσres]
      exact hI
  · apply (quadraticRatio_le_two_iff _).mpr
    have hAn : A.subgroupOf D ≠ (⊥ : Subgroup D) := by
      intro hzero
      apply hA.1
      have hmap := congrArg (Subgroup.map D.subtype) hzero
      simpa [Subgroup.map_subgroupOf_eq_of_le (show A ≤ D from le_sup_right)] using hmap
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : IsElementaryAbelian 2 A := hA.2
    have hEA : IsElementaryAbelian 2 (A.subgroupOf D) :=
      IsElementaryAbelian.subgroupOf (show A ≤ D from le_sup_right)
    have hAD : IsElementaryTwo (A.subgroupOf D) := ⟨hAn, hEA⟩
    have hqD : IsQuadratic σ (A.subgroupOf D) := by
      intro a ha b hb v
      apply Subtype.ext
      exact hq (a : X) ha (b : X) hb (v : _)
    have hfixed : fixedCodim σ (A.subgroupOf D) ≤ fixedCodim ρ A := by
      have hc := fixedCodim_subrepresentation_le (ρ.comp D.subtype)
        (invariantSubspace ρ D I.toSubmodule hDinv) (A.subgroupOf D)
      have hfix : fixedSpace (ρ.comp D.subtype) (A.subgroupOf D) = fixedSpace ρ A := by
        ext v
        constructor
        · intro hv a
          exact hv ⟨⟨(a : X),
            (le_sup_right : A ≤ D) a.property⟩, a.property⟩
        · intro hv a
          exact hv ⟨(a : X), a.property⟩
      have hc' : fixedCodim (ρ.comp D.subtype) (A.subgroupOf D) = fixedCodim ρ A := by
        unfold fixedCodim
        rw [hfix]
      have hσfix : fixedSpace σ (A.subgroupOf D) =
          fixedSpace (invariantSubspace ρ D I.toSubmodule hDinv).toRepresentation
            (A.subgroupOf D) := by
        ext v
        constructor
        · intro hv a
          apply Subtype.ext
          exact congrArg Subtype.val (hv a)
        · intro hv a
          apply Subtype.ext
          exact congrArg Subtype.val (hv a)
      unfold fixedCodim
      rw [hσfix]
      exact hc.trans_eq hc'
    have hrank : rank (A.subgroupOf D) = rank A :=
      congrArg (Nat.log 2)
        (Nat.card_congr (subgroupOfEquivOfLe (show A ≤ D from le_sup_right)).toEquiv)
    have hbudget : fixedCodim σ (A.subgroupOf D) ≤ 2 * rank (A.subgroupOf D) := by
      calc
        fixedCodim σ (A.subgroupOf D) ≤ fixedCodim ρ A := hfixed
        _ ≤ 2 * rank A := hsmall
        _ = 2 * rank (A.subgroupOf D) := by rw [hrank]
    exact ⟨A.subgroupOf D, hAD, hqD, hbudget⟩
  · exact ⟨(MulEquiv.subgroupCongr hfitD).trans eLd⟩

private theorem disjoint_rank_le_two
    {X : Type*} [Group X] [Finite X]
    (hz : center (generalizedFitting X) = ⊥)
    (hm : ExceptionalModel (generalizedFitting X))
    (A : Subgroup X) (hA : IsElementaryTwo A)
    (hd : Disjoint A (generalizedFitting X)) : rank A ≤ 2 := by
  let L := generalizedFitting X
  have hc : centralizer (L : Set X) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have hxl : x ∈ L := Theory.GroupTheory.centralizer_generalizedFitting_le X hx
    have hz' : (⟨x,hxl⟩ : L) ∈ center L := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp hx y y.property)
    rw [hz] at hz'
    exact congrArg Subtype.val hz'
  let f : X →* MulAut.Outer L :=
    (QuotientGroup.mk' (MulAut.innerSubgroup L)).comp MulAut.conjNormal
  have hk : f.ker = L := by
    dsimp only [f]
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      MulAut.conjNormal_comap_innerSubgroup, hc, sup_bot_eq]
  have hi : Function.Injective (f.comp A.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply _root_.eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    have hx' : x.val ∈ f.ker := hx
    rw [hk] at hx'
    exact disjoint_iff_inf_le.mp hd ⟨x.property,hx'⟩
  have hdiv := (card_dvd_of_injective (f.comp A.subtype) hi).trans
    (ModelFacts.exceptional_outer_card_dvd hm)
  rw [hA.card_eq_two_pow_rank] at hdiv
  by_contra hn
  have hthree : 3 ≤ rank A := by omega
  have hn : 2 ^ 3 ∣ 12 := (pow_dvd_pow 2 hthree).trans hdiv
  norm_num at hn

/-- Every faithful binary action with exceptional generalized Fitting subgroup
has strict quadratic ratio greater than two. This applies to the original
module restricted to the centralizer of an additional Suzuki component. -/
theorem quadraticRatio_gt_two
    {X : Type u} [Group X] [Finite X]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) X W) (hf : Function.Injective ρ)
    (hsq : IsSQTK KnownSimple.IsKnownSimple X)
    (hL : IsQuasisimple (generalizedFitting X))
    (hm : ExceptionalModel (generalizedFitting X)) : 2 < quadraticRatio ρ := by
  have hz := ModelFacts.exceptional_center hm
  by_contra! hsmall
  obtain ⟨A,hA,hq,hbound⟩ := (quadraticRatio_le_two_iff ρ).mp hsmall
  obtain ⟨U,N,hi,hfaith⟩ := faithful_irreducible_section ρ hf hL hz
  let : Finite (U.toSubmodule ⧸ N.toSubmodule) :=
    Finite.of_surjective _ N.toSubmodule.mkQ_surjective
  have hquad : IsQuadratic N.quotientRepresentation A :=
    quadratic_of_equivariant_surjection U.toRepresentation N.quotientRepresentation
      N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective (fun _ _ => rfl) A
        (quadratic_subrepresentation ρ U hq)
  have hcodim : fixedCodim N.quotientRepresentation A ≤ 2 * rank A := by
    apply le_trans ?_ hbound
    exact (Nat.le_add_right _ _).trans
      ((fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N A).trans
        (fixedCodim_subrepresentation_le ρ U A))
  obtain ⟨t,ht⟩ := ModelFacts.exceptional_involution hm
  have hdegree (I : Subrepresentation
      (N.quotientRepresentation.comp (generalizedFitting X).subtype))
      (hIf : Function.Injective I.toRepresentation)
      (hIi : IsIrreducible I.toRepresentation) :
      4 < Module.finrank (ZMod 2) I.toSubmodule :=
    NativeStrictBound.finrank_gt_four_of_exceptional I.toRepresentation
      (hsq.subgroup _) hIf hL hIi hz hm t ht
  obtain ⟨I,_,_,D,hD,_,_,_,hyp,hqD,⟨e⟩⟩ :=
    component_action_of_faithful_irreducible N.quotientRepresentation hL hz hsq
      (disjoint_rank_le_two hz hm) hdegree A hi hfaith hA hquad hcodim
  have hmD : ExceptionalModel (generalizedFitting D) := by
    unfold ExceptionalModel at hm ⊢
    rcases hm with hm | hm | hm
    all_goals obtain ⟨f⟩ := hm
    · exact Or.inl ⟨e.trans f⟩
    · exact Or.inr (Or.inl ⟨e.trans f⟩)
    · exact Or.inr (Or.inr ⟨e.trans f⟩)
  exact (not_lt_of_ge hqD) (SourceStrictBound.quadraticRatio_gt_two_of_exceptional
    (restrictedRepresentation N.quotientRepresentation D I.toSubmodule hD)
    hyp (ModelFacts.exceptional_center hmD) hmD)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.FaithfulExceptional
