module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.ConstituentGeometry
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Models
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Sections
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Ratios
public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.Representation.BinaryOffender.IrreducibleOrbitAction
public import Theory.Representation.ConjugateRep
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient

/-!
# The terminal component constituent

This file performs the component passage in the last paragraph of terminal
§13.6.  A faithful irreducible `H*` section is restricted to the actual normal
component `L*`.  A faithful irreducible constituent is chosen explicitly.  A
small quadratic actor cannot move this constituent: the moved-constituent
estimate would give both a degree contradiction and the rank-two obstruction.
The actor therefore stabilizes the constituent, and the join of the actor and
`L*` has a faithful irreducible action satisfying the literal B.4 hypotheses.

The source component conclusion is retained by the final application theorem;
only its proved residual-model and quasisimplicity consequences are used in
this reduction.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSections
open CFSG.Quasithin.Chapter13.Section08
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound

universe u v

/-- A convenient name for the component action used throughout this file. -/
private abbrev componentAction {X W : Type*} [Group X] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) X W)
    (K : Subgroup X) (I : Subrepresentation (ρ.comp K.subtype)) :
    Representation (ZMod 2) K I.toSubmodule := I.toRepresentation

def restrictedRepresentation
    {X W : Type*} [Group X] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) (D : Subgroup X)
    (I : Submodule (ZMod 2) W)
    (hD : D ≤ subspaceStabilizer ρ I) :
    Representation (ZMod 2) D I :=
  { toFun := fun d => (ρ d).restrict (fun v hv => (hD d.property v).2 hv)
    map_one' := by
      ext v
      simp
    map_mul' := by
      intro a b
      ext v
      exact congrArg (fun f : Module.End (ZMod 2) W => f (v : W))
        (map_mul ρ (a : X) (b : X)) }

/-- A nonzero irreducible constituent of a faithful irreducible action of a
centerless quasisimple normal subgroup is itself faithful. -/
private theorem exists_faithful_component_constituent
    {X W : Type*} [Group X] [Finite X]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) (hρ : IsIrreducible ρ)
    (hfaith : Function.Injective ρ) (K : Subgroup X) [K.Normal]
    (hK : IsQuasisimple K) (hz : center K = ⊥) :
    ∃ I : Subrepresentation (ρ.comp K.subtype),
      IsIrreducible I.toRepresentation ∧ Function.Injective I.toRepresentation := by
  let _ : IsQuasisimple K := hK
  let _ : IsIrreducible ρ := hρ
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial ρ
  have hKne : K ≠ ⊥ := by
    have hnt : Nontrivial (K ⧸ center K) := hK.simple.toNontrivial
    have hntK : Nontrivial K :=
      (QuotientGroup.mk'_surjective (center K)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot K).mp hntK
  have hsurvive : ¬ K ≤ ρ.ker := by
    intro h
    apply hKne
    apply le_bot_iff.mp
    exact h.trans ((MonoidHom.ker_eq_bot_iff ρ).mpr hfaith).le
  obtain ⟨I, hI⟩ :=
    Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
      (ρ.comp K.subtype)
  let : IsIrreducible I.toRepresentation := hI
  let : Nontrivial I.toSubmodule :=
    Subrepresentation.irreducible_module_nontrivial I.toRepresentation
  have hInonbot : I.toSubmodule ≠ (⊥ : Submodule (ZMod 2) W) := by
    intro h
    have hs : Subsingleton I.toSubmodule := by
      rw [h]
      infer_instance
    exact not_nontrivial I.toSubmodule (show Nontrivial I.toSubmodule from inferInstance)
  have hsimple : IsSimpleGroup K := by
    let : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
    apply IsSimpleGroup.mk
    intro N hN
    rcases hK.normal_le_center_or_eq_top N with hNC | htop
    · exact Or.inl (le_bot_iff.mp (hNC.trans_eq hz))
    · exact Or.inr htop
  let _ : IsSimpleGroup K := hsimple
  have hIfaith : Function.Injective I.toRepresentation := by
    apply (MonoidHom.ker_eq_bot_iff I.toRepresentation).mp
    have hker : I.toRepresentation.ker = (⊥ : Subgroup K) := by
      rcases (inferInstance : I.toRepresentation.ker.Normal).eq_bot_or_eq_top with hbot | htop
      · exact hbot
      · exfalso
        have hIfix : I.toSubmodule ≤ fixedSpace ρ K := by
          intro v hv k
          have hk : (⟨k, k.property⟩ : K) ∈ I.toRepresentation.ker := by
            rw [htop]
            exact mem_top _
          have hkfix := congrArg (fun f : Module.End (ZMod 2) I.toSubmodule =>
              f ⟨v, hv⟩) (MonoidHom.mem_ker.mp hk)
          have hvfix := hkfix
          exact congrArg Subtype.val hvfix
        let F : Subrepresentation ρ :=
          { toSubmodule := fixedSpace ρ K
            apply_mem_toSubmodule := fun g v hv =>
              (fixedSpace_stable_of_normal ρ K (mem_top g) v).mpr hv }
        have hIF : I.toSubmodule ≤ F.toSubmodule := hIfix
        rcases (show F = (⊥ : Subrepresentation ρ) ∨ F = ⊤ from
          (inferInstance : IsSimpleOrder (Subrepresentation ρ)).eq_bot_or_eq_top F) with
          hFb | hFt
        · exfalso
          apply hInonbot
          have hFbot : F.toSubmodule = (⊥ : Submodule (ZMod 2) W) :=
            congrArg Subrepresentation.toSubmodule hFb
          exact le_bot_iff.mp (hFbot ▸ hIF)
        · have hFtop : fixedSpace ρ K = ⊤ := by
            exact congrArg Subrepresentation.toSubmodule hFt
          apply hsurvive
          intro k hk
          change ρ k = 1
          apply LinearMap.ext
          intro v
          have hvtop : v ∈ (⊤ : Submodule (ZMod 2) W) := Submodule.mem_top
          have hv : v ∈ fixedSpace ρ K := hFtop.symm ▸ hvtop
          change ∀ q : K, ρ q v = v at hv
          exact hv ⟨k, hk⟩
    exact hker
  exact ⟨I, hI, hIfaith⟩

private theorem irreducible_of_component_restriction
    {X W : Type*} [Group X] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) (K : Subgroup X) [K.Normal]
    [Representation.IsIrreducible (ρ.comp K.subtype)] :
    Representation.IsIrreducible ρ := by
  let : Nontrivial W :=
    Subrepresentation.irreducible_module_nontrivial (ρ.comp K.subtype)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let T : Subrepresentation (ρ.comp K.subtype) :=
    ⟨S.toSubmodule, fun l _ hv => S.apply_mem_toSubmodule l hv⟩
  rcases eq_bot_or_eq_top T with hT | hT
  · left
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun V : Subrepresentation (ρ.comp K.subtype) => V.toSubmodule) hT)
  · right
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun V : Subrepresentation (ρ.comp K.subtype) => V.toSubmodule) hT)

variable {G : Type*} [Group G] [Finite G]
  (H V₃ V₁ : Subgroup G) [IsElementaryAbelian 2 (Source.UH H V₃)]
  (hn : H ≤ normalizer (V₁ : Set G))
  (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)

open Section08

set_option maxHeartbeats 3000000 in
/-- The literal terminal action after passing to a faithful component
constituent.  The quantitative hypotheses are intentionally explicit: the
center, degree, and rank inputs are supplied by the independent terminal
model-fact and B.4-exclusion branches. -/
theorem component_action_of_section
    {𝒦 : GroupClass}
    (hfit : generalizedFitting (Source.Hstar H) =
      Source.starImage H (terminalResidual H))
    (hL : IsQuasisimple (Source.starImage H (terminalResidual H)))
    (hz : center (Source.starImage H (terminalResidual H)) = ⊥)
    (hsqtk : IsSQTK 𝒦 (Source.Hstar H))
    (hrank : ∀ B : Subgroup (Source.Hstar H), IsElementaryTwo B →
      Disjoint B (Source.starImage H (terminalResidual H)) → rank B ≤ 2)
    (U : Subrepresentation (starRepresentation H V₃ V₁ hn hk))
    (N : Subrepresentation U.toRepresentation)
    [Finite (U.toSubmodule ⧸ N.toSubmodule)]
    (hdegree : ∀
      (I : Subrepresentation
        (N.quotientRepresentation.comp
          (Source.starImage H (terminalResidual H)).subtype)),
      Function.Injective I.toRepresentation → Representation.IsIrreducible I.toRepresentation →
        4 < Module.finrank (ZMod 2) I.toSubmodule)
    (A : Subgroup (Source.Hstar H))
    (hi : N.quotientRepresentation.IsIrreducible)
    (hf : Function.Injective N.quotientRepresentation)
    (hA : IsElementaryTwo A)
    (hq : IsQuadratic N.quotientRepresentation A)
    (hsmall : fixedCodim N.quotientRepresentation A ≤ 2 * rank A) :
    ∃ I : Subrepresentation
        (N.quotientRepresentation.comp
          (Source.starImage H (terminalResidual H)).subtype),
      IsIrreducible I.toRepresentation ∧
      Function.Injective I.toRepresentation ∧
      ∃ (D : Subgroup (Source.Hstar H))
        (hD : D ≤ subspaceStabilizer N.quotientRepresentation I.toSubmodule),
        D = Source.starImage H (terminalResidual H) ⊔ A ∧
        Function.Injective
          (restrictedRepresentation N.quotientRepresentation D I.toSubmodule hD) ∧
        Representation.IsIrreducible
          (restrictedRepresentation N.quotientRepresentation D I.toSubmodule hD) ∧
        B4Hypotheses 𝒦
          (restrictedRepresentation N.quotientRepresentation D I.toSubmodule hD) ∧
        quadraticRatio
          (restrictedRepresentation N.quotientRepresentation D I.toSubmodule hD) ≤ 2 ∧
        Nonempty (generalizedFitting D ≃* Source.starImage H (terminalResidual H)) := by
  let ρ := N.quotientRepresentation
  let L := Source.starImage H (terminalResidual H)
  have hLn0 : (Source.starImage H (terminalResidual H)).Normal := by
    rw [← hfit]
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
      have hz : v ∈ (⊥ : Submodule (ZMod 2) (U.toSubmodule ⧸ N.toSubmodule)) :=
        by rw [hbot] at hvIJ'; exact hvIJ'
      exact hz
    obtain ⟨hdisA, hdim, hdim2⟩ := moved_star_constituent_bounds
      H V₃ V₁ hn hk U N I.toSubmodule hKI hIfaith' A hA hq hsmall a ha hdis
    have hR := hrank A hA hdisA
    have hdeg := hdegree I hIfaith hI
    have hle4 : Module.finrank (ZMod 2) I.toSubmodule ≤ 4 := by
      calc
        Module.finrank (ZMod 2) I.toSubmodule ≤ 2 * rank A := hdim2
        _ ≤ 2 * 2 := Nat.mul_le_mul_left 2 hR
        _ = 4 := by norm_num
    exact (Nat.not_lt_of_ge hle4) hdeg
  let D : Subgroup (Source.Hstar H) := L ⊔ A
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
    change (ρ (l : Source.Hstar H)) (v : _) = (ρ (l : Source.Hstar H)) (v : _)
    rfl
  have hσirr : Representation.IsIrreducible σ := by
    have hLdI : Representation.IsIrreducible (σ.comp Ld.subtype) := by
      apply (irreducible_comp_surjective_iff eLd.symm.toMonoidHom eLd.symm.surjective
        (σ.comp Ld.subtype)).mp
      rw [hσres]
      exact hI
    let : Representation.IsIrreducible (σ.comp Ld.subtype) := hLdI
    exact irreducible_of_component_restriction σ Ld
  have hcent : centralizer (L : Set (Source.Hstar H)) ≤ L := by
    have hcent0 := centralizer_generalizedFitting_le (G := Source.Hstar H)
    rw [hfit] at hcent0
    exact hcent0
  have hσfaith : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff σ).mp
    apply le_bot_iff.mp
    intro d hd
    have hd1 : σ d = 1 := MonoidHom.mem_ker.mp hd
    have hcomm : (d : Source.Hstar H) ∈ centralizer (L : Set (Source.Hstar H)) := by
      rw [mem_centralizer_iff]
      intro l hl
      have hconj : (d : Source.Hstar H) * l * (d : Source.Hstar H)⁻¹ ∈ L :=
        (inferInstance : L.Normal).conj_mem l hl (d : Source.Hstar H)
      have hc : (d : Source.Hstar H) * l * (d : Source.Hstar H)⁻¹ * l⁻¹ ∈ L :=
        L.mul_mem hconj (L.inv_mem hl)
      let c : L := ⟨(d : Source.Hstar H) * l * (d : Source.Hstar H)⁻¹ * l⁻¹, hc⟩
      let lD : D := ⟨l, (le_sup_left : L ≤ D) hl⟩
      have hd1' : ∀ v : I.toSubmodule, σ d v = v := by
        intro v
        exact congrArg (fun f : Module.End (ZMod 2) I.toSubmodule => f v) hd1
      have hdi' : ∀ v : I.toSubmodule, σ d⁻¹ v = v := by
        intro v
        have hv := congrArg (fun f : Module.End (ZMod 2) I.toSubmodule => f v)
          (show σ d * σ d⁻¹ = 1 by simpa using (map_mul σ d d⁻¹).symm)
        simpa [hd1] using hv
      let cD : D := ⟨(c : Source.Hstar H), (le_sup_left : L ≤ D) c.property⟩
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
      have hcval : (d : Source.Hstar H) * l * (d : Source.Hstar H)⁻¹ * l⁻¹ = 1 :=
        congrArg Subtype.val (hIfaith (by
          have hc1' : I.toRepresentation c = I.toRepresentation (1 : L) := by
            simpa only [map_one] using hc1
          exact hc1'))
      have hconj' : (d : Source.Hstar H) * l * (d : Source.Hstar H)⁻¹ = l :=
        mul_inv_eq_one.mp hcval
      have hdl : (d : Source.Hstar H) * l = l * (d : Source.Hstar H) := by
        calc
          (d : Source.Hstar H) * l =
              ((d : Source.Hstar H) * l * (d : Source.Hstar H)⁻¹) * d := by simp
          _ = l * (d : Source.Hstar H) := by rw [hconj']
      exact hdl.symm
    have hdL : (d : Source.Hstar H) ∈ L := hcent hcomm
    have hdI : I.toRepresentation ⟨(d : Source.Hstar H), hdL⟩ = 1 := by
      apply LinearMap.ext
      intro v
      have hv := congrArg (fun f : Module.End (ZMod 2) I.toSubmodule => f v) hd1
      exact hv
    have hdL1 : (⟨(d : Source.Hstar H), hdL⟩ : L) = 1 :=
      hIfaith (by simpa using hdI)
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    exact congrArg (fun z : L => (z : Source.Hstar H)) hdL1
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
  · simpa [σ, ρ] using hσfaith
  · simpa [σ, ρ] using hσirr
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
      exact hq (a : Source.Hstar H) ha (b : Source.Hstar H) hb (v : _)
    have hfixed : fixedCodim σ (A.subgroupOf D) ≤ fixedCodim ρ A := by
      have hc := fixedCodim_subrepresentation_le (ρ.comp D.subtype)
        (invariantSubspace ρ D I.toSubmodule hDinv) (A.subgroupOf D)
      have hfix : fixedSpace (ρ.comp D.subtype) (A.subgroupOf D) = fixedSpace ρ A := by
        ext v
        constructor
        · intro hv a
          exact hv ⟨⟨(a : Source.Hstar H),
            (le_sup_right : A ≤ D) a.property⟩, a.property⟩
        · intro hv a
          exact hv ⟨(a : Source.Hstar H), a.property⟩
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
  · let efit : generalizedFitting D ≃* L :=
      (by
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
        exact (MulEquiv.subgroupCongr
          (generalizedFitting_eq_of_quasisimple_two_quotient Ld hquot hcore)).trans eLd)
    exact ⟨efit⟩

/-! The source-level wrapper keeps the complete component conclusion beside
the literal section and component action.  In particular, none of the
generation, residual, or diagram clauses is replaced by the exceptional
carrier equivalence used in the preceding reduction. -/
set_option maxHeartbeats 3000000 in
theorem component_action_of_source
    {𝒦 : GroupClass}
    (S : Subgroup H)
    (hs : Components.Conclusion S)
    (hz : center (Source.starImage H (terminalResidual H)) = ⊥)
    (hsqtk : IsSQTK 𝒦 (Source.Hstar H))
    (hrank : ∀ B : Subgroup (Source.Hstar H), IsElementaryTwo B →
      Disjoint B (Source.starImage H (terminalResidual H)) → rank B ≤ 2)
    (hdegree : ∀
      (U : Subrepresentation (starRepresentation H V₃ V₁ hn hk))
      (N : Subrepresentation U.toRepresentation)
      (I : Subrepresentation
        (N.quotientRepresentation.comp
          (Source.starImage H (terminalResidual H)).subtype)),
      Function.Injective I.toRepresentation →
        Representation.IsIrreducible I.toRepresentation →
          4 < Module.finrank (ZMod 2) I.toSubmodule)
    (hsmall : quadraticRatio (starRepresentation H V₃ V₁ hn hk) ≤ 2) :
    ∃ (U : Subrepresentation (starRepresentation H V₃ V₁ hn hk))
      (N : Subrepresentation U.toRepresentation),
      letI : Finite (U.toSubmodule ⧸ N.toSubmodule) :=
        Finite.of_surjective _ N.toSubmodule.mkQ_surjective
      ∃ (A : Subgroup (Source.Hstar H))
      (I : Subrepresentation
        (N.quotientRepresentation.comp
          (Source.starImage H (terminalResidual H)).subtype))
      (D : Subgroup (Source.Hstar H))
      (hD : D ≤ subspaceStabilizer N.quotientRepresentation I.toSubmodule),
      Components.Conclusion S ∧
      N.quotientRepresentation.IsIrreducible ∧
      Function.Injective N.quotientRepresentation ∧
      IsElementaryTwo A ∧
      IsQuadratic N.quotientRepresentation A ∧
      fixedCodim N.quotientRepresentation A ≤ 2 * rank A ∧
      IsIrreducible I.toRepresentation ∧
      Function.Injective I.toRepresentation ∧
      D = Source.starImage H (terminalResidual H) ⊔ A ∧
      Function.Injective
        (restrictedRepresentation N.quotientRepresentation D I.toSubmodule hD) ∧
      Representation.IsIrreducible
        (restrictedRepresentation N.quotientRepresentation D I.toSubmodule hD) ∧
      B4Hypotheses 𝒦
        (restrictedRepresentation N.quotientRepresentation D I.toSubmodule hD) ∧
      quadraticRatio
        (restrictedRepresentation N.quotientRepresentation D I.toSubmodule hD) ≤ 2 ∧
      Nonempty (generalizedFitting D ≃* Source.starImage H (terminalResidual H)) := by
  have hfit := (residual_model_of_source H S hs).1
  have hL := residual_quasisimple_of_source H S hs
  obtain ⟨U, N, A, hi, hf, hA, hqStar, hcStar, hqN, hcN, hbound⟩ :=
    exists_bounded_faithful_irreducible_star_section H V₃ V₁ hn hk hfit hL hz hsmall
  let : Finite (U.toSubmodule ⧸ N.toSubmodule) :=
    Finite.of_surjective _ N.toSubmodule.mkQ_surjective
  obtain ⟨I, hI, hIfaith, D, hD, hjoin, hσfaith, hσirr, hB4, hratio, heq⟩ :=
    component_action_of_section H V₃ V₁ hn hk hfit hL hz hsqtk hrank U N (hdegree U N) A
      hi hf hA hqN hbound
  refine ⟨U, N, ?_⟩
  let : Finite (U.toSubmodule ⧸ N.toSubmodule) :=
    Finite.of_surjective _ N.toSubmodule.mkQ_surjective
  exact ⟨A, I, D, hD, hs, hi, hf, hA, hqN, hbound, hI, hIfaith,
    hjoin, hσfaith, hσirr, hB4, hratio, heq⟩

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound
