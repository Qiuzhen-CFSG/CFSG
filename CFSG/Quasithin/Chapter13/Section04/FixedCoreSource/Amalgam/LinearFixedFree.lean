module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ComponentFixedFree
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearParabolicPair
public import Theory.Representation.PSL3Two.FanoFixedFreeQuotient
public import Theory.Representation.BinaryOffender.ConjugationCommutator

/-!
# Fully moved fixed-line orbits in the original linear amalgam

The selected component has no fixed vectors on the whole omega module,
hence on either original fixed-line orbit. Its Fano permutation quotient
therefore kills the constant line. The whole orbit is actually the dual
natural module or the Fano core, of dimension three or six, under the same
marking of the original parabolic and common Sylow. In particular the
orbit equals its group commutator with the component. Applying the result
to both original vertices and using their proved spanning identity gives
[V₀,K]=V₀.

This removes the possible trivial summands from the earlier orbit
classification. The comparison of the two orbits, the remaining model
exclusions, Thompson normality and the overgroup supplement still belong
to the 13.4.7 assembly. Structural1222 and Source1332OneTwo retain their
earlier producers; no PlaneAmalgamSource1347 premise is used here.
Source: Aschbacher–Smith 13.4.7, printed pp.900–901.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open BinaryLinearThree.FanoDecomposition Representation.BinaryOffender
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The original fixed-line orbit is fully moved, and its whole action is
actually dual natural or the Fano core under the same parabolic/Sylow marking. -/
theorem original_pair_linear_fixed_line_models
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL) :
    let C := K.map (A ⊔ B).subtype
    let F := omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)
    let U := conjugateSpanBy F C
    ⁅U,C⁆ = U ∧ ∃ he : IsElementaryAbelian 2 U, let := he
      let ρ := Representation.elementaryRepresentation (p := 2)
        (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy F C)))
      (Module.finrank (ZMod 2) (Additive U) = 3 ∨
        Module.finrank (ZMod 2) (Additive U) = 6) ∧
      ∃ e : (C ⧸ pCore 2 C) ≃* BinaryLinearThree.Group,
        let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
        (A.subgroupOf C).map f = Matrix.PSL3Two.pointParabolicSL ∧
        (B.subgroupOf C).map f = Matrix.PSL3Two.lineParabolicSL ∧
        ((T : Subgroup G).subgroupOf C).map f = Matrix.PSL3Two.borelSL ∧
        (Nonempty (Representation.Equiv (BinaryLinearThree.W.dual.comp f) ρ) ∨
          Nonempty (Representation.Equiv (lineCoreRepresentation.comp f) ρ)) := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let F := Z ⊓ centralizer (B : Set G)
  let U := conjugateSpanBy F C
  obtain ⟨he,hd,_,e,hP,hS,⟨q,hq,_,_⟩,_⟩ := original_pair_linear_fixed_line_quotient
    h₀ h structural D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  let := he
  let ρ := Representation.elementaryRepresentation (p := 2)
    (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy F C)))
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfree := original_pair_component_fixed_free h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK
  have hUW : U ≤ conjugateSpanBy Z X :=
    conjugateSpanBy_mono inf_le_left (map_subtype_le K)
  have hfixed (v : Additive U) (hv : ∀ c : C, ρ c v = v) : v = 0 := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply hfree.le
    refine ⟨hUW v.toMul.property,?_⟩
    intro c hc
    have hh := congrArg (fun x : Additive U => x.toMul.val) (hv ⟨c,hc⟩)
    change c * v.toMul.val * c⁻¹ = v.toMul.val at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  change Module.finrank (ZMod 2) (Additive U) = 3 ∨
    Module.finrank (ZMod 2) (Additive U) = 4 ∨
    Module.finrank (ZMod 2) (Additive U) = 6 ∨
    Module.finrank (ZMod 2) (Additive U) = 7 at hd
  obtain ⟨_,hm,hmodels,hdim⟩ := BinaryLinearThree.FanoFixedFreeQuotient.whole_models
    f hf ρ q hq (by rcases hd with hd | hd | hd | hd <;> omega) hfixed
  have hA := original_pair_linear_companion_image h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK eK e hP hS
  exact ⟨group_commutator_eq_of_elementary_moved U C
    (le_normalizer_conjugateSpanBy F C) hm,he,hdim,e,hA,hP,hS,hmodels⟩
/-- The complete original omega module is its commutator with the actual linear component. -/
theorem original_pair_linear_whole_moved
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL) :
    let C := K.map (A ⊔ B).subtype
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
    ⁅U,C⁆ = U := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let F₁ := Z ⊓ centralizer (A : Set G)
  let F₂ := Z ⊓ centralizer (B : Set G)
  let U₁ := conjugateSpanBy F₁ C
  let U₂ := conjugateSpanBy F₂ C
  let U := conjugateSpanBy Z X
  have hm₂ : ⁅U₂,C⁆ = U₂ := (original_pair_linear_fixed_line_models h₀ h structural
    D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK).1
  have hm₁ : ⁅U₁,C⁆ = U₁ := by
    have aux := fun (J : Subgroup (B ⊔ A : Subgroup G)) (hJ : J.IsCComponent)
      (eJ : ((J.map (B ⊔ A).subtype) ⧸ pCore 2 (J.map (B ⊔ A).subtype)) ≃*
        Matrix.PSL3Two.PSL) =>
      (original_pair_linear_fixed_line_models h₀ h structural D m hTB hTA eB eA hne.symm
        (by simpa only [sup_comm B A] using hout) hindexL hindexB hindexA
        (by dsimp only; rw [sup_comm B A]; exact Or.symm hres) h1332 J hJ eJ).1
    have aux' : ∀ (J : Subgroup (A ⊔ B : Subgroup G)) (hJ : J.IsCComponent)
      (eJ : ((J.map (A ⊔ B).subtype) ⧸ pCore 2 (J.map (A ⊔ B).subtype)) ≃*
        Matrix.PSL3Two.PSL),
      ⁅conjugateSpanBy F₁ (J.map (A ⊔ B).subtype),J.map (A ⊔ B).subtype⁆ =
        conjugateSpanBy F₁ (J.map (A ⊔ B).subtype) := by
      rw [sup_comm B A] at aux
      exact aux
    exact aux' K hK eK
  have hs : U = U₁ ⊔ U₂ := original_pair_component_fixed_line_spans h₀ h structural
    D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK
  change ⁅U,C⁆ = U
  apply le_antisymm
  · exact le_normalizer_iff_commutator_le_left.mp
      ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X))
  · rw [hs]
    apply sup_le
    · calc
        U₁ = ⁅U₁,C⁆ := hm₁.symm
        _ ≤ ⁅U₁ ⊔ U₂,C⁆ := commutator_mono le_sup_left le_rfl
    · calc
        U₂ = ⁅U₂,C⁆ := hm₂.symm
        _ ≤ ⁅U₁ ⊔ U₂,C⁆ := commutator_mono le_sup_right le_rfl

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
