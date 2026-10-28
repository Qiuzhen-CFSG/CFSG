module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.Multiplicity.SplitPrimeExclusion
public import Theory.Representation.BinaryOffender.PerfectCentralizer
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration
public import CFSG.Quasithin.ChapterD.Section02.Inheritance

/-!
# The terminal support obstruction in the nonfaithful actor branch

Let K be the original full SL₃ image on V_M and let X commute with K.
The literal K-fixed space vanishes. Thus [V_M,X] cannot be an Irr⁺
member: K stabilizes this canonical moved space, and perfectness kills
its action in the cyclic centralizer of an Irr⁺ representation.

For the actual starred actor A and B ≤ A with [X,B] = X, suppose an
A-invariant Irr⁺ member I satisfies V_M = I + C_{V_M}(A). Passing to the
literal quotient by I shows that X fixes that quotient, so [V_M,X] = I.
The preceding obstruction rules this out. D.2.7 therefore gives strict
ratio decrease on every such constituent. In particular its actual
restricted A-image has ratio below two, contradicting any endpoint-two
constituent supplied by the Suzuki branch of D.3.8 and K.3.6.

The final theorem applies this to exactly the component J and A-orbit
constructed in SourceActors. It retains that component, the original
component-centralizer placement and commutator equality, three-freeness,
five-divisibility, and the restriction on the original field degree.
It does not construct the invariant Suzuki constituent: that extraction,
together with the faithful-actor multiplicity/cubic-containment argument,
remains with qt-d-1222-natural-preliminary-source. The source theorem is
not complete until these premises are discharged. Final chapter assembly
remains with qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith, D.2.7--8, pp.179--180, and the last paragraph
of D.3.9, p.201, used for 11.0.4 on p.760, combined manuscript of
1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative ENNReal
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
namespace CubicSupport
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W)

/-- A fixed-space supplement forces the constituent to be the whole moved space. -/
private theorem moved_eq_of_invariant_supplement {X A B : Subgroup H}
    {I : Submodule (ZMod 2) W} (hI : IsIrrPlus ρ X I)
    (hAI : A ≤ subspaceStabilizer ρ I) (hBA : B ≤ A)
    (hXB : ⁅X,B⁆ = X) (hs : I ⊔ fixedSpace ρ A = ⊤) :
    subspaceCommutator ρ ⊤ X = I := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,v,_,rfl⟩
    obtain ⟨i,hi,c,hc,rfl⟩ := Submodule.mem_sup.mp (show v ∈ I ⊔ fixedSpace ρ A by rw [hs]; trivial)
    have hdiff := differences_mem_of_invariant_mod_fixed ρ hI.choose (hBA.trans hAI)
      (show X ≤ subspaceStabilizer ρ (fixedSpace ρ A ⊔ I) by
        rw [sup_comm,hs]; exact le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      (fixedSpace_antitone ρ hBA) hXB c hc x hx
    have he : ρ x (i+c) - (i+c) = (ρ x i-i)+(ρ x c-c) := by rw [map_add]; abel
    rw [he]
    exact I.add_mem (I.sub_mem ((hI.choose hx i).2 hi) hi) hdiff
  · rw [← hI.choose_spec.1]
    exact subspaceCommutator_mono_left ρ le_top X

variable [FiniteDimensional (ZMod 2) W]

/-- A fixed-free perfect commuting actor excludes an Irr⁺ moved space. -/
private theorem not_irrPlus_moved_of_commuting_perfect {K X : Subgroup H}
    [Group.IsPerfect K] (hK : fixedSpace ρ K = ⊥)
    (hXK : X ≤ centralizer (K : Set H)) :
    ¬ IsIrrPlus ρ X (subspaceCommutator ρ ⊤ X) := by
  intro hI
  have hKI : K ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ X) :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      ((le_centralizer_iff.mp hXK).trans (Subgroup.centralizer_le_normalizer _))
  exact hI.ne_bot ρ (bot_unique (hK ▸ hI.le_fixedSpace_of_perfect_centralizes ρ
    (le_centralizer_iff.mp hXK) hKI))

/-- The faithful-span alternative is impossible, so D.2.7 gives strict ratio decrease. -/
private theorem starred_constituent_ratio_drop [Finite H] {K X A B : Subgroup H}
    [Group.IsPerfect K] (hK : fixedSpace ρ K = ⊥)
    (hXK : X ≤ centralizer (K : Set H)) (hA : A ∈ ChapterD.QhatStar ρ)
    (hBA : B ≤ A) (hXB : ⁅X,B⁆ = X)
    {I : Submodule (ZMod 2) W} (hI : IsIrrPlus ρ X I)
    (hAI : A ≤ subspaceStabilizer ρ I) :
    restrictedSubgroup ρ I A ∈ ChapterD.Qhat (subspaceImageRepresentation ρ I) ∧
      actionRatio (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A) < cubicRatio ρ := by
  have hn : ¬ I ≤ fixedSpace ρ A := by
    intro hi
    apply hI.not_le_fixedSpace ρ
    rw [← hXB]
    exact le_fixedSpace_commutator_of_invariant ρ hI.choose (hi.trans (fixedSpace_antitone ρ hBA))
  rcases (ChapterD.QhatStar.restriction_alternatives ρ hA I hAI hn).2.2 with hd | ⟨_,hs⟩
  · exact hd
  · have he := moved_eq_of_invariant_supplement ρ hI hAI hBA hXB hs
    exact (not_irrPlus_moved_of_commuting_perfect ρ hK hXK (he.symm ▸ hI)).elim

end CubicSupport
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The original full SL₃ image has zero fixed space on precisely V_M. -/
theorem sl3_fullAction_component_fixedSpace_eq_bot
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    fixedSpace (imageRepresentation ρ) K = ⊥ := by
  let := fullModule_elementary D S
  let ρ := fullModuleConjugation D S
  let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
  dsimp only
  apply bot_unique
  intro v hv
  have hc : (v.toMul : G) ∈ centralizer (L : Set G) := by
    intro l hl
    have he := hv ⟨actionHom ρ (inclusion L.le_normalizer ⟨l,hl⟩),
      mem_map_of_mem (actionHom ρ) (show inclusion L.le_normalizer ⟨l,hl⟩ ∈
        L.subgroupOf (normalizer (L : Set G)) from hl)⟩
    have he' := congrArg (fun w => (w.toMul : G)) he
    change l * (v.toMul : G) * l⁻¹ = v.toMul at he'
    exact mul_inv_eq_iff_eq_mul.mp he'
  have he : (v.toMul : G) = 1 := mem_bot.mp
    ((sl3_centralizers_eq_bot D S m).2 ▸ ⟨v.toMul.property,hc⟩)
  exact congrArg Additive.ofMul (show v.toMul = 1 from Subtype.ext he)

/-- The full moved space of any subgroup commuting with the original component is not Irr⁺. -/
theorem sl3_fullAction_centralizing_support_not_irrPlus
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∀ X : Subgroup (actionImage ρ), X ≤ centralizer (K : Set (actionImage ρ)) →
      ¬ IsIrrPlus (imageRepresentation ρ) X (subspaceCommutator (imageRepresentation ρ) ⊤ X) := by
  let := fullModule_elementary D S
  let := (sl3_fullAction_component_isComponent D S m).2
  dsimp only
  intro X hc
  exact CubicSupport.not_irrPlus_moved_of_commuting_perfect _
    (sl3_fullAction_component_fixedSpace_eq_bot D S m) hc

/-- Every invariant Irr⁺ constituent of the actual moved orbit has strictly smaller ratio, hence ratio below two. -/
theorem sl3_fullAction_starred_constituent_ratio_drop
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let τ := imageRepresentation ρ
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∀ A X B : Subgroup (actionImage ρ), A ∈ ChapterD.QhatStar τ →
      X ≤ centralizer (K : Set (actionImage ρ)) → B ≤ A → ⁅X,B⁆ = X →
      ∀ I : Submodule (ZMod 2) (Additive (componentOrbit V (normalizer (L : Set G)))),
        IsIrrPlus τ X I → A ≤ subspaceStabilizer τ I →
        restrictedSubgroup τ I A ∈ ChapterD.Qhat (subspaceImageRepresentation τ I) ∧
          actionRatio (subspaceImageRepresentation τ I) (restrictedSubgroup τ I A) < cubicRatio τ ∧
          actionRatio (subspaceImageRepresentation τ I) (restrictedSubgroup τ I A) < 2 := by
  let := fullModule_elementary D S
  let := (sl3_fullAction_component_isComponent D S m).2
  dsimp only
  intro A X B hA hc hBA hm I hI hAI
  have hd := CubicSupport.starred_constituent_ratio_drop _
    (sl3_fullAction_component_fixedSpace_eq_bot D S m) hc hA hBA hm hI hAI
  exact ⟨hd.1,hd.2,hd.2.trans_le (fullAction_cubicRatio_le_two D S)⟩

/-- The terminal D.3.9 contradiction, with the literal restricted actor retained. -/
theorem sl3_fullAction_starred_no_endpoint_constituent
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let τ := imageRepresentation ρ
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∀ A X B : Subgroup (actionImage ρ), A ∈ ChapterD.QhatStar τ →
      X ≤ centralizer (K : Set (actionImage ρ)) → B ≤ A → ⁅X,B⁆ = X →
      ∀ I : Submodule (ZMod 2) (Additive (componentOrbit V (normalizer (L : Set G)))),
        IsIrrPlus τ X I → A ≤ subspaceStabilizer τ I →
        2 ≤ actionRatio (subspaceImageRepresentation τ I) (restrictedSubgroup τ I A) → False := by
  let := fullModule_elementary D S
  dsimp only
  intro A X B hA hc hBA hm I hI hAI hr
  exact (not_lt_of_ge hr)
    (sl3_fullAction_starred_constituent_ratio_drop D S m A X B hA hc hBA hm I hI hAI).2.2

/-- The actual nonfaithful source component and its orbit have no saturated Irr⁺
support. Every actor-invariant Irr⁺ constituent of that same orbit has strictly
smaller ratio than the original minimum, and in particular ratio below two. -/
theorem sl3_fullAction_starred_nonfaithful_component_strict_constituents
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let τ := imageRepresentation ρ
    let H := actionImage ρ
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∀ A : Subgroup H, A ∈ ChapterD.QhatStar τ →
      A ⊓ centralizer (K : Set H) ≠ ⊥ →
      S.field.degree % 4 = 2 ∧
      ∃ J : Subgroup H, IsComponent H J ∧
        ⁅J,A ⊓ centralizer (K : Set H)⁆ ≠ ⊥ ∧
        componentOrbit J A ≤ centralizer (K : Set H) ∧
        ⁅componentOrbit J A,A ⊓ centralizer (K : Set H)⁆ = componentOrbit J A ∧
        Nat.Coprime 3 (Nat.card J) ∧ 5 ∣ Nat.card J ∧
        (¬ IsIrrPlus τ (componentOrbit J A) (subspaceCommutator τ ⊤ (componentOrbit J A))) ∧
        ∀ I : Submodule (ZMod 2) (Additive (componentOrbit V (normalizer (L : Set G)))),
          IsIrrPlus τ (componentOrbit J A) I → A ≤ subspaceStabilizer τ I →
          restrictedSubgroup τ I A ∈ ChapterD.Qhat (subspaceImageRepresentation τ I) ∧
            actionRatio (subspaceImageRepresentation τ I) (restrictedSubgroup τ I A) < cubicRatio τ ∧
            actionRatio (subspaceImageRepresentation τ I) (restrictedSubgroup τ I A) < 2 := by
  let := fullModule_elementary D S
  let ρ := fullModuleConjugation D S
  let H := actionImage ρ
  let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
  dsimp only
  intro A hA hn
  obtain ⟨J,hJ,hm,ho,he,h3⟩ :=
    sl3_fullAction_starred_nonfaithful_component D S m heven A hA hn
  let := hJ.2
  have hJne : J ≠ ⊥ := by
    intro hz
    rw [hz,commutator_bot_left] at hm
    exact hm rfl
  refine ⟨sl3_fullAction_starred_nonfaithful_degree D S m heven A hA hn,
    J,hJ,hm,ho,he,h3,
    sl3_fullAction_perfect_centralizer_five_dvd D S m heven J hJne
      ((le_componentOrbit J A).trans ho),
    sl3_fullAction_centralizing_support_not_irrPlus D S m _ ho,?_⟩
  intro I hI hAI
  exact sl3_fullAction_starred_constituent_ratio_drop D S m A (componentOrbit J A)
    (A ⊓ centralizer (K : Set H)) hA ho inf_le_left he I hI hAI

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
