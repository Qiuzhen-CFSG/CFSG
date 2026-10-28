module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearOrbitPair
public import Theory.Representation.PSL3Two.NaturalDualSum

/-!
# The split case of the original two-orbit comparison

Both orbit classifications use the same marking. If both are natural, their
opposite orientations force zero intersection, so their proved spanning sum is
the actual six-dimensional natural-plus-dual module. Otherwise an original
orbit is already a six-dimensional Fano core. No homogeneous double survives
the first branch. Identifying the whole module in the core branches and the
Thompson and overgroup conclusions remain in the source assembly.

Structural1222 and Source1332OneTwo retain their preceding producers.
Source: Aschbacher–Smith 13.4.7, printed pp.900–901.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open BinaryLinearThree.FanoDecomposition
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The original module is the split natural-plus-dual six-space, or one
of its original fixed-line orbits is already a six-dimensional Fano core. -/
theorem original_pair_linear_orbit_comparison
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
    let X := A ⊔ B
    let C := K.map X.subtype
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U := conjugateSpanBy Z X
    let U₁ := conjugateSpanBy (Z ⊓ centralizer (A : Set G)) C
    let U₂ := conjugateSpanBy (Z ⊓ centralizer (B : Set G)) C
    ∃ he : IsElementaryAbelian 2 U, let := he
      let ρ := Representation.elementaryRepresentation (p := 2)
        (U.normalizerMonoidHom.comp (inclusion
          ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X))))
      ∃ e : (C ⧸ pCore 2 C) ≃* BinaryLinearThree.Group,
        let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
        (A.subgroupOf C).map f = Matrix.PSL3Two.pointParabolicSL ∧
        (B.subgroupOf C).map f = Matrix.PSL3Two.lineParabolicSL ∧
        ((T : Subgroup G).subgroupOf C).map f = Matrix.PSL3Two.borelSL ∧
        ((U₁ ⊓ U₂ = ⊥ ∧
          Nonempty (Representation.Equiv
            ((BinaryLinearThree.W.prod BinaryLinearThree.W.dual).comp f) ρ) ∧
          Nat.card U = 64) ∨ Nat.card U₁ = 64 ∨ Nat.card U₂ = 64) := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  have hUX : U ≤ X := conjugateSpanBy_le (fun z hz =>
    (hTA.trans le_sup_left) ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  have hred := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).1
  let : IsElementaryAbelian 2 (U.subgroupOf X) := hred.elementary
  let he : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hUX).symm.toMonoidHom (subgroupOfEquivOfLe hUX).symm.injective
  let := he
  obtain ⟨e,hA,hB,hS⟩ := original_pair_linear_parabolic_pair h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK eK
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨he₁,he₂,hm₁,hm₂⟩ := original_pair_linear_same_marking_models h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK e hA hB
  let := he₁
  let := he₂
  refine ⟨he,e,hA,hB,hS,?_⟩
  have hs := original_pair_component_fixed_line_spans h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK
  rcases hm₁ with hn | hc
  · obtain ⟨a⟩ := hn
    rcases hm₂ with hn | hc
    · obtain ⟨b⟩ := hn
      exact Or.inl (BinaryLinearThree.NaturalDualSum.subgroup_sum f hf
        ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X))
        (le_normalizer_conjugateSpanBy _ C) (le_normalizer_conjugateSpanBy _ C)
        hs.symm a b)
    · obtain ⟨b⟩ := hc
      right; right
      calc
        _ = Nat.card LineCore := (Nat.card_congr b.toLinearEquiv.toEquiv).symm
        _ = 64 := by
          let : Nonempty Line := ⟨Matrix.PSL3Two.flagLine⟩
          rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
            BinaryPermutation.finrank_core,Matrix.PSL3Two.Fano.card_line]
          rfl
  · obtain ⟨a⟩ := hc
    right; left
    calc
      _ = Nat.card BinaryLinearThree.Core := (Nat.card_congr a.toLinearEquiv.toEquiv).symm
      _ = 64 := by
        let : Nonempty BinaryLinearThree.Point := ⟨Matrix.PSL3Two.flagPoint⟩
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
          BinaryPermutation.finrank_core,Matrix.PSL3Two.Fano.card_point]
        rfl

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
