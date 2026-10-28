module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionQuotientFF
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionNormalSupport

/-!
# Normal support on the literal chosen-seed isotypic pair

The existing odd-degree natural SL₃ reduction supplies an actual component
orbit in the component centralizer for each starred actor. The layer rank
bound makes a moved Suzuki orbit a normal pair; the other surviving support
is already a normal component. Thus every support is normal in Aut_M(U).

Faithfulness of the full action and the complementary conjugate isotypic
halves force that support to move both halves. Its centralizer placement
makes both halves invariant. Component dichotomy then identifies the kernels
on them as central. For the Suzuki pair they are trivial, and the theorem
retains the actual two components, their group isomorphism, and the original
conjugation-and-multiplication coordinates.

All extra normality, movement and faithfulness conclusions are discharged
from the original chosen-module hypotheses. This does not exclude the
surviving support or establish U = W. The FF classification, component
movement and multiplicity arguments, other-model FF sections and Source325
assembly remain with qt-baumann-fsu.
Source: Aschbacher--Smith D.3.14--18, printed pp.202--203;
chosen-seed application3.2.5, p.580.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The surviving support is normal; a Suzuki support is the actual centerless
product of its two conjugate components, with multiplication coordinates. -/
theorem normalizer_starred_normal_support_of_odd_linearThree
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G))
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let f := internalHom M U hn
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map f
    let C := centralizer (K : Set (internalActionImage M U hn))
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component → A ∈ QhatStar ρ →
      ∃ X J : Subgroup (internalActionImage M U hn),
        X.Normal ∧ X ≤ C ∧ X ≠ ⊥ ∧ ⁅X,A ⊓ C⁆ = X ∧
        IsComponent (internalActionImage M U hn) J ∧ J ≤ C ∧ X = componentOrbit J A ∧
        ((∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) ∧
            ∃ a ∈ A, a ∉ normalizer (J : Set (internalActionImage M U hn)) ∧
              (normalizer (J : Set (internalActionImage M U hn))).index = 2 ∧
              X = J ⊔ J.map (MulAut.conj a).toMonoidHom ∧
              ∃ d : J × J ≃* X,
                (∀ x y : J, (d (x,y) : internalActionImage M U hn) =
                  x.val * (a * y.val * a⁻¹)) ∧ center X = ⊥) ∨
          (X = J ∧ J.Normal ∧ primeRank 3 J = 1 ∧ pCore 3 C = ⊥)) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let f := internalHom M U hn
  let ρ := UniqueFactor.imageRepresentation M U hn
  let K := (L.subgroupOf M).map f
  let C := centralizer (K : Set (internalActionImage M U hn))
  dsimp only
  intro A hAS hA
  have hs := D.normalizer_starred_component_support_of_odd_linearThree
    h hmany hc hm hne F ho e A hAS hA
  rcases hs with ⟨X,J,hXC,_,hXn,hXB,hJ,hJC,hX,hcases⟩
  have hr := (D.normalizer_action_layer_sqtk h).stronglyQuasithin
  have hXnormal : X.Normal := by
    rcases hcases with ⟨_,_,hmove⟩ | ⟨hXJ,hJn,_⟩
    · rw [hX]
      exact (moved_component_orbit_normal_pair hr J A hJ hmove).1
    · exact hXJ.symm ▸ hJn
  refine ⟨X,J,hXnormal,hXC,hXn,hXB,hJ,hJC,hX,?_⟩
  rcases hcases with ⟨_,⟨r,hrpos,⟨ej⟩⟩,hmove⟩ | hcase
  · left
    obtain ⟨_,a,ha,han,hi,hpair,_⟩ := moved_component_orbit_normal_pair hr J A hJ hmove
    let : IsSimpleGroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) :=
      (BenderSuzuki.External.huppert_blackburn_XI_3_6 r hrpos).1
    let : IsSimpleGroup J := ej.isSimpleGroup
    let := hJ.2
    have hz : center J = ⊥ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
        (fun hh => Group.IsPerfect.not_isMulCommutative J (center_eq_top_iff.mp hh))
    obtain ⟨d,hd,hzpair⟩ := centerless_component_pair_coordinates J hJ hz a han
    let eX : (J ⊔ J.map (MulAut.conj a).toMonoidHom : Subgroup (internalActionImage M U hn)) ≃* X :=
      MulEquiv.subgroupCongr (hX.trans hpair).symm
    have hzX : center X = ⊥ := by
      rw [hX,hpair]
      exact hzpair
    exact ⟨r,hrpos,⟨ej⟩,a,ha,han,hi,hX.trans hpair,d.trans eX,hd,hzX⟩
  · exact Or.inr hcase

/-- Every normal component-orbit support supplied by the preceding theorem
moves both literal halves and has central restricted kernels. Centerless
support acts faithfully. No irreducibility of a whole type is assumed. -/
theorem normalizer_normal_support_on_isotypic_pair
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let f := internalHom M U hn
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map f
    let C := centralizer (K : Set (internalActionImage M U hn))
    let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component → A ∈ QhatStar ρ →
      ∀ X J : Subgroup (internalActionImage M U hn),
        X.Normal → X ≤ C → X ≠ ⊥ → IsComponent (internalActionImage M U hn) J →
        X = componentOrbit J A →
        ∃ t : M, t.val ∈ (T : Subgroup G) ∧ t.val ∉ normalizer (V : Set G) ∧
          IsCompl I (I.map (ρ (f t))) ∧
          A ≤ subspaceStabilizer ρ I ∧ A ≤ subspaceStabilizer ρ (I.map (ρ (f t))) ∧
          ∃ hXI : X ≤ subspaceStabilizer ρ I,
          ∃ hXIt : X ≤ subspaceStabilizer ρ (I.map (ρ (f t))),
            (¬ I ≤ fixedSpace ρ X) ∧ (¬ I.map (ρ (f t)) ≤ fixedSpace ρ X) ∧
            (subgroupActionHom ρ I X hXI).ker ≤ center X ∧
            (subgroupActionHom ρ (I.map (ρ (f t))) X hXIt).ker ≤ center X ∧
            (center X = ⊥ →
              Function.Injective (subgroupActionHom ρ I X hXI) ∧
              Function.Injective (subgroupActionHom ρ (I.map (ρ (f t))) X hXIt)) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let f := internalHom M U hn
  let ρ := UniqueFactor.imageRepresentation M U hn
  let K := (L.subgroupOf M).map f
  let C := centralizer (K : Set (internalActionImage M U hn))
  let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  dsimp only
  intro A hAS hA X J hXnormal hXC hXn hJ hX
  let := hXnormal
  have hp := D.normalizer_starred_isotypic_pair_of_moved_of_many h hmany hc hm hne
  let t := hp.choose
  have ht := hp.choose_spec.1
  have hnt := hp.choose_spec.2.1
  have hcompl := hp.choose_spec.2.2.1
  have hdim := hp.choose_spec.2.2.2.2.1
  have hperm := hp.choose_spec.2.2.2.2.2.1
  have hAI := D.normalizer_starred_stabilizes_isotypic_of_moved_of_many
    h hmany hc hm hne A hAS hA
  have hneq : I ≠ I.map (ρ (f t)) := by
    intro he
    have hd := hcompl.disjoint
    change Disjoint I (I.map (ρ (f t))) at hd
    rw [←he] at hd
    have hz : I = ⊥ := disjoint_self.mp hd
    change 2 < Module.finrank (ZMod 2) I at hdim
    rw [hz,finrank_bot] at hdim
    omega
  have hXI : X ≤ subspaceStabilizer ρ I := by
    apply le_subspaceStabilizer
    intro x hx v hv
    obtain ⟨g,rfl⟩ := (UniqueFactor.actionHom M U hn).rangeRestrict_surjective x
    have he := typePart_map_eq_of_image_centralizer ρ f (L.subgroupOf M)
      (internalSubrepresentation hn D.normalizes) g (hXC hx)
    change I.map (ρ (f g)) = I at he
    rw [←he]
    exact Submodule.mem_map.mpr ⟨v,hv,rfl⟩
  have hpairs := normal_component_orbit_pair_actions ρ
    (UniqueFactor.imageRepresentation_injective M U hn) X J A hJ hX hXn
    I (f t) hcompl hneq hperm hAI hXI
  refine ⟨t,ht,hnt,hcompl,hAI,hpairs.1,hXI,?_⟩
  exact hpairs.2

/-- Every surviving starred support is normal and moves both literal isotypic
halves. The Suzuki branch is an actual pair of conjugate components, with
multiplication coordinates and faithful restricted action on each half. -/
theorem normalizer_starred_normal_support_on_pair_of_odd_linearThree
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G))
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let f := internalHom M U hn
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map f
    let C := centralizer (K : Set (internalActionImage M U hn))
    let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component → A ∈ QhatStar ρ →
      ∃ t : M, t.val ∈ (T : Subgroup G) ∧ t.val ∉ normalizer (V : Set G) ∧
        IsCompl I (I.map (ρ (f t))) ∧
        A ≤ subspaceStabilizer ρ I ∧ A ≤ subspaceStabilizer ρ (I.map (ρ (f t))) ∧
        ∃ X J : Subgroup (internalActionImage M U hn),
          X.Normal ∧ X ≤ C ∧ X ≠ ⊥ ∧ ⁅X,A ⊓ C⁆ = X ∧
          IsComponent (internalActionImage M U hn) J ∧ J ≤ C ∧ X = componentOrbit J A ∧
          ∃ hXI : X ≤ subspaceStabilizer ρ I,
          ∃ hXIt : X ≤ subspaceStabilizer ρ (I.map (ρ (f t))),
            (¬ I ≤ fixedSpace ρ X) ∧ (¬ I.map (ρ (f t)) ≤ fixedSpace ρ X) ∧
            (subgroupActionHom ρ I X hXI).ker ≤ center X ∧
            (subgroupActionHom ρ (I.map (ρ (f t))) X hXIt).ker ≤ center X ∧
            ((∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) ∧
                ∃ a ∈ A, a ∉ normalizer (J : Set (internalActionImage M U hn)) ∧
                  (normalizer (J : Set (internalActionImage M U hn))).index = 2 ∧
                  X = J ⊔ J.map (MulAut.conj a).toMonoidHom ∧
                  ∃ d : J × J ≃* X,
                    (∀ x y : J, (d (x,y) : internalActionImage M U hn) =
                      x.val * (a * y.val * a⁻¹)) ∧
                    Function.Injective (subgroupActionHom ρ I X hXI) ∧
                    Function.Injective (subgroupActionHom ρ (I.map (ρ (f t))) X hXIt)) ∨
              (X = J ∧ J.Normal ∧ primeRank 3 J = 1 ∧ pCore 3 C = ⊥)) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let f := internalHom M U hn
  let ρ := UniqueFactor.imageRepresentation M U hn
  let K := (L.subgroupOf M).map f
  let C := centralizer (K : Set (internalActionImage M U hn))
  let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  dsimp only
  intro A hAS hA
  have hs := D.normalizer_starred_normal_support_of_odd_linearThree
    h hmany hc hm hne F ho e A hAS hA
  rcases hs with ⟨X,J,hXN,hXC,hXn,hXB,hJ,hJC,hX,hcases⟩
  have hp := D.normalizer_normal_support_on_isotypic_pair
    h hmany hc hm hne A hAS hA X J hXN hXC hXn hJ hX
  rcases hp with ⟨t,ht,hnt,hcompl,hAI,hAIt,hXI,hXIt,hIm,hItm,hker,hkert,hfaith⟩
  refine ⟨t,ht,hnt,hcompl,hAI,hAIt,X,J,hXN,hXC,hXn,hXB,hJ,hJC,hX,
    hXI,hXIt,hIm,hItm,hker,hkert,?_⟩
  rcases hcases with ⟨r,hr,ej,a,ha,han,hi,hpair,d,hd,hz⟩ | hcase
  · exact Or.inl ⟨r,hr,ej,a,ha,han,hi,hpair,d,hd,(hfaith hz).1,(hfaith hz).2⟩
  · exact Or.inr hcase

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
