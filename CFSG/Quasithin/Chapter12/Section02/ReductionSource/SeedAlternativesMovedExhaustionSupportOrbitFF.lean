module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionSupportSections
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSupportOrbitFF

/-!
# FF support orbits in the literal chosen normalizer action

In the normal quasisimple support branch, select the existing homogeneous
Irr⁺ section inside the original isotypic half. Its orbit under the Sylow
half stabilizer and its exchanged copy are disjoint. Their pointwise kernels
on the original starred actor both equal that actor's centralizer on the
support. D.2.5 and the shared displacement budget give an offender on one
orbit. Literal conjugation supplies an explicit offender in the original
half stabilizer, eliminating the earlier centralizer alternative. The same
actor gives an FF offender on the literal central orbit section through its
original kernel quotient, as needed by B.5.1.

The last theorem applies this to every starred actor in the surviving
odd-degree natural SL₃ branch. It retains the actual Suzuki pair alternative
and all source hypotheses. The FF conclusion concerns the homogeneous orbit;
extracting and classifying its Irr⁺ constituent, the Suzuki pair exclusion,
component movement, multiplicity, other model branches and Source325
assembly remain with qt-baumann-fsu.
Source: Aschbacher--Smith D.3.5 and D.3.17, printed pp.195--196,203,
applied in3.2.5, p.580; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- On a normal quasisimple support the two homogeneous orbits have the
same literal actor kernel. The original starred actor offends on one of
them, and conjugation gives an FF orbit in the original half. -/
theorem normalizer_normal_quasisimple_support_orbit_ff
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    let := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let f := internalHom M U hn
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map f
    let C := centralizer (K : Set (internalActionImage M U hn))
    let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
    let S := (internalSylow T M U hn D.sylow_normalizes_component : Subgroup (internalActionImage M U hn))
    let P := S ⊓ subspaceStabilizer ρ I
    ∀ A : Subgroup (internalActionImage M U hn), A ≤ S → A ∈ QhatStar ρ →
      ∀ X : Subgroup (internalActionImage M U hn),
        X.Normal → IsQuasisimple X → X ≤ C → ⁅X,A ⊓ C⁆ = X →
        ∃ (t : M) (R : Submodule (ZMod 2) (Additive U)),
          t.val ∈ (T : Subgroup G) ∧ t.val ∉ normalizer (V : Set G) ∧
          R ≤ I ∧ IsIrrPlusWith ρ X P R ∧
          let Y := orbitSpan ρ P R
          Y ≤ I ∧ Disjoint Y (Y.map (ρ (f t))) ∧
          subspaceKernel ρ Y A = A ⊓ centralizer (X : Set _) ∧
          subspaceKernel ρ (Y.map (ρ (f t))) A = A ⊓ centralizer (X : Set _) ∧
          (IsOffender (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y A) ∨
            IsOffender (subspaceImageRepresentation ρ (Y.map (ρ (f t))))
              (restrictedSubgroup ρ (Y.map (ρ (f t))) A)) ∧
          (∃ B : Subgroup (internalActionImage M U hn), B ≤ P ∧ IsElementaryAbelian 2 B ∧
            IsOffender (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y B)) ∧
          IsFFModule (subspaceImageRepresentation ρ Y) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let f := internalHom M U hn
  let ρ := UniqueFactor.imageRepresentation M U hn
  let K := (L.subgroupOf M).map f
  let C := centralizer (K : Set (internalActionImage M U hn))
  let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
  let S := (internalSylow T M U hn D.sylow_normalizes_component : Subgroup (internalActionImage M U hn))
  let P := S ⊓ subspaceStabilizer ρ I
  dsimp only
  intro A hAS hA X hXN hqs hXC hXB
  let := hXN
  let := hqs
  have hX : IsComponent (internalActionImage M U hn) X := ⟨hXN.isSubnormal,hqs⟩
  have hXX : X = componentOrbit X A := by
    apply le_antisymm (le_componentOrbit X A)
    apply iSup_le
    intro a
    rintro _ ⟨x,hx,rfl⟩
    exact hXN.conj_mem x hx a.val
  obtain ⟨t,ht,hnt,hcompl,_,_,_,R,hRI,hR,_,_,_,_,_,_⟩ :=
    D.normalizer_normal_support_sections h hmany hc hm hne A hAS hA
      X X hXN hXC hX.isCComponent.ne_bot hXB hX hXX
  change IsCompl I (I.map (ρ (f t))) at hcompl
  have hneq : I ≠ I.map (ρ (f t)) := by
    intro he
    have hz : I = ⊥ := disjoint_self.mp (by simpa only [←he] using hcompl.disjoint)
    exact hR.isIrrPlus.ne_bot ρ (bot_unique (hRI.trans hz.le))
  obtain ⟨t₀,_,_,_,_,_,hperm,_⟩ :=
    D.normalizer_starred_isotypic_pair_of_moved_of_many h hmany hc hm hne
  change ∀ g, I.map (ρ g) = I ∨ I.map (ρ g) = I.map (ρ (f t₀)) at hperm
  have he := (hperm (f t)).resolve_left (Ne.symm hneq)
  have hp : ∀ g : internalActionImage M U hn,
      I.map (ρ g) = I ∨ I.map (ρ g) = I.map (ρ (f t)) := by
    intro g
    simpa only [he] using hperm g
  have hSP : S ≤ normalizer (P : Set _) :=
    permuted_pair_normalizes_half_stabilizer ρ I (f t) hneq hp S
  have hAI := D.normalizer_starred_stabilizes_isotypic_of_moved_of_many
    h hmany hc hm hne A hAS hA
  have hAP : A ≤ P := le_inf hAS hAI
  have hYI : orbitSpan ρ P R ≤ I := orbitSpan_le ρ hRI inf_le_right
  have hd := hcompl.disjoint.mono hYI (Submodule.map_mono hYI)
  have htS : f t ∈ S := mem_map_of_mem f
    (show t ∈ (T : Subgroup G).subgroupOf M from ht)
  have hff := homogeneous_support_pair_orbit_ff ρ X S P A (A ⊓ C)
    (internalSylow T M U hn D.sylow_normalizes_component).isPGroup'
    inf_le_left hSP hAP inf_le_left hXB hA R hR (f t) htS hd
  exact ⟨t,R,ht,hnt,hRI,hR,hYI,hd,hff⟩

/-- Every starred actor in the surviving odd-degree SL₃ case either exchanges
an actual Suzuki component pair or gives an FF homogeneous orbit for a normal
three-rank-one support. The extra centralizer alternative has been removed. -/
theorem normalizer_support_ff_or_suzuki_of_odd_linearThree
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G))
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
    let := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let f := internalHom M U hn
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map f
    let C := centralizer (K : Set (internalActionImage M U hn))
    let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
    let S := (internalSylow T M U hn D.sylow_normalizes_component : Subgroup (internalActionImage M U hn))
    let P := S ⊓ subspaceStabilizer ρ I
    ∀ A : Subgroup (internalActionImage M U hn), A ≤ S → A ∈ QhatStar ρ →
      ∃ X J : Subgroup (internalActionImage M U hn),
        X.Normal ∧ X ≤ C ∧ X ≠ ⊥ ∧ ⁅X,A ⊓ C⁆ = X ∧
        IsComponent (internalActionImage M U hn) J ∧ J ≤ C ∧ X = componentOrbit J A ∧
        ((∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) ∧
            ∃ a ∈ A, a ∉ normalizer (J : Set (internalActionImage M U hn)) ∧
              (normalizer (J : Set (internalActionImage M U hn))).index = 2 ∧
              X = J ⊔ J.map (MulAut.conj a).toMonoidHom) ∨
          (X = J ∧ J.Normal ∧ primeRank 3 J = 1 ∧ pCore 3 C = ⊥ ∧
            ∃ (t : M) (R : Submodule (ZMod 2) (Additive U)),
              t.val ∈ (T : Subgroup G) ∧ t.val ∉ normalizer (V : Set G) ∧
              R ≤ I ∧ IsIrrPlusWith ρ X P R ∧
              let Y := orbitSpan ρ P R
              Y ≤ I ∧ Disjoint Y (Y.map (ρ (f t))) ∧
              subspaceKernel ρ Y A = A ⊓ centralizer (X : Set _) ∧
              subspaceKernel ρ (Y.map (ρ (f t))) A = A ⊓ centralizer (X : Set _) ∧
              (IsOffender (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y A) ∨
                IsOffender (subspaceImageRepresentation ρ (Y.map (ρ (f t))))
                  (restrictedSubgroup ρ (Y.map (ρ (f t))) A)) ∧
              (∃ B : Subgroup (internalActionImage M U hn), B ≤ P ∧ IsElementaryAbelian 2 B ∧
                IsOffender (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y B)) ∧
              IsFFModule (subspaceImageRepresentation ρ Y))) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  dsimp only
  intro A hAS hA
  obtain ⟨X,J,hXN,hXC,hXn,hXB,hJ,hJC,hX,hcases⟩ :=
    D.normalizer_starred_normal_support_of_odd_linearThree h hmany hc hm hne F ho e A hAS hA
  refine ⟨X,J,hXN,hXC,hXn,hXB,hJ,hJC,hX,?_⟩
  rcases hcases with ⟨r,hr,ej,a,ha,han,hindex,hpair,_⟩ | ⟨he,hJN,hr,hcore⟩
  · exact Or.inl ⟨r,hr,ej,a,ha,han,hindex,hpair⟩
  · right
    refine ⟨he,hJN,hr,hcore,?_⟩
    exact D.normalizer_normal_quasisimple_support_orbit_ff h hmany hc hm hne
      A hAS hA X hXN (he.symm ▸ hJ.2) hXC hXB


/-- The selected homogeneous support orbit gives an actual FF offender on
its central section, using the original support extension and kernel projection. -/
theorem normalizer_normal_quasisimple_support_ff_section
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    let := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let f := internalHom M U hn
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map f
    let C := centralizer (K : Set (internalActionImage M U hn))
    let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
    let S := (internalSylow T M U hn D.sylow_normalizes_component : Subgroup (internalActionImage M U hn))
    let P := S ⊓ subspaceStabilizer ρ I
    ∀ A : Subgroup (internalActionImage M U hn), A ≤ S → A ∈ QhatStar ρ →
      ∀ X : Subgroup (internalActionImage M U hn),
        X.Normal → IsQuasisimple X → X ≤ C → ⁅X,A ⊓ C⁆ = X →
        ∃ (t : M) (R : Submodule (ZMod 2) (Additive U)),
          t.val ∈ (T : Subgroup G) ∧ t.val ∉ normalizer (V : Set G) ∧ R ≤ I ∧
          ∃ hR : IsIrrPlusWith ρ X P R,
            let σ := orbitSectionRepresentation ρ hR
            ∃ B : Subgroup (internalActionImage M U hn), B ≤ P ∧ IsElementaryAbelian 2 B ∧
              IsOffender (KernelQuotient.action σ)
                ((B.subgroupOf (X ⊔ P)).map (KernelQuotient.projection σ)) ∧
              IsFFModule (KernelQuotient.action σ) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro hU M U hn f ρ K C I S P A hAS hA X hXN hqs hXC hXB
  let := hqs
  obtain ⟨t,R,ht,hnt,hRI,hR,_,_,_,_,_,⟨B,hBP,hB,hoff⟩,_⟩ :=
    D.normalizer_normal_quasisimple_support_orbit_ff h hmany hc hm hne
      A hAS hA X hXN hqs hXC hXB
  have hsection := homogeneous_support_orbit_section_offender ρ X P B
    ((internalSylow T M U hn D.sylow_normalizes_component).isPGroup'.to_le inf_le_left)
    hBP hB R hR hoff
  exact ⟨t,R,ht,hnt,hRI,hR,B,hBP,hB,hsection,_,hsection⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
