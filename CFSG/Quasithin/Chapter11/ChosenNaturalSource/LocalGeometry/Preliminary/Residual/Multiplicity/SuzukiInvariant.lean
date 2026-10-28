module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.Multiplicity.SuzukiComponent
public import Theory.GroupTheory.CommutingThreePrimeRank
public import Theory.GroupTheory.GeneralizedFitting.ComponentLayerStructure
public import Theory.GroupTheory.GeneralizedFitting.InvolutionGenerated
public import Theory.SpecificGroups.Suzuki.CyclicOuter
public import Theory.SpecificGroups.SL3.InvolutionBlock
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Theory.Representation.BinaryOffender.Homogeneous.Existence
/-!
# An invariant constituent of the actual moved Suzuki orbit

The original normalizer is SQTK. Theorem A gives the same odd-rank bounds
on the semisimple layer of its faithful full-module image; no inheritance
of SQTK by arbitrary quotients is assumed. In even field degree the marked
full SL₃ component has order divisible by five. Two distinct conjugates
of the retained Suzuki component would commute, and their trivial centers
would make these three factors contribute five-rank at least three.
Consequently the actual actor normalizes that Suzuki component and its
whole actor orbit is exactly the component.

Homogeneous Irr⁺ selection now gives an actor-invariant member. Indeed,
Suzuki's outer automorphism group has odd order, so every elementary
binary actor induces inner automorphisms. Correcting the conjugating
operator by the corresponding component operator identifies the two
literal central quotient representations. Homogeneity then identifies
the original Irr⁺ members, before passing to any quotient.

The final application keeps the original component, orbit, centralizer
placement and commutator identity. It constructs a constituent of precisely
that orbit, invariant under the same starred actor, and applies the strict
ratio bound to its literal restricted actor. The Suzuki endpoint lower
bound on this chosen constituent and the faithful-actor cubic-containment
argument remain with qt-d-1222-natural-preliminary-source. Final chapter
assembly remains with qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith, A.1.42, p.32; Theorem A, pp.33--41; D.3.8--9,
pp.199--201, and K.3.6, p.457, used in 11.0.4, p.760, combined manuscript
of 1 March 2004. The central-quotient transport follows the same construction
as Homogeneous/NaturalFive, specialized here to inner automorphisms.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative ENNReal
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
namespace SuzukiSupport
open Representation.BinaryOffender.Homogeneous
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W)
private theorem same_central_images (X : Subgroup H)
    (I J : Submodule (ZMod 2) W)
    (hI : X ≤ subspaceStabilizer ρ I) (hJ : X ≤ subspaceStabilizer ρ J)
    (e : I ≃ₗ[ZMod 2] J)
    (he : ∀ (x : X) v, e ((invariantSubspace ρ X I hI).toRepresentation x v) =
      (invariantSubspace ρ X J hJ).toRepresentation x (e v)) :
    SameModule (quotientImage ρ X I hI) (quotientImage ρ X J hJ) := by
  let CI := (fixedSpace ρ X).comap I.subtype
  let CJ := (fixedSpace ρ X).comap J.subtype
  have hf : CI.map e.toLinearMap = CJ := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩ x
      have hv' : (invariantSubspace ρ X I hI).toRepresentation x v = v :=
        Subtype.ext (hv x)
      exact congrArg Subtype.val ((he x v).symm.trans (congrArg e hv'))
    · intro hw
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      intro x
      have hh : (invariantSubspace ρ X I hI).toRepresentation x (e.symm w) = e.symm w := by
        apply e.injective
        exact (he x (e.symm w)).trans (by
          rw [e.apply_symm_apply]
          exact Subtype.ext (hw x))
      exact congrArg (fun u : I => (u : W)) hh
  let qE := Submodule.Quotient.equiv CI CJ e hf
  have hq (x : X) (v : centralQuotient ρ X I) :
      qE (centralQuotientRepresentation ρ X I hI x v) =
        centralQuotientRepresentation ρ X J hJ x (qE v) := by
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      change Submodule.Quotient.mk (e ((invariantSubspace ρ X I hI).toRepresentation x v)) =
        Submodule.Quotient.mk ((invariantSubspace ρ X J hJ).toRepresentation x (e v))
      exact congrArg (fun u : J => (Submodule.Quotient.mk u : J ⧸ CJ)) (he x v)
  let ei := centralQuotientImageEquiv ρ X I
  let ej := centralQuotientImageEquiv ρ X J
  let E := ei.symm.trans (qE.trans ej)
  refine ⟨E, ?_⟩
  intro x v
  obtain ⟨w, rfl⟩ := ei.surjective v
  change ej (qE (ei.symm ((quotientImage ρ X I hI).toRepresentation x (ei w)))) =
    (quotientImage ρ X J hJ).toRepresentation x (ej (qE (ei.symm (ei w))))
  rw [← centralQuotientImageEquiv_equivariant, ei.symm_apply_apply,
    ei.symm_apply_apply, hq, centralQuotientImageEquiv_equivariant]

private theorem homogeneous_map_eq_of_twist
    {X T : Subgroup H} {I : Submodule (ZMod 2) W}
    (hI : IsIrrPlusWith ρ X T I) (t : T) (c : I ≃ₗ[ZMod 2] I)
    (hc : ∀ (x : X) v,
      c ((invariantSubspace ρ X I hI.invariant).toRepresentation x v) =
        (invariantSubspace ρ X I hI.invariant).toRepresentation
          (X.normalizerMonoidHom ⟨(t : H)⁻¹, hI.normalizes (T.inv_mem t.property)⟩ x) (c v)) :
    I.map (ρ t.val) = I := by
  let hJ := hI.isIrrPlus.map_normalizer ρ (hI.normalizes t.property)
  let e := c.trans (Submodule.equivMapOfInjective (ρ t.val) (ρ.apply_bijective t.val).1 I)
  apply hI.eq_of_isomorphic_conjugate ρ t
  apply same_central_images ρ X I (I.map (ρ t.val)) hI.invariant hJ.choose e
  intro x v
  apply Subtype.ext
  change ρ t.val (c ((invariantSubspace ρ X I hI.invariant).toRepresentation x v)).val =
    ρ x.val (ρ t.val (c v).val)
  rw [hc]
  change ρ t.val (ρ (X.normalizerMonoidHom
    ⟨(t : H)⁻¹, hI.normalizes (T.inv_mem t.property)⟩ x).val (c v).val) = _
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  simp only [inv_inv, ← Module.End.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel_left]


private theorem homogeneous_invariant_of_odd_outer [Finite H]
    {X A : Subgroup H} {I : Submodule (ZMod 2) W}
    (hI : IsIrrPlusWith ρ X A I) (hA : IsElementaryAbelian 2 A)
    (ho : Odd (Nat.card (MulAut.Outer X))) : A ≤ subspaceStabilizer ρ I := by
  let := hA
  intro a ha
  apply (subspace_map_eq_iff ρ I a).mp
  let t : A := ⟨a,ha⟩
  let n : normalizer (X : Set H) := ⟨a⁻¹,hI.normalizes (A.inv_mem ha)⟩
  have hn : n ^ 2 = 1 := by
    apply Subtype.ext
    change (a⁻¹) ^ 2 = 1
    rw [inv_pow,elemPow_eq_one_of_isElementaryAbelian a ha,inv_one]
  obtain ⟨u,hu⟩ := involution_inner_of_odd_outer ho (X.normalizerMonoidHom n)
    (by rw [← map_pow,hn,map_one])
  let σ := (invariantSubspace ρ X I hI.invariant).toRepresentation
  let c := LinearMap.GeneralLinearGroup.toLinearEquiv (σ.asGroupHom u)
  apply homogeneous_map_eq_of_twist ρ hI t c
  intro x v
  change σ u (σ x v) = σ (X.normalizerMonoidHom n x) (σ u v)
  rw [← hu]
  change σ u (σ x v) = σ (u * x * u⁻¹) (σ u v)
  simp only [← Module.End.mul_apply,← map_mul,mul_assoc,inv_mul_cancel,mul_one]

private theorem exists_invariant_irrPlus_of_suzuki [Finite H]
    [FiniteDimensional (ZMod 2) W] (hf : Function.Injective ρ)
    (X A : Subgroup H) [Group.IsPerfect X] (hX : X ≠ ⊥)
    (hA : IsElementaryAbelian 2 A) (hn : A ≤ normalizer (X : Set H))
    {r : ℕ} (hr : 0 < r)
    (e : X ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) :
    ∃ I : Submodule (ZMod 2) W, IsIrrPlus ρ X I ∧ A ≤ subspaceStabilizer ρ I := by
  let := hA
  obtain ⟨I,hI⟩ := Homogeneous.exists_isIrrPlusWith_of_faithful ρ hf X A hX hn
    (IsElementaryAbelian.isPGroup 2 A)
  have ho : Odd (Nat.card (MulAut.Outer X)) := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact BenderSuzuki.MatrixGroups.suzuki_odd_outer_index r (by omega)
  exact ⟨I,hI.isIrrPlus,homogeneous_invariant_of_odd_outer ρ hI hA ho⟩
end SuzukiSupport

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Theorem A controls the actual semisimple layer of the full action image. -/
theorem fullAction_layer_sqtk :
    letI := fullModule_elementary D S
    IsSQTK KnownSimple.IsKnownSimple (componentLayer (actionImage (fullModuleConjugation D S))) := by
  let := fullModule_elementary D S
  let ρ := fullModuleConjugation D S
  let E := componentLayer (actionImage ρ)
  have hs := normalizer_sqtk D S
  have hsec : ChapterA.Section02.IsSectionOf E (normalizer (L : Set G)) :=
    (ChapterA.Section02.IsSectionOf.subgroup E).ambient_surjective
      (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective
  exact ⟨ChapterA.Section02.TheoremA.stronglyQuasithin_section
    ChapterA.Section02.theoremA_knownSimple hs.stronglyQuasithin hs.isKGroup hsec
      componentLayer_idempotent, hsec.isKGroup hs.isKGroup⟩

/-- The determinant-corrected SL₂ block supplies five-divisibility in even degree. -/
theorem sl3_fullAction_component_five_dvd
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) :
    letI := fullModule_elementary D S
    5 ∣ Nat.card ((L.subgroupOf (normalizer (L : Set G))).map
      (actionHom (fullModuleConjugation D S))) := by
  let := fullModule_elementary D S
  obtain ⟨e,_⟩ := sl3_fullAction_component_marking D S m
  rw [Nat.card_congr e.toEquiv]
  let F := S.field.Carrier
  have hd : 5 ∣ Nat.card SL(2,F) := by
    rw [BenderSuzuki.External.huppert614_card_specialLinearGroup, S.field.card_eq]
    apply dvd_mul_of_dvd_right
    rw [← pow_mul]
    apply (by decide : 5 ∣ 2 ^ 4 - 1).trans
    apply Nat.pow_sub_one_dvd_pow_sub_one
    obtain ⟨k,hk⟩ := heven
    exact ⟨k,by omega⟩
  exact hd.trans (card_dvd_of_injective
    ((Matrix.SL3.blockEmbedding F).comp Matrix.SpecialLinearGroup.toGL)
    ((Matrix.SL3.blockEmbedding_injective F).comp Matrix.SpecialLinearGroup.toGL_injective))

private theorem components_eq_of_five_rank {H : Type*} [Group H] [Finite H]
    (K P Q : Subgroup H) (hK : IsComponent H K) (hP : IsComponent H P)
    (hQ : IsComponent H Q) (hr : primeRank 5 (componentLayer H) ≤ 2)
    (hPK : P ≤ centralizer (K : Set H)) (hQK : Q ≤ centralizer (K : Set H))
    (hPz : Nat.Coprime 5 (Nat.card (center P)))
    (hQz : Nat.Coprime 5 (Nat.card (center Q)))
    (hdK : 5 ∣ Nat.card K) (hdP : 5 ∣ Nat.card P) (hdQ : 5 ∣ Nat.card Q) : P = Q := by
  by_contra hn
  have hPQ : P ≤ centralizer (Q : Set H) :=
    commutator_eq_bot_iff_le_centralizer.mp (hP.commutator_eq_bot_of_ne hQ hn)
  let E := componentLayer H
  have hk : K ≤ E := le_sSup hK
  have hp : P ≤ E := le_sSup hP
  have hq : Q ≤ E := le_sSup hQ
  let eK := subgroupOfEquivOfLe hk
  let eP := subgroupOfEquivOfLe hp
  let eQ := subgroupOfEquivOfLe hq
  have hh := primeRank_three_of_commuting_of_centers_coprime (p := 5)
    (P.subgroupOf E) (Q.subgroupOf E) (K.subgroupOf E)
    (fun p hp q hq => Subtype.ext (hPQ hp q hq))
    (fun k hk p hp => Subtype.ext ((hPK hp k hk).symm))
    (fun k hk q hq => Subtype.ext ((hQK hq k hk).symm))
    (by rwa [Nat.card_congr (centerCongr eP).toEquiv])
    (by rwa [Nat.card_congr (centerCongr eQ).toEquiv])
    (by rwa [Nat.card_congr eP.toEquiv])
    (by rwa [Nat.card_congr eQ.toEquiv])
    (by rwa [Nat.card_congr eK.toEquiv])
  change 3 ≤ primeRank 5 (componentLayer H) at hh
  omega

/-- Five-rank excludes distinct actor-conjugates of the same retained Suzuki component. -/
theorem sl3_fullAction_suzuki_component_invariant
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let H := actionImage ρ
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∀ J A : Subgroup H, IsComponent H J →
      componentOrbit J A ≤ centralizer (K : Set H) → 5 ∣ Nat.card J →
      (∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)) →
      A ≤ normalizer (J : Set H) ∧ componentOrbit J A = J := by
  let := fullModule_elementary D S
  let ρ := fullModuleConjugation D S
  let H := actionImage ρ
  let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
  dsimp only
  intro J A hJ ho hdJ ⟨r,hr,⟨e⟩⟩
  let := hJ.2
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 r hr).1
  let : IsSimpleGroup J := e.isSimpleGroup
  have hz : center J = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun hh => Group.IsPerfect.not_isMulCommutative J (center_eq_top_iff.mp hh))
  have hPz : Nat.Coprime 5 (Nat.card (center J)) := by simp [hz]
  have hn : A ≤ normalizer (J : Set H) := by
    intro a ha
    apply mem_normalizer_iff_map_conj_eq.mpr
    let Q := J.map (MulAut.conj a).toMonoidHom
    let eqJ : J ≃* Q := J.equivMapOfInjective _ (MulAut.conj a).injective
    have hQle : Q ≤ componentOrbit J A :=
      (le_iSup (fun a : A => J.map (MulAut.conj (a : H)).toMonoidHom) ⟨a,ha⟩)
    apply (components_eq_of_five_rank K J Q
      (sl3_fullAction_component_isComponent D S m) hJ (hJ.map_conj a)
      ((fullAction_layer_sqtk D S).stronglyQuasithin 5 Nat.prime_five (by decide))
      ((le_componentOrbit J A).trans ho) (hQle.trans ho) hPz
      (by rwa [← Nat.card_congr (centerCongr eqJ).toEquiv])
      (sl3_fullAction_component_five_dvd D S m heven) hdJ
      (by rwa [← Nat.card_congr eqJ.toEquiv])).symm
  exact ⟨hn,le_antisymm (iSup_conjugates_le_of_le_normalizer J A J le_rfl hn)
    (le_componentOrbit J A)⟩

/-- Construct an invariant Irr⁺ member of the literal component orbit. -/
theorem sl3_fullAction_suzuki_orbit_invariant_constituent
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let τ := imageRepresentation ρ
    let H := actionImage ρ
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∀ J A : Subgroup H, IsComponent H J → IsElementaryAbelian 2 A →
      componentOrbit J A ≤ centralizer (K : Set H) → 5 ∣ Nat.card J →
      (∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)) →
      A ≤ normalizer (J : Set H) ∧ componentOrbit J A = J ∧
      ∃ I : Submodule (ZMod 2) (Additive (componentOrbit V (normalizer (L : Set G)))),
        IsIrrPlus τ (componentOrbit J A) I ∧ A ≤ subspaceStabilizer τ I := by
  let := fullModule_elementary D S
  dsimp only
  intro J A hJ hA ho hd he
  obtain ⟨hn,hX⟩ := sl3_fullAction_suzuki_component_invariant D S m heven J A hJ ho hd he
  let := hJ.2
  have hJne : J ≠ ⊥ := by
    intro heq
    simp [heq] at hd
  obtain ⟨r,hr,⟨e⟩⟩ := he
  obtain ⟨I,hI,hAI⟩ := SuzukiSupport.exists_invariant_irrPlus_of_suzuki _
    (imageRepresentation_injective _) J A hJne hA hn hr e
  exact ⟨hn,hX,I,hX.symm ▸ hI,hAI⟩

/-- The original nonfaithful actor supplies an actual invariant constituent with strict ratio below two. -/
theorem sl3_fullAction_starred_nonfaithful_invariant_constituent
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
        (∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)) ∧
        A ≤ normalizer (J : Set H) ∧ componentOrbit J A = J ∧
        ∃ I : Submodule (ZMod 2) (Additive (componentOrbit V (normalizer (L : Set G)))),
          IsIrrPlus τ (componentOrbit J A) I ∧ A ≤ subspaceStabilizer τ I ∧
          restrictedSubgroup τ I A ∈ ChapterD.Qhat (subspaceImageRepresentation τ I) ∧
          actionRatio (subspaceImageRepresentation τ I) (restrictedSubgroup τ I A) < cubicRatio τ ∧
          actionRatio (subspaceImageRepresentation τ I) (restrictedSubgroup τ I A) < 2 := by
  let := fullModule_elementary D S
  dsimp only
  intro A hA hn
  obtain ⟨hd,J,hJ,hm,ho,hcomm,h3,h5,he,_,hstrict⟩ :=
    sl3_fullAction_starred_nonfaithful_suzuki_component D S m heven A hA hn
  obtain ⟨hAJ,hX,I,hI,hAI⟩ := sl3_fullAction_suzuki_orbit_invariant_constituent
    D S m heven J A hJ hA.1.2.1.2 ho h5 he
  exact ⟨hd,J,hJ,hm,ho,hcomm,h3,h5,he,hAJ,hX,I,hI,hAI,hstrict I hI hAI⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
