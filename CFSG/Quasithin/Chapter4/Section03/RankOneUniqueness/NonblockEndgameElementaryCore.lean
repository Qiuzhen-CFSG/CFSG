module
public import Theory.GroupTheory.PGroup.OmegaCoprimeAction
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameUnitarySource
public import Theory.Representation.PSL3Four.NormalCoreDegree
public import Theory.Representation.BinaryConjugationSection.QuotientSection
public import Theory.Representation.BinaryConjugationSection.ConjugationCoordinates
public import Theory.Representation.BinaryConjugationSection.ActionKernel
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameCoreSections

/-!
# Central elementary subgroups in the original linear-four component core

Every elementary subgroup of O₂(K_Z) preserved by the original cubic
extension is centralized by K_Z. A nontrivial perfect component action
would survive on an irreducible section. The source rank bound puts that
section in dimension at most twelve. Clifford restriction and the marked
PSL₃(4) quotient then force dimension nine, contradicting the original
cubic parity theorem. Both endpoints of every selected section are pulled
back through the same conjugation coordinates.

In particular K_Z centralizes Ω₁(Z(O₂(K_Z))). If O₂(K_Z) were abelian,
its first omega would detect its ambient centralizer, contradicting
characteristic two. The source-cubic application supplies these conclusions
without selecting any extension of the adjoint module.

The nonabelian core layers, strict secondary-core enlargement and original
MS construction remain with qt-d-1222-rankone-uniqueness-nonblock. These
results do not yet prove the terminal contradiction.
Source: Aschbacher--Smith, conclusion of original 4.3.2, pp.618--619;
C.1.35 for the source rank bound, and Clifford theory for restriction.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {d : MSData c 2}
namespace RootCoordinates
variable (m : RootCoordinates d)
  (s : SecondarySourceData c 2) (D : Chapter12.Section02.ChosenModule T L V)
  (X : Subgroup G) (hX : Nat.card X = 3) (hXK : X ≤ (K c).coreCenterIn 2)
  (hXr : X ≤ rootNormalizer c) (hfix : Q c ⊓ centralizer (X : Set G) = ⊥)
  (hcomm : ⁅secondary c,X⁆ ≤ (secondary c).pCoreIn 2)
  (e : (s.component ⧸ pCore 2 s.component) ≃* Matrix.PSL3Four.PSL)

omit [Finite G] in
include hXr in
private theorem component_extension_normal :
    ((s.component.map (rootNormalizer c).subtype).subgroupOf
      (s.component.map (rootNormalizer c).subtype ⊔ X)).Normal := by
  let := s.normal
  apply normal_subgroupOf_of_le_normalizer
  have hh := s.component.le_normalizer_map (rootNormalizer c).subtype
  have hn : rootNormalizer c ≤ normalizer (s.component.map (rootNormalizer c).subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  exact (sup_le (map_subtype_le _) hXr).trans hn

include m D hX hXK hXr hfix hcomm e

/-- An irreducible section of an invariant elementary core subgroup has trivial component action. -/
theorem elementary_core_section_component_kernel
    (A B : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (s.component.map (rootNormalizer c).subtype ⊔ X : Subgroup G) W)
    (a : BinaryConjugationSection (s.component.map (rootNormalizer c).subtype ⊔ X) A B ρ)
    [ρ.IsIrreducible] :
    (s.component.map (rootNormalizer c).subtype).subgroupOf
      (s.component.map (rootNormalizer c).subtype ⊔ X) ≤ ρ.ker := by
  let M := s.component.map (rootNormalizer c).subtype
  let E := M ⊔ X
  let H := M.subgroupOf E
  let : H.Normal := component_extension_normal s X hXr
  let : Finite W := Finite.of_surjective (fun x => (a.coordinates x).toAdd) a.onto
  let : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  let f : H ≃* s.component := (subgroupOfEquivOfLe (show M ≤ E from le_sup_left)).trans
    (s.component.equivMapOfInjective (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective).symm
  let eq : (H ⧸ pCore 2 H) ≃* Matrix.PSL3Four.PSL :=
    (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e
  by_contra hnt
  have hc : ((pCore 2 s.component).map s.component.subtype).map
      (rootNormalizer c).subtype ≤ R₂ c := by
    change (s.component.pCoreIn 2).map (rootNormalizer c).subtype ≤ R₂ c
    rw [map_pCoreIn_of_injective 2 s.component (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective]
    exact s.component_core_le D
  have hd := d.elementary_section_card_le (by decide) A
    (hA.trans (hc.trans (radical_le_sylow c))) (fun x => (a.coordinates x).toAdd) a.onto
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hd
  have hdim : Module.finrank (ZMod 2) W ≤ 12 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hd
  have h9 := Representation.PSL3Four.normal_core_simple_degree H eq ρ hdim hnt
  apply m.component_section_not_odd_degree s D X hX hXK hfix hcomm A B hA
    a.kernel_le a.normalized a.kernel_normalized (show Odd 9 by decide)
  rw [a.relIndex_eq_card,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,h9]


/-- The component fixes every elementary source section, without assuming
that the whole extension action is irreducible. -/
theorem elementary_core_action_component_kernel
    (A B : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (s.component.map (rootNormalizer c).subtype ⊔ X : Subgroup G) W)
    (a : BinaryConjugationSection (s.component.map (rootNormalizer c).subtype ⊔ X) A B ρ) :
    (s.component.map (rootNormalizer c).subtype).subgroupOf
      (s.component.map (rootNormalizer c).subtype ⊔ X) ≤ ρ.ker := by
  let M := s.component.map (rootNormalizer c).subtype
  let E := M ⊔ X
  let H := M.subgroupOf E
  let : Finite W := Finite.of_surjective (fun x => (a.coordinates x).toAdd) a.onto
  let : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  by_contra hn
  let : Group.IsPerfect s.component := s.isComponent.perfect
  let f : H ≃* s.component := (subgroupOfEquivOfLe (show M ≤ E from le_sup_left)).trans
    (s.component.equivMapOfInjective (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective).symm
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective
    (f := f.symm.toMonoidHom) f.symm.surjective
  obtain ⟨P,N,hi,hnt⟩ :=
    Representation.QuadraticFourGroup.exists_irreducible_section_surviving_perfect (ρ := ρ) H hn
  let aa := a.invariantSection P
  let bb := aa.quotientSection N
  let : IsElementaryAbelian 2 (a.invariantPreimage P) :=
    IsElementaryAbelian.of_injective (inclusion (a.invariantPreimage_le P))
      (inclusion_injective (a.invariantPreimage_le P))
  let : N.quotientRepresentation.IsIrreducible := hi
  exact hnt (m.elementary_core_section_component_kernel s D X hX hXK hXr hfix hcomm e
    _ _ ((a.invariantPreimage_le P).trans hA) N.quotientRepresentation bb)

/-- Every invariant elementary subgroup of the actual component core is central. -/
theorem elementary_core_centralizes_component
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    (hN : s.component.map (rootNormalizer c).subtype ⊔ X ≤ normalizer (A : Set G)) :
    s.component.map (rootNormalizer c).subtype ≤ centralizer (A : Set G) := by
  let M := s.component.map (rootNormalizer c).subtype
  let E := M ⊔ X
  let H := M.subgroupOf E
  have hAE : A ≤ E := hA.trans ((map_mono (map_subtype_le _)).trans le_sup_left)
  obtain ⟨ρ,⟨a⟩⟩ := BinaryConjugationSection.exists_conjugation_coordinates E A ⊥
    hAE hN bot_le (by rw [(⊥ : Subgroup G).normalizer_eq_top]; exact le_top)
  have hker : H ≤ ρ.ker := m.elementary_core_action_component_kernel s D X
    hX hXK hXr hfix hcomm e A ⊥ hA ρ a
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  apply commutator_le.mpr
  intro g hg x hx
  exact (a.action_mem_ker_iff (⟨g,show g ∈ E from mem_sup_left hg⟩ : E)).mp
    (hker hg) x hx


/-- The component centralizes the central omega of its actual embedded core. -/
theorem component_centralizes_core_centralOmega :
    s.component.map (rootNormalizer c).subtype ≤
      centralizer (omegaCenterIn ((s.component.map (rootNormalizer c).subtype).pCoreIn 2) : Set G) := by
  let M := s.component.map (rootNormalizer c).subtype
  have hn : M ⊔ X ≤ normalizer (M : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show M ≤ M ⊔ X from le_sup_left)).mp
      (component_extension_normal s X hXr)
  have hcore : M.pCoreIn 2 = ((pCore 2 s.component).map s.component.subtype).map
      (rootNormalizer c).subtype := by
    rw [←map_pCoreIn_of_injective 2 s.component (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective]
    rfl
  exact m.elementary_core_centralizes_component s D X hX hXK hXr hfix hcomm e _
    ((map_subtype_le _).trans hcore.le)
    ((hn.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))).trans
      (normalizer_le_normalizer_omegaCenterIn _))

/-- An abelian component core is impossible under the original characteristic-two hypotheses. -/
theorem component_core_not_abelian
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ¬ IsMulCommutative (pCore 2 s.component) := by
  intro hab
  let := hab
  let M := s.component.map (rootNormalizer c).subtype
  let P := M.pCoreIn 2
  have hP : P = ((pCore 2 s.component).map s.component.subtype).map
      (rootNormalizer c).subtype := by
    dsimp only [P,M]
    rw [←map_pCoreIn_of_injective 2 s.component (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective]
    rfl
  have hc := m.component_centralizes_core_centralOmega s D X hX hXK hXr hfix hcomm e
  have hself : centralizer (pCore 2 s.component : Set s.component) ≤ pCore 2 s.component :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2
      (s.component.equivMapOfInjective (rootNormalizer c).subtype
        (rootNormalizer c).subtype_injective)).mpr
      (SourceEndgame.unitaryFive_component_core_selfCentralizing s D h)
  have hsmall := OmegaAction.centralizer_omegaOne_pCore_le hself
  have htop : pCore 2 s.component = ⊤ := by
    apply top_unique
    intro g _
    apply hsmall
    rintro q ⟨q,hq,rfl⟩
    have hqA : (((q : s.component) : rootNormalizer c) : G) ∈ omegaCenterIn P := by
      apply (mem_omegaCenterIn_iff P _).mpr
      refine ⟨?_,?_,?_⟩
      · rw [hP]
        exact mem_map_of_mem _ (mem_map_of_mem _ q.property)
      · intro r hr
        rw [hP] at hr
        obtain ⟨r,⟨r,hr,rfl⟩,rfl⟩ := hr
        exact congrArg (fun z : pCore 2 s.component => (((z : s.component) : rootNormalizer c) : G))
          (mul_comm ⟨r,hr⟩ q)
      · let : IsElementaryAbelian 2 (omega (pCore 2 s.component) (p := 2) 1) :=
          IsElementaryAbelian.omega₁_of_isMulCommutative _
        have hp : q ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian q hq
        exact congrArg (fun z : pCore 2 s.component => (((z : s.component) : rootNormalizer c) : G)) hp
    have hh := hc (mem_map_of_mem _ g.property) _ hqA
    apply Subtype.ext
    apply Subtype.ext
    exact hh
  have hp : IsPGroup 2 s.component := by
    have hp := (pCore_isPGroup (p := 2) (G := s.component))
    rw [htop] at hp
    exact hp.of_surjective (topEquiv (G := s.component)).toMonoidHom
      (topEquiv (G := s.component)).surjective
  let := hp.isNilpotent
  exact s.isComponent.not_isSolvable inferInstance

end RootCoordinates

/-- The source cubic supplies the elementary-core restrictions without a
chosen cubic or a representation-recognition premise. The earlier MS and
secondary constructions remain the enclosing source owner's obligations. -/
theorem MSData.linearFour_core_constraints (d : MSData c 2) (m : RootCoordinates d)
    (s : SecondarySourceData c 2) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (e : (s.component ⧸ pCore 2 s.component) ≃* Matrix.PSL3Four.PSL) :
    ¬ IsMulCommutative (pCore 2 s.component) ∧
      s.component.map (rootNormalizer c).subtype ≤
        Subgroup.centralizer (omegaCenterIn ((s.component.map (rootNormalizer c).subtype).pCoreIn 2) : Set G) ∧
      ∀ A : Subgroup G, IsElementaryAbelian 2 A →
        A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype →
        rootNormalizer c ≤ normalizer (A : Set G) →
        s.component.map (rootNormalizer c).subtype ≤ Subgroup.centralizer (A : Set G) := by
  obtain ⟨X,hX,hXK,hr,hfix,_,_,_,hcomm,_,_⟩ := d.exists_source_cubic_root D
  refine ⟨m.component_core_not_abelian s D X hX hXK hr hfix hcomm e h,
    m.component_centralizes_core_centralOmega s D X hX hXK hr hfix hcomm e,?_⟩
  intro A ha hA hn
  let := ha
  exact m.elementary_core_centralizes_component s D X hX hXK hr hfix hcomm e A hA
    ((sup_le (map_subtype_le _) hr).trans hn)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
