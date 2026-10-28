module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.Inputs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.FFPassage.Sections
public import CFSG.Quasithin.ChapterB.Section01.IrreducibleInvariance
public import Theory.GroupTheory.CentralPChiefFactorsOddQuotient
public import Theory.GroupTheory.PResidual.Defs

/-!
# The cubic-cover FF passage

Cubic faithfulness supplies a genuine Irr⁺ member. Thompson replacement and
B.7.2(1) stabilize it under a minimal best offender. The ratio-one equality
case then makes it the whole module, after which B.4.5 supplies actual hexacode
coordinates. Those coordinates, rather than a dimension hypothesis, give six
binary dimensions. The same argument excludes every strong FF-offender.

The final theorems `irreducible_of_isFFModule` and `passage` discharge B.7.2(1)
using its proved source statement. Their only classification premise is the
universal specialized irreducible input; no homogeneous selection or
irreducibility of the original module is assumed. The argument works for every
finite overgroup with the stated centralizer control, so does not need the
additional source hypothesis that the component and a Sylow two-subgroup
generate the actor. The earlier conditional assembly interfaces are retained.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.7.2(1),
printed p.119; B.4.2(8) and B.4.5, pp.86–87; F.9.18(6), pp.325–326;
13.8.21(2), p.956.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender Atlas.Codes
open Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.FFPassage
universe u v
variable {D : Type u} [Group D] [Finite D]
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The genuine residual and chief-factor hypotheses of B.7.2 hold for the
actual cubic cover. Every nontrivial elementary two-subgroup has full
commutator with the component. -/
theorem invariance_hypotheses (L : Subgroup D) [L.Normal]
    (eL : L ≃* HexEvenAutomorphisms) (z : D) (hzorder : orderOf z = 3)
    (hcent : centralizer (L : Set D) ≤ zpowers z)
    (A : Subgroup D) (hA : IsElementaryTwo A) :
    L ≠ ⊥ ∧ pResidual 2 L = ⊤ ∧ HasCentralPChiefFactors 2 L ∧ ⁅L, A⁆ = L := by
  let : IsQuasisimple HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv eL.symm
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center L))
  have hLne : L ≠ ⊥ := (nontrivial_iff_ne_bot L).mp inferInstance
  have hr : pResidual 2 L = ⊤ := by
    apply (pResidual_eq_top_iff 2 L).mpr
    intro N hN hp
    let := hN
    have hsub : Subsingleton (L ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hp.isNilpotent
    apply top_unique
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  have hchief : HasCentralPChiefFactors 2 L :=
    hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient
      (⊥ : Subgroup L) (by simp)
      (IsQuasisimple.of_mulEquiv QuotientGroup.quotientBot.symm)
  refine ⟨hLne, hr, hchief, ?_⟩
  have hcomp : IsComponent D L := ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩
  rcases hcomp.commutator_dichotomy A with hb | he
  · exfalso
    have hAc : A ≤ zpowers z :=
      (commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm A L).trans hb)).trans hcent
    let : IsElementaryAbelian 2 A := hA.2
    apply hA.1
    apply bot_unique
    intro a ha
    have htwo : orderOf a ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian a ha)
    have hthree : orderOf a ∣ 3 := by
      have hh := (zpowers z).orderOf_dvd_natCard (hAc ha)
      rwa [Nat.card_zpowers, hzorder] at hh
    have ho : orderOf a = 1 := Nat.dvd_one.mp (by
      have hh := Nat.dvd_gcd htwo hthree
      norm_num at hh ⊢
      exact hh)
    exact orderOf_eq_one_iff.mp ho
  · have hconj (a : A) : L.map (MulAut.conj (a : D)).toMonoidHom = L :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal a.property)
    simpa only [hconj, iSup_const] using he

variable [Nontrivial V]

/-- Conditional assembly using exactly the general source B.7.2(1)
implication. `irreducible_of_isFFModule` below discharges this premise. -/
theorem irreducible_of_B72
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D) [L.Normal]
    (eL : L ≃* HexEvenAutomorphisms) (inputs : IrreducibleInputs.{u,v} L)
    (z : D) (hzorder : orderOf z = 3)
    (hzcenter : zpowers z = (center L).map L.subtype)
    (hcent : centralizer (L : Set D) ≤ L) (hpoly : CubicPolynomial ρ z)
    (hB72 : Function.Injective ρ →
      ∀ (A X : Subgroup D), IsBestOffender ρ A → X ≠ ⊥ →
        pResidual 2 X = ⊤ → ⁅X, A⁆ = X → HasCentralPChiefFactors 2 X →
        ∀ a ∈ A, (∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v) →
          ∀ I, IsIrrPlus ρ X I → a ∈ subspaceStabilizer ρ I)
    (hFF : IsFFModule ρ) : IsIrreducible (ρ.comp L.subtype) := by
  have hcz := centralizer_le_zpowers L z hcent hzcenter
  have hzL : z ∈ L := by
    have hm : z ∈ (center L).map L.subtype := hzcenter ▸ mem_zpowers z
    obtain ⟨l, _, rfl⟩ := hm
    exact l.property
  let : IsQuasisimple HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv eL.symm
  have hfaith := faithful_of_cubicPolynomial ρ L z hzL hzorder hcz hpoly
  obtain ⟨A₀, hA₀⟩ := hFF
  obtain ⟨A, _, hA, hquad, _⟩ := hA₀.exists_quadratic_minimalBestOffender ρ
  obtain ⟨hne, hr, hchief, hcomm⟩ := invariance_hypotheses L eL z hzorder hcz A hA.1.1
  obtain ⟨I, hI⟩ := exists_isIrrPlus_of_faithful ρ hfaith L hne
  have hAI : A ≤ subspaceStabilizer ρ I := by
    intro a ha
    exact hB72 hfaith A L hA.1 hne hr hcomm hchief a ha
      (fun b hb v => hquad b hb a ha v) I hI
  have htop := irrPlus_eq_top_of_offender ρ L eL inputs z hzL hzorder hcz hpoly A
    (hA.1.isOffender ρ) I hI hAI
  have hirr := irrPlus_irreducible ρ L z hzL hpoly I hI
  subst I
  let e : (invariantSubspace ρ L ⊤ hI.choose).toRepresentation ≃ₗ (ρ.comp L.subtype) :=
    { Submodule.topEquiv with isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }
  exact e.irreducible_euqiv.mp hirr

omit [Nontrivial V] in
/-- An irreducible faithful FF-module receives actual coordinates from the
universal input, including transport from the top intermediate overgroup. -/
theorem hexacodeModel_of_irreducible
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D)
    (inputs : IrreducibleInputs.{u,v} L) (hfaith : Function.Injective ρ)
    (hirr : IsIrreducible (ρ.comp L.subtype)) (hFF : IsFFModule ρ) :
    quadraticRatio ρ = 1 ∧ Nonempty (HexacodeModel L ρ) := by
  let J : Subgroup D := ⊤
  let t : J ≃* D := Subgroup.topEquiv
  let τ := ρ.comp J.subtype
  have hi : IsIrreducible (τ.comp (L.subgroupOf J).subtype) :=
    (irreducible_comp_surjective_iff (subgroupOfEquivOfLe (show L ≤ J from le_top)).toMonoidHom
      (subgroupOfEquivOfLe (show L ≤ J from le_top)).surjective (ρ.comp L.subtype)).mpr hirr
  have hFFτ : IsFFModule τ := by
    apply hFF.map_equivariant ρ τ (t.symm.toMonoidHom)
      t.symm.injective (LinearEquiv.refl _ _)
    intro g v
    rfl
  have hratio := inputs.ff_ratio J le_top V τ (hfaith.comp J.subtype_injective) hi hFFτ
  obtain ⟨m⟩ := inputs.small J le_top V τ (hfaith.comp J.subtype_injective) hi
    (hratio ▸ by norm_num)
  have hratioρ : quadraticRatio ρ = 1 := by
    -- Transporting the ratio can be avoided: any offender is strong in one
    -- actor iff its top-subgroup copy is strong in the other.
    apply le_antisymm ((isFFModule_iff_quadraticRatio_le_one ρ).mp hFF)
    apply le_of_not_gt
    intro hlt
    obtain ⟨A, hs⟩ := (isStrongFFModule_iff_quadraticRatio_lt_one ρ).mpr hlt
    let A₀ := A.subgroupOf J
    have hm : A₀.map J.subtype = A := map_subgroupOf_eq_of_le le_top
    have helem : IsElementaryTwo A₀ := by
      let : IsElementaryAbelian 2 A := hs.1.2
      refine ⟨?_, IsElementaryAbelian.subgroupOf (show A ≤ J from le_top)⟩
      intro hb
      apply hs.1.1
      rw [← hm, hb, Subgroup.map_bot]
    have hc : fixedCodim τ A₀ = fixedCodim ρ A := by
      unfold fixedCodim
      rw [fixedSpace_comp_map, hm]
    have hr : rank A₀ = rank A := by
      rw [← rank_map_injective J.subtype J.subtype_injective, hm]
    have hstrong : IsStrongFFModule τ := ⟨A₀, helem, by rw [hc, hr]; exact hs.2⟩
    have hh := (isStrongFFModule_iff_quadraticRatio_lt_one τ).mp hstrong
    rw [hratio] at hh
    exact lt_irrefl _ hh
  refine ⟨hratioρ, ⟨{
    actor := m.actor.comp t.symm.toMonoidHom
    faithful := m.faithful.comp t.symm.injective
    component_image := ?_
    coordinates := m.coordinates
    intertwines := fun g v => m.intertwines (t.symm g) v }⟩⟩
  rw [← Subgroup.map_map]
  have hm : L.map t.symm.toMonoidHom = L.subgroupOf J := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_map, map_subgroupOf_eq_of_le (show L ≤ J from le_top)]
    change L.map (MonoidHom.id D) = L
    exact Subgroup.map_id L
  rw [hm]
  exact m.component_image

/-- Conditional algebraic assembly deriving absence of strong offenders,
irreducibility for FF-modules, the actual intertwiner, and dimension six.
`passage` below discharges the B.7.2(1) premise. -/
theorem passage_of_B72
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D) [L.Normal]
    (eL : L ≃* HexEvenAutomorphisms) (inputs : IrreducibleInputs.{u,v} L)
    (z : D) (hzorder : orderOf z = 3)
    (hzcenter : zpowers z = (center L).map L.subtype)
    (hcent : centralizer (L : Set D) ≤ L) (hpoly : CubicPolynomial ρ z)
    (hB72 : Function.Injective ρ →
      ∀ (A X : Subgroup D), IsBestOffender ρ A → X ≠ ⊥ →
        pResidual 2 X = ⊤ → ⁅X, A⁆ = X → HasCentralPChiefFactors 2 X →
        ∀ a ∈ A, (∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v) →
          ∀ I, IsIrrPlus ρ X I → a ∈ subspaceStabilizer ρ I) :
    ¬ IsStrongFFModule ρ ∧
      (IsFFModule ρ → IsIrreducible (ρ.comp L.subtype) ∧
        Nonempty (HexacodeModel L ρ) ∧ Module.finrank (ZMod 2) V = 6) := by
  have hcz := centralizer_le_zpowers L z hcent hzcenter
  have hzL : z ∈ L := by
    have hm : z ∈ (center L).map L.subtype := hzcenter ▸ mem_zpowers z
    obtain ⟨l, _, rfl⟩ := hm
    exact l.property
  let : IsQuasisimple HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv eL.symm
  have hfaith := faithful_of_cubicPolynomial ρ L z hzL hzorder hcz hpoly
  have hrec (hFF : IsFFModule ρ) : IsIrreducible (ρ.comp L.subtype) ∧
      quadraticRatio ρ = 1 ∧ Nonempty (HexacodeModel L ρ) := by
    have hi := irreducible_of_B72 ρ L eL inputs z hzorder hzcenter hcent hpoly hB72 hFF
    exact ⟨hi, hexacodeModel_of_irreducible ρ L inputs hfaith hi hFF⟩
  constructor
  · rintro ⟨A, hA⟩
    have hr := (hrec ⟨A, hA.1, hA.2.le⟩).2.1
    have hh := (isStrongFFModule_iff_quadraticRatio_lt_one ρ).mp ⟨A, hA⟩
    rw [hr] at hh
    exact lt_irrefl _ hh
  · intro hFF
    obtain ⟨hi, _, ⟨m⟩⟩ := hrec hFF
    exact ⟨hi, ⟨m⟩, m.finrank⟩

/-- Every FF-module with primitive cubic central action is irreducible under
the component. Thompson replacement and the proved B.7.2(1) supply stabilization
of an actual Irr⁺ member, even when the original offender does not preserve it. -/
theorem irreducible_of_isFFModule
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D) [L.Normal]
    (eL : L ≃* HexEvenAutomorphisms) (inputs : IrreducibleInputs.{u,v} L)
    (z : D) (hzorder : orderOf z = 3)
    (hzcenter : zpowers z = (center L).map L.subtype)
    (hcent : centralizer (L : Set D) ≤ L) (hpoly : CubicPolynomial ρ z)
    (hFF : IsFFModule ρ) : IsIrreducible (ρ.comp L.subtype) := by
  apply irreducible_of_B72 ρ L eL inputs z hzorder hzcenter hcent hpoly _ hFF
  intro hfaith A X hA hX hres hcomm hchief a ha hquad I hI
  exact ChapterB.source_lemma_B_7_2_1 ρ hfaith hA hX hres hcomm hchief ha hquad hI

/-- The passage from the universal irreducible B.4.2/B.4.5 inputs to arbitrary
nonzero cubic modules: there are no strong FF-offenders, and an FF-module is
component-irreducible with actual hexacode coordinates and hence dimension six.
Faithfulness and all hypotheses of B.7.2(1) are derived in the proof. -/
theorem passage
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D) [L.Normal]
    (eL : L ≃* HexEvenAutomorphisms) (inputs : IrreducibleInputs.{u,v} L)
    (z : D) (hzorder : orderOf z = 3)
    (hzcenter : zpowers z = (center L).map L.subtype)
    (hcent : centralizer (L : Set D) ≤ L) (hpoly : CubicPolynomial ρ z) :
    ¬ IsStrongFFModule ρ ∧
      (IsFFModule ρ → IsIrreducible (ρ.comp L.subtype) ∧
        Nonempty (HexacodeModel L ρ) ∧ Module.finrank (ZMod 2) V = 6) := by
  apply passage_of_B72 ρ L eL inputs z hzorder hzcenter hcent hpoly
  intro hfaith A X hA hX hres hcomm hchief a ha hquad I hI
  exact ChapterB.source_lemma_B_7_2_1 ρ hfaith hA hX hres hcomm hchief ha hquad hI

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.FFPassage
