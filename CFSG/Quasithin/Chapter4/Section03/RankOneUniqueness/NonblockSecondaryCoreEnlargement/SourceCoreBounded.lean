module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameBoundedCore
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceCoreSmall

/-!
# SourceCoreBounded without strict core enlargement

These are the original core-action arguments with their literal subtype maps,
using only SecondaryActionData. No strict enlargement clause is supplied.
They feed recognition of the full component-core Frattini module.
Source: Aschbacher--Smith, original 4.3.2 and 4.3.11--16, pp.617--619.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
open Nonblock.RootCoordinates
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} {d : MSData c n}
namespace RootCoordinates
variable (m : RootCoordinates d)
include m

/-- The original whole radical has order 2^(11n), with its original MS core. -/
theorem radical_card (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) (s : SecondaryActionData c n) :
    Nat.card (R₂ c) = 2^(11*n) := by
  have hc := ((Q c).subgroupOf (R₂ c)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (core_le_radical c)).toEquiv] at hc
  change Nat.card (Q c) * (Q c).relIndex (R₂ c) = Nat.card (R₂ c) at hc
  rw [d.core_card,(SourceActionEndgame.RootCoordinates.radical_relIndex_core m) hn D s,←pow_mul,←pow_add] at hc
  convert hc.symm using 1
  congr 1
  omega

/-- Every section of the literal radical satisfies the whole-group order bound. -/
theorem radical_section_card_le (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) (s : SecondaryActionData c n)
    (A : Subgroup G) (hA : A ≤ R₂ c) {W : Type*} (f : A → W)
    (hf : Function.Surjective f) : Nat.card W ≤ 2^(11*n) := by
  exact (Nat.card_le_card_of_surjective f hf).trans
    ((Nat.card_le_card_of_injective (inclusion hA) (inclusion_injective hA)).trans_eq
      ((SourceActionEndgame.RootCoordinates.radical_card m) hn D s))

omit [Finite G] m in
private theorem component_extension_normal
    (s : SecondaryActionData c n) (X : Subgroup G) (hXr : X ≤ rootNormalizer c) :
    ((s.component.map (rootNormalizer c).subtype).subgroupOf
      (s.component.map (rootNormalizer c).subtype ⊔ X)).Normal := by
  let := s.normal
  apply normal_subgroupOf_of_le_normalizer
  have hh := s.component.le_normalizer_map (rootNormalizer c).subtype
  have hn : rootNormalizer c ≤ normalizer (s.component.map (rootNormalizer c).subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  exact (sup_le (map_subtype_le _) hXr).trans hn
end RootCoordinates
namespace RootCoordinates
variable {d : MSData c 2} (m : RootCoordinates d)
  (s : SecondaryActionData c 2) (D : Chapter12.Section02.ChosenModule T L V)
  (X : Subgroup G) (hX : Nat.card X = 3) (hXK : X ≤ (K c).coreCenterIn 2)
  (hXr : X ≤ rootNormalizer c) (hfix : Q c ⊓ centralizer (X : Set G) = ⊥)
  (hcomm : ⁅secondary c,X⁆ ≤ (secondary c).pCoreIn 2)
  (e : (s.component ⧸ pCore 2 s.component) ≃* Matrix.PSL3Four.PSL)
include m D hX hXK hXr hfix hcomm e

/-- A moved irreducible section of the actual component core has binary degree sixteen or eighteen. -/
theorem irreducible_core_section_degree
    (A B : Subgroup G)
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (s.component.map (rootNormalizer c).subtype ⊔ X : Subgroup G) W)
    (a : BinaryConjugationSection (s.component.map (rootNormalizer c).subtype ⊔ X) A B ρ)
    [ρ.IsIrreducible]
    (hnt : ¬ (s.component.map (rootNormalizer c).subtype).subgroupOf
      (s.component.map (rootNormalizer c).subtype ⊔ X) ≤ ρ.ker) :
    Module.finrank (ZMod 2) W = 16 ∨ Module.finrank (ZMod 2) W = 18 := by
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
  have hc : ((pCore 2 s.component).map s.component.subtype).map
      (rootNormalizer c).subtype ≤ R₂ c := by
    change (s.component.pCoreIn 2).map (rootNormalizer c).subtype ≤ R₂ c
    rw [map_pCoreIn_of_injective 2 s.component (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective]
    exact s.component_core_le D
  have hd := (SourceActionEndgame.RootCoordinates.radical_section_card_le m) (by decide) D s A (hA.trans hc)
    (fun x => (a.coordinates x).toAdd) a.onto
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hd
  have hdim : Module.finrank (ZMod 2) W ≤ 22 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hd
  rcases Representation.PSL3Four.normal_core_simple_degree_le_twenty_two H eq ρ hdim hnt with h9 | h
  · exfalso
    apply (SourceActionEndgame.RootCoordinates.component_section_not_odd_degree m) s D X hX hXK hfix hcomm A B hA
      a.kernel_le a.normalized a.kernel_normalized (show Odd 9 by decide)
    rw [a.relIndex_eq_card,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,h9]
  · exact h

/-- Retain the actual irreducible module and literal section maps selected on
 the core Frattini quotient, for subsequent full-module recognition. -/
theorem exists_moved_core_module
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ∃ (A B : Subgroup G) (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) (s.component.map (rootNormalizer c).subtype ⊔ X : Subgroup G) W)
      (_ : BinaryConjugationSection (s.component.map (rootNormalizer c).subtype ⊔ X) A B ρ),
      ρ.IsIrreducible ∧
      A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype ∧
      (frattini ((s.component.map (rootNormalizer c).subtype).pCoreIn 2)).map
        ((s.component.map (rootNormalizer c).subtype).pCoreIn 2).subtype ≤ B ∧
      ¬ (s.component.map (rootNormalizer c).subtype).subgroupOf
        (s.component.map (rootNormalizer c).subtype ⊔ X) ≤ ρ.ker ∧
      (Module.finrank (ZMod 2) W = 16 ∨ Module.finrank (ZMod 2) W = 18) := by
  let M := s.component.map (rootNormalizer c).subtype
  let E := M ⊔ X
  let H := M.subgroupOf E
  let P := M.pCoreIn 2
  let B := (frattini P).map P.subtype
  let : Group.IsPerfect s.component := s.isComponent.perfect
  let eM := s.component.equivMapOfInjective (rootNormalizer c).subtype
    (rootNormalizer c).subtype_injective
  let : Group.IsPerfect M := Group.IsPerfect.ofSurjective (f := eM.toMonoidHom) eM.surjective
  let eH : H ≃* M := subgroupOfEquivOfLe (show M ≤ E from le_sup_left)
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective (f := eH.symm.toMonoidHom) eH.symm.surjective
  have hcore : P = ((pCore 2 s.component).map s.component.subtype).map
      (rootNormalizer c).subtype := by
    dsimp only [P,M]
    rw [←map_pCoreIn_of_injective 2 s.component (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective]
    rfl
  have hNM : E ≤ normalizer (M : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show M ≤ E from le_sup_left)).mp
      (component_extension_normal s X hXr)
  have hNP : E ≤ normalizer (P : Set G) :=
    hNM.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hNB : E ≤ normalizer (B : Set G) :=
    hNP.trans (normalizer_le_normalizer_characteristic_image P (frattini P))
  have hB : B.subgroupOf P = frattini P :=
    comap_map_eq_self_of_injective P.subtype_injective _
  let : (B.subgroupOf P).Normal := hB.symm ▸ inferInstance
  have hp : IsPGroup 2 P := isPGroup_pCoreIn 2 M
  let : Fact (IsPGroup 2 P) := ⟨hp⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let eB := QuotientGroup.quotientMulEquivOfEq hB
  let : IsElementaryAbelian 2 (P ⧸ B.subgroupOf P) :=
    IsElementaryAbelian.of_surjective eB.symm.toMonoidHom eB.symm.surjective
  obtain ⟨ρ,⟨a⟩⟩ := BinaryConjugationSection.exists_elementary_quotient_coordinates
    E P B ((pCoreIn_le 2 M).trans le_sup_left) hNP (map_subtype_le _) hNB
  have hnt : ¬ H ≤ ρ.ker := by
    intro hk
    have hcomm : ⁅P,M⁆ ≤ B := by
      rw [commutator_comm]
      apply commutator_le.mpr
      intro g hg p hp
      exact (a.action_mem_ker_iff (⟨g,mem_sup_left hg⟩ : E)).mp (hk hg) p hp
    have hzero := Subgroup.commutator_eq_bot_of_le_frattini_of_perfect P M hp
      (le_sup_left.trans hNP) hcomm
    have hcentral : M ≤ centralizer (P : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
    have hMP : M ≤ P := by
      intro g hg
      have hc : (⟨g,hg⟩ : M) ∈ centralizer (pCore 2 M : Set M) := by
        intro q hq
        exact Subtype.ext (hcentral hg q (mem_map_of_mem _ hq))
      exact mem_map_of_mem M.subtype
        (component_core_selfCentralizing s D h hc)
    let : Group.IsNilpotent M := (hp.to_le hMP).isNilpotent
    have hsol : Group.IsSolvable s.component :=
      Group.isSolvable_of_isSolvable_injective (f := eM.toMonoidHom) eM.injective
    exact s.isComponent.not_isSolvable hsol
  obtain ⟨J,N,hi,hnt⟩ := Representation.QuadraticFourGroup.exists_irreducible_section_surviving_perfect
    (ρ := ρ) H hnt
  let b := (a.invariantSection J).quotientSection N
  let : N.quotientRepresentation.IsIrreducible := hi
  have hA := (a.invariantPreimage_le J).trans hcore.le
  have hd := (SourceActionEndgame.RootCoordinates.irreducible_core_section_degree m) s D X hX hXK hXr hfix hcomm e
    _ _ hA N.quotientRepresentation b hnt
  exact ⟨_,_,_,inferInstance,inferInstance,_,b,hi,hA,
    (a.invariantSection J).kernel_le_invariantPreimage N,hnt,hd⟩

/-- Selection on the actual core Frattini quotient, with both endpoints in G. -/
theorem exists_moved_core_section
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ∃ A B : Subgroup G, B ≤ A ∧
      A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype ∧
      (frattini ((s.component.map (rootNormalizer c).subtype).pCoreIn 2)).map
        ((s.component.map (rootNormalizer c).subtype).pCoreIn 2).subtype ≤ B ∧
      s.component.map (rootNormalizer c).subtype ⊔ X ≤ normalizer (A : Set G) ∧
      s.component.map (rootNormalizer c).subtype ⊔ X ≤ normalizer (B : Set G) ∧
      ¬ ⁅s.component.map (rootNormalizer c).subtype,A⁆ ≤ B ∧
      (B.relIndex A = 2^16 ∨ B.relIndex A = 2^18) := by
  obtain ⟨A,B,W,_,_,ρ,b,hi,hA,hFB,hnt,hd⟩ :=
    exists_moved_core_module m s D X hX hXK hXr hfix hcomm e h
  let : Finite W := Finite.of_surjective (fun a => (b.coordinates a).toAdd) b.onto
  let : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  refine ⟨A,B,b.kernel_le,hA,hFB,b.normalized,b.kernel_normalized,?_,?_⟩
  · intro hz
    apply hnt
    intro g hg
    apply (b.action_mem_ker_iff g).mpr
    intro q hq
    exact hz (commutator_mem_commutator hg hq)
  · rw [b.relIndex_eq_card,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    rcases hd with hd | hd
    · exact Or.inl (congrArg (fun j : ℕ => 2^j) hd)
    · exact Or.inr (congrArg (fun j : ℕ => 2^j) hd)

/-- Small invariant subgroups are fixed even when their numerators are nonabelian. -/
theorem small_invariant_core_centralizes_component
    (A : Subgroup G)
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    (hN : s.component.map (rootNormalizer c).subtype ⊔ X ≤ normalizer (A : Set G))
    (hcard : Nat.card A ≤ 2^12) :
    s.component.map (rootNormalizer c).subtype ≤ centralizer (A : Set G) := by
  let M := s.component.map (rootNormalizer c).subtype
  let E := M ⊔ X
  let B := (frattini A).map A.subtype
  let : Group.IsPerfect s.component := s.isComponent.perfect
  let eM := s.component.equivMapOfInjective (rootNormalizer c).subtype
    (rootNormalizer c).subtype_injective
  let : Group.IsPerfect M := Group.IsPerfect.ofSurjective (f := eM.toMonoidHom) eM.surjective
  have hAM : A ≤ M := hA.trans (map_mono (map_subtype_le _))
  have hB : B.subgroupOf A = frattini A := comap_map_eq_self_of_injective A.subtype_injective _
  let : (B.subgroupOf A).Normal := hB.symm ▸ inferInstance
  have hp : IsPGroup 2 A :=
    ((pCore_isPGroup (p := 2) (G := s.component)).map s.component.subtype |>.map
      (rootNormalizer c).subtype).to_le hA
  let : Fact (IsPGroup 2 A) := ⟨hp⟩
  let : IsElementaryAbelian 2 (A ⧸ frattini A) := isElementaryAbelian_quotient_frattini
  let eB := QuotientGroup.quotientMulEquivOfEq hB
  let : IsElementaryAbelian 2 (A ⧸ B.subgroupOf A) :=
    IsElementaryAbelian.of_surjective eB.symm.toMonoidHom eB.symm.surjective
  obtain ⟨ρ,⟨a⟩⟩ := BinaryConjugationSection.exists_elementary_quotient_coordinates E A B
    (hAM.trans le_sup_left) hN (map_subtype_le _)
    (hN.trans (normalizer_le_normalizer_characteristic_image A (frattini A)))
  have hb : Nat.card (Additive (A ⧸ B.subgroupOf A)) ≤ 2^12 :=
    (Nat.card_le_card_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)).trans hcard
  have hk := (SourceActionEndgame.RootCoordinates.small_core_action_component_kernel m) s D X hX hXK hXr hfix hcomm e A B hA ρ a hb
  have hz : ⁅A,M⁆ = ⊥ := Subgroup.commutator_eq_bot_of_le_frattini_of_perfect A M hp
    (le_sup_left.trans hN) (by
      rw [commutator_comm]
      apply commutator_le.mpr
      intro g hg a' ha'
      exact (a.action_mem_ker_iff (⟨g,mem_sup_left hg⟩ : E)).mp (hk hg) a' ha')
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)

/-- The original core has a small, component-fixed Frattini subgroup, hence class at most two. -/
theorem component_frattini_structure
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    let M := s.component.map (rootNormalizer c).subtype
    let P := M.pCoreIn 2
    Nat.card (frattini P) ≤ 2^6 ∧
      M ≤ Subgroup.centralizer ((frattini P).map P.subtype : Set G) ∧ frattini P ≤ center P := by
  let M := s.component.map (rootNormalizer c).subtype
  let E := M ⊔ X
  let P := M.pCoreIn 2
  let F := (frattini P).map P.subtype
  have hcore : P = ((pCore 2 s.component).map s.component.subtype).map
      (rootNormalizer c).subtype := by
    dsimp only [P,M]
    rw [←map_pCoreIn_of_injective 2 s.component (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective]
    rfl
  obtain ⟨A,B,hBA,hA,hFB,_,_,_,hd⟩ :=
    (SourceActionEndgame.RootCoordinates.exists_moved_core_section m) s D X hX hXK hXr hfix hcomm e h
  have hAP : A ≤ P := hA.trans hcore.ge
  have hPR : P ≤ R₂ c := s.component_core_le D
  have hPcard : Nat.card P ≤ 2^22 :=
    (SourceActionEndgame.RootCoordinates.radical_section_card_le m) (by decide) D s P hPR id Function.surjective_id
  have hAc : Nat.card A ≤ 2^22 :=
    (Nat.card_le_card_of_injective (inclusion hAP) (inclusion_injective hAP)).trans hPcard
  have hFc : Nat.card (frattini P) ≤ Nat.card B := by
    have hh := Nat.card_le_card_of_injective (inclusion hFB) (inclusion_injective hFB)
    rw [card_map_of_injective P.subtype_injective] at hh
    exact hh
  have hindex : 2^16 ≤ B.relIndex A := by
    rcases hd with hd | hd
    · exact hd.ge
    · rw [hd]
      norm_num
  have hc := (B.subgroupOf A).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hBA).toEquiv] at hc
  change B.relIndex A * Nat.card B = Nat.card A at hc
  have hsmall : Nat.card (frattini P) ≤ 2^6 := by
    have hh := Nat.mul_le_mul hindex hFc
    rw [hc] at hh
    norm_num at hh hAc ⊢
    omega
  have hNM : E ≤ normalizer (M : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show M ≤ E from le_sup_left)).mp
      (component_extension_normal s X hXr)
  have hNP : E ≤ normalizer (P : Set G) :=
    hNM.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hcF : M ≤ centralizer (F : Set G) :=
    (SourceActionEndgame.RootCoordinates.small_invariant_core_centralizes_component m) s D X hX hXK hXr hfix hcomm e F
      ((map_subtype_le _).trans hcore.le)
      (hNP.trans (normalizer_le_normalizer_characteristic_image P (frattini P))) (by
        rw [card_map_of_injective P.subtype_injective]
        exact hsmall.trans (by norm_num))
  refine ⟨hsmall,hcF,?_⟩
  intro z hz
  apply mem_center_iff.mpr
  intro p
  apply Subtype.ext
  exact (hcF (pCoreIn_le 2 M p.property) z (mem_map_of_mem _ hz)).symm

end RootCoordinates

/-- The original cubic supplies the actor for a moved section of order 2^16 or 2^18. -/
theorem MSData.linearFour_moved_core_section (d : MSData c 2) (m : RootCoordinates d)
    (s : SecondaryActionData c 2) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (e : (s.component ⧸ pCore 2 s.component) ≃* Matrix.PSL3Four.PSL) :
    ∃ X A B : Subgroup G, Nat.card X = 3 ∧ X ≤ (K c).coreCenterIn 2 ∧
      X ≤ rootNormalizer c ∧ B ≤ A ∧
      A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype ∧
      s.component.map (rootNormalizer c).subtype ⊔ X ≤ normalizer (A : Set G) ∧
      s.component.map (rootNormalizer c).subtype ⊔ X ≤ normalizer (B : Set G) ∧
      ¬ ⁅s.component.map (rootNormalizer c).subtype,A⁆ ≤ B ∧
      (B.relIndex A = 2^16 ∨ B.relIndex A = 2^18) := by
  obtain ⟨X,hX,hXK,hr,hfix,_,_,_,hcomm,_,_⟩ := d.exists_source_cubic_root D
  obtain ⟨A,B,hAB,hA,_,hNA,hNB,hm,hd⟩ :=
    (SourceActionEndgame.RootCoordinates.exists_moved_core_section m) s D X hX hXK hr hfix hcomm e h
  exact ⟨X,A,B,hX,hXK,hr,hAB,hA,hNA,hNB,hm,hd⟩

/-- Source application: the whole original component core has central Frattini subgroup of order at most 64. -/
theorem MSData.linearFour_frattini_structure (d : MSData c 2) (m : RootCoordinates d)
    (s : SecondaryActionData c 2) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (e : (s.component ⧸ pCore 2 s.component) ≃* Matrix.PSL3Four.PSL) :
    let M := s.component.map (rootNormalizer c).subtype
    let P := M.pCoreIn 2
    Nat.card (frattini P) ≤ 2^6 ∧
      M ≤ Subgroup.centralizer ((frattini P).map P.subtype : Set G) ∧
      frattini P ≤ center P ∧ commutator P ≤ center P := by
  obtain ⟨X,hX,hXK,hr,hfix,_,_,_,hcomm,_,_⟩ := d.exists_source_cubic_root D
  obtain ⟨hc,hf,hz⟩ := (SourceActionEndgame.RootCoordinates.component_frattini_structure m) s D X hX hXK hr hfix hcomm e h
  let P := (s.component.map (rootNormalizer c).subtype).pCoreIn 2
  let : Fact (IsPGroup 2 P) := ⟨isPGroup_pCoreIn 2 _⟩
  exact ⟨hc,hf,hz,commutator_le_frattini_of_isPGroup (p := 2) |>.trans hz⟩
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
