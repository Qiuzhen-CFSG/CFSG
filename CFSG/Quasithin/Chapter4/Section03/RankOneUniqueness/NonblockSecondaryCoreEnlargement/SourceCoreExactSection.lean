module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceCoreOrder
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement MatrixGroups
open Representation.SL3.AdjointCubicCentralizer.GraphExtension.FrattiniDescent
@[expose] public section
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
open Nonblock.RootCoordinates
attribute [local instance] SecondaryActionData.normal
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {d : MSData c 2}
set_option backward.isDefEq.respectTransparency false

 theorem exact_section
    (m : RootCoordinates d) (s : SecondaryActionData c 2)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (X : Subgroup G) (hX : Nat.card X = 3) (hXK : X ≤ (K c).coreCenterIn 2)
    (hXr : X ≤ rootNormalizer c) (hfix : Q c ⊓ centralizer (X : Set G) = ⊥)
    (hcomm : ⁅secondary c,X⁆ ≤ (secondary c).pCoreIn 2)
    (e : (s.component ⧸ pCore 2 s.component) ≃* Matrix.PSL3Four.PSL) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) (s.component.map (rootNormalizer c).subtype ⊔ X : Subgroup G) W)
      (_ : BinaryConjugationSection (s.component.map (rootNormalizer c).subtype ⊔ X)
        ((s.component.map (rootNormalizer c).subtype).pCoreIn 2)
        ((frattini ((s.component.map (rootNormalizer c).subtype).pCoreIn 2)).map
          ((s.component.map (rootNormalizer c).subtype).pCoreIn 2).subtype) ρ),
      ρ.IsIrreducible ∧ Module.finrank (ZMod 2) W = 16 ∧
        ¬ (s.component.map (rootNormalizer c).subtype).subgroupOf
          (s.component.map (rootNormalizer c).subtype ⊔ X) ≤ ρ.ker := by
  let M := s.component.map (rootNormalizer c).subtype
  let P := M.pCoreIn 2
  let F := (frattini P).map P.subtype
  have hcore : P = ((pCore 2 s.component).map s.component.subtype).map
      (rootNormalizer c).subtype := by
    dsimp only [P,M]
    rw [←map_pCoreIn_of_injective 2 s.component (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective]
    rfl
  obtain ⟨A,B,W,_,_,ρ,b,hi,hA,hFB,hnt,hd⟩ :=
    RootCoordinates.exists_moved_core_module m s D X hX hXK hXr hfix hcomm e h
  let : Finite W := Finite.of_surjective (fun a => (b.coordinates a).toAdd) b.onto
  let : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  have hAP : A ≤ P := hA.trans hcore.ge
  have hF : Nat.card (frattini P) = 4 :=
    (MSData.linearFour_special_root d m s D h e).2.2.2
  have hFc : Nat.card F = 4 := (card_map_of_injective P.subtype_injective).trans hF
  have hBc : 4 ≤ Nat.card B := hFc ▸
    Nat.card_le_card_of_injective (inclusion hFB) (inclusion_injective hFB)
  have hAc : Nat.card A ≤ Nat.card P :=
    Nat.card_le_card_of_injective (inclusion hAP) (inclusion_injective hAP)
  have hPc : Nat.card P = 2^18 :=
    (RootCoordinates.component_core_exact_order m s D h e).1
  have hApc : Nat.card A ≤ 2^18 := by
    calc Nat.card A ≤ Nat.card P := hAc
      _ = 2^18 := hPc
  have hcard := b.card_section
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W),Nat.card_zmod] at hcard
  have hdegree : Module.finrank (ZMod 2) W = 16 := by
    rcases hd with hd | hd
    · exact hd
    · rw [hd] at hcard
      norm_num at hcard hPc
      omega
  rw [hdegree] at hcard
  norm_num at hcard hPc
  have hBpc : Nat.card B ≤ 4 := by omega
  have hAe : A = P := eq_of_le_of_card_ge hAP (by omega)
  have hBe : B = F := (eq_of_le_of_card_ge hFB (by rw [hFc]; omega)).symm
  subst A B
  exact ⟨W,inferInstance,inferInstance,ρ,b,hi,hdegree,hnt⟩

/-- A degree-sixteen irreducible binary section remains irreducible on the
normal component when the component action is nontrivial. -/
theorem sixteen_restriction_irreducible
    {A W : Type*} [Group A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) [ρ.IsIrreducible]
    (H : Subgroup A) [H.Normal]
    (e : (H ⧸ pCore 2 H) ≃* Matrix.PSL3Four.PSL)
    (hd : Module.finrank (ZMod 2) W = 16) (hnt : ¬ H ≤ ρ.ker) :
    IsIrreducible (ρ.comp H.subtype) := by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨J,hJ⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp H.subtype)
  let : J.toRepresentation.IsIrreducible := hJ
  have hjd := J.toSubmodule.finrank_le
  have hj := Representation.PSL3Four.core_simple_degree_le_twenty_two
    e J.toRepresentation (by omega)
  have hjne : Module.finrank (ZMod 2) J.toSubmodule ≠ 1 := by
    intro h1
    apply hnt
    apply le_ker_of_normal_invariants_ne_bot ρ H
    let : Nontrivial J.toSubmodule := Subrepresentation.irreducible_module_nontrivial J.toRepresentation
    obtain ⟨v,hv⟩ := exists_ne (0 : J.toSubmodule)
    have ht (g : H) : J.toRepresentation g v = v := by
      obtain ⟨a,ha⟩ := exists_smul_eq_of_finrank_eq_one h1 hv (J.toRepresentation g v)
      have ha0 : a ≠ 0 := by
        intro he
        have hh : J.toRepresentation g v = 0 := by simpa [he] using ha.symm
        apply hv
        simpa only [J.toRepresentation.inv_self_apply,map_zero] using
          congrArg (J.toRepresentation g⁻¹) hh
      have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
      simpa only [ha1,one_smul] using ha.symm
    intro hb
    have hm : (v : W) ∈ invariants (ρ.comp H.subtype) :=
      fun g => congrArg Subtype.val (ht g)
    rw [hb,Submodule.mem_bot] at hm
    exact hv (Subtype.ext hm)
  exact irreducible_restrict_of_large_constituent ρ H inferInstance J hJ (by omega)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
