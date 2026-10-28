module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.AlternatingCovers.SevenExclusion.Degree
public import Theory.Representation.BinaryOffender.CubicCenterChief
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient

/-!
# Cubic-center actions in the second-normalizer triple-seven row

An order-three element moving a binary space survives on a literal chief
factor: otherwise its faithful cyclic action lies in the two-group kernel
of a chief flag. On that factor the intrinsic two-core acts trivially.
If the cubic image is central in the triple-seven quotient, quasisimplicity
and its center of order three make the factor faithful. The proved degree
twelve bound contradicts the full plane's dimension at most six.

SecondSeven applies this to the original Cartan factor and the entire V₂,
including C_V(L). No irreducibility or faithfulness of the original K-action
is assumed. This is local supporting mathematics for
qt-d-1222-natural-relative-components.

Source: Aschbacher--Smith 11.1.2, printed pp.764--765; the triple-seven
binary-degree calculation is the one used in B.1.13 and K.1, pp.73--74,452.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.SecondSevenAction

private theorem moving_cubic_section {G W : Type*} [Group G] [Finite G]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (x : G) (hx : orderOf x = 3)
    (hm : ρ x ≠ 1) :
    ∃ U N : Subrepresentation ρ,
      IsIrreducible (sectionRepresentation ρ U N) ∧
      sectionRepresentation ρ U N x ≠ 1 := by
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : Nontrivial W := by
    by_contra hn
    let : Subsingleton W := not_nontrivial_iff_subsingleton.mp hn
    exact hm (Subsingleton.elim _ _)
  obtain ⟨c,n,hmono,hzero,hlast,hchief⟩ := exists_chief_flag ρ
  have hex : ∃ i, i < n ∧ sectionRepresentation ρ (c i) (c (i+1)) x ≠ 1 := by
    by_contra! hall
    let E := zpowers x
    let σ := ρ.comp E.subtype
    let : IsSimpleGroup E := isSimpleGroup_of_prime_card (p := 3) (by rw [Nat.card_zpowers,hx])
    have hf : Function.Injective σ := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rcases (inferInstance : σ.ker.Normal).eq_bot_or_eq_top with h | h
      · exact h
      · exact (hm (show σ ⟨x,mem_zpowers x⟩ = 1 from (show (⟨x,mem_zpowers x⟩ : E) ∈ σ.ker from h.symm ▸ mem_top _))).elim
    let F : Fin (n+1) → Submodule (ZMod 2) W := fun i => (c i).toSubmodule
    have hp := BinaryRadical.flagKernel_isPGroup σ hf F
      (by change (c 0).toSubmodule = ⊥; rw [hzero]; rfl)
      (by change (c n).toSubmodule = ⊤; rw [hlast]; rfl)
    have hmF : (⟨x,mem_zpowers x⟩ : E) ∈ BinaryRadical.flagKernel σ F := by
      refine ⟨(BinaryRadical.mem_flagStabilizer σ F).mpr (fun i v => ?_),?_⟩
      · constructor
        · intro hv
          have hh := (c i).apply_mem_toSubmodule x⁻¹ hv
          change ρ x⁻¹ (ρ x v) ∈ (c i).toSubmodule at hh
          simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,
            Module.End.one_apply] using hh
        · intro hv
          exact (c i).apply_mem_toSubmodule x hv
      · intro i v hv
        exact (sectionRepresentation_trivial_iff ρ (c i) (c (i+1)) x).mp
          (fun w => LinearMap.congr_fun (hall i i.isLt) w) v hv
    have hc := hp.orderOf_coprime (by decide : Nat.Coprime 2 3) ⟨⟨x,mem_zpowers x⟩,hmF⟩
    simp only [orderOf_mk,hx] at hc
    norm_num at hc
  obtain ⟨i,hi,hm⟩ := hex
  exact ⟨c i,c (i+1),
    MathieuCode.Hexad.ChiefFlag.Actions.irreducible_section_of_covBy (hchief i hi),hm⟩

/-- The cubic center of an actual triple-seven two-core quotient cannot
move a binary space of dimension at most six. -/
theorem central_cubic_trivial {G W : Type*} [Group G] [Finite G]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    [IsQuasisimple (G ⧸ pCore 2 G)]
    (e : ((G ⧸ pCore 2 G) ⧸ center (G ⧸ pCore 2 G)) ≃* alternatingGroup (Fin 7))
    (hc : Nat.card (center (G ⧸ pCore 2 G)) = 3)
    (ρ : Representation (ZMod 2) G W) (hd : Module.finrank (ZMod 2) W ≤ 6)
    (x : G) (hx : orderOf x = 3)
    (hz : QuotientGroup.mk' (pCore 2 G) x ∈ center (G ⧸ pCore 2 G)) : ρ x = 1 := by
  by_contra hm
  obtain ⟨U,N,hi,hm⟩ := moving_cubic_section ρ x hx hm
  let σ := sectionRepresentation ρ U N
  let := hi
  have hcore := normal_p_subgroup_le_ker σ (pCore 2 G) pCore_isPGroup
  let τ := quotientOfLEKer σ (pCore 2 G) hcore
  let : τ.IsIrreducible := (quotientOfLEKer_irreducible_iff _ _ _).mpr hi
  have hmove : τ (QuotientGroup.mk' (pCore 2 G) x) ≠ 1 := hm
  have hk : τ.ker ≤ center (G ⧸ pCore 2 G) := by
    rcases IsQuasisimple.normal_le_center_or_eq_top τ.ker with h | h
    · exact h
    · exact (hmove (show QuotientGroup.mk' (pCore 2 G) x ∈ τ.ker from h.symm ▸ mem_top _)).elim
  have hcard : Nat.card τ.ker ∣ 3 := hc ▸ card_dvd_of_le hk
  have hf : Function.Injective τ := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rcases (Nat.dvd_prime Nat.prime_three).mp hcard with h | h
    · exact card_eq_one.mp h
    · have he : τ.ker = center (G ⧸ pCore 2 G) := eq_of_le_of_card_ge hk (by omega)
      exact (hmove (show QuotientGroup.mk' (pCore 2 G) x ∈ τ.ker from he.symm ▸ hz)).elim
  obtain ⟨a⟩ := GLS3.Chapter5.OddCentralCovers.triple_seven_equiv e hc
  let υ := τ.comp a.symm.toMonoidHom
  have hu : IsIrreducible υ :=
    (irreducible_comp_surjective_iff a.symm.toMonoidHom a.symm.surjective τ).mpr inferInstance
  have hlo := ChapterB.ComponentRecognition.AlternatingCovers.SevenExclusion.finrank_ge_twelve
    υ (hf.comp a.symm.injective) hu
  have hdim : Module.finrank (ZMod 2)
      (N.toSubmodule ⧸ (sectionLower ρ U N).toSubmodule) ≤ 6 :=
    (Submodule.finrank_quotient_le _).trans ((Submodule.finrank_le _).trans hd)
  exact (by omega : ¬ 12 ≤ 6) (hlo.trans hdim)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.SecondSevenAction
