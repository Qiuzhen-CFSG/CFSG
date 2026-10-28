module
public import Theory.Representation.BinaryOffender.MarkedCentralQuotient
public import Theory.Representation.BinaryRadicalFlag.FlagKernel
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Actions.Sections
public import Theory.GroupTheory.Covering

/-!
# Faithful chief detection of a cubic quasisimple center

A faithful binary action detects a subgroup of order three on some chief
factor of the full actor: otherwise that subgroup lies in the two-group
flag kernel. The kernel on the quasisimple component is central and misses
its cubic center, hence is trivial. The chosen factor retains the literal
subrepresentation quotient and the original component inclusion.

Source: the faithful chief-factor step in Aschbacher–Smith13.5.21, p.924.
-/

public section
open Subgroup Theory.GroupTheory
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [Finite V] (ρ : Representation (ZMod 2) G V)

/-- A faithful binary representation detects a cubic component center on an
actual irreducible chief factor of the full actor. The chief kernel is central
in the quasisimple component, so that factor is faithful on the component. -/
theorem exists_faithful_chief_of_cubic_center
    (L : Subgroup G) [IsQuasisimple L] (hf : Function.Injective ρ)
    (hc : Nat.card (center L) = 3) :
    ∃ U N : Subrepresentation ρ,
      IsIrreducible (sectionRepresentation ρ U N) ∧
      Function.Injective ((sectionRepresentation ρ U N).comp L.subtype) := by
  classical
  let : Nontrivial (center L) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Nontrivial G := (L.subtype_injective.comp (center L).subtype_injective).nontrivial
  let : Nontrivial V := by
    by_contra hn
    let : Subsingleton V := not_nontrivial_iff_subsingleton.mp hn
    have : Subsingleton G := Function.Injective.subsingleton hf
    exact not_subsingleton G inferInstance
  obtain ⟨c,n,hmono,hzero,hlast,hchief⟩ := exists_chief_flag ρ
  let Z := (center L).map L.subtype
  have hZcard : Nat.card Z = 3 := (card_map_of_injective L.subtype_injective).trans hc
  have hZ : ∃ i, i < n ∧ ¬ Z ≤ (sectionRepresentation ρ (c i) (c (i+1))).ker := by
    by_contra hbad
    have hall : ∀ i < n, Z ≤ (sectionRepresentation ρ (c i) (c (i+1))).ker := by
      simpa only [not_exists, not_and, not_not] using hbad
    let W : Fin (n+1) → Submodule (ZMod 2) V := fun i => (c i).toSubmodule
    have hZK : Z ≤ BinaryRadical.flagKernel ρ W := by
      intro z hz
      refine ⟨(BinaryRadical.mem_flagStabilizer ρ W).mpr (fun i v => ?_),?_⟩
      · constructor
        · intro hv
          have hh := (c i).apply_mem_toSubmodule z⁻¹ hv
          simpa only [← Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,
            Module.End.one_apply] using hh
        · intro hv
          exact (c i).apply_mem_toSubmodule z hv
      · intro i v hv
        exact (sectionRepresentation_trivial_iff ρ (c i) (c (i+1)) z).mp
          (fun w => congrArg (fun f : Module.End (ZMod 2) _ => f w) (hall i i.isLt hz)) v hv
    have hp := (BinaryRadical.flagKernel_isPGroup ρ hf W
      (by change (c 0).toSubmodule = ⊥; rw [hzero]; rfl)
      (by change (c n).toSubmodule = ⊤; rw [hlast]; rfl)).to_le hZK
    have h2 : 2 ∣ Nat.card Z := hp.card_eq_or_dvd.resolve_left (by omega)
    norm_num [hZcard] at h2
  obtain ⟨i,hi,hzi⟩ := hZ
  let σ := sectionRepresentation ρ (c i) (c (i+1))
  have hn : ¬ L ≤ σ.ker := fun hh => hzi ((map_subtype_le _).trans hh)
  have hk : (σ.comp L.subtype).ker ≤ center L := by
    rcases IsQuasisimple.normal_le_center_or_eq_top (σ.comp L.subtype).ker with hk | ht
    · exact hk
    · exact (hn (fun x hx => show σ x = 1 from
        (show (⟨x,hx⟩ : L) ∈ (σ.comp L.subtype).ker from
          ht.symm ▸ (show (⟨x,hx⟩ : L) ∈ (⊤ : Subgroup L) from by trivial)))).elim
  have hkc : Nat.card (σ.comp L.subtype).ker ∣ 3 := by
    rw [←hc]
    exact card_dvd_of_le hk
  have hkb : (σ.comp L.subtype).ker = ⊥ := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hkc with hh | hh
    · exact (eq_bot_iff_card _).mpr hh
    · have he : (σ.comp L.subtype).ker = center L :=
        eq_of_le_of_card_ge hk (by omega)
      apply (hzi ?_).elim
      rintro _ ⟨l,hl,rfl⟩
      exact (show l ∈ (σ.comp L.subtype).ker from he.symm ▸ hl)
  refine ⟨c i,c (i+1),?_,(MonoidHom.ker_eq_bot_iff _).mp hkb⟩
  exact MathieuCode.Hexad.ChiefFlag.Actions.irreducible_section_of_covBy (hchief i hi)
end Representation.BinaryOffender
