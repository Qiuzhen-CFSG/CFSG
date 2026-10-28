module
public import Theory.Representation.BinaryOffender.MarkedCentralQuotient
public import Theory.Representation.BinaryRadicalFlag.FlagKernel
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Actions.Sections
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.InvolutionRatio
public import Theory.Representation.BinaryOffender.QuasisimpleImage

/-!
# A prescribed involution survives on a chief factor

For a faithful finite binary action with trivial two-core, the common kernel
of a chief flag is trivial: it is a normal subgroup of the two-group flag
kernel. Thus any prescribed involution survives on an actual chief section.
The same involution has no larger displacement there, and displacement at
most two yields quadratic ratio at most two for the faithful chief image.

Source application: Aschbacher--Smith 10.2.1, printed p.743, the chief-action
input for B.4.2 and B.4.5. No chief-factor uniqueness is assumed or asserted.
-/

public section
open Subgroup Theory.GroupTheory
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [Finite V] (ρ : Representation (ZMod 2) G V)

/-- A literal chief section on which the prescribed involution remains small. -/
@[expose] def HasMarkedChiefSection (t : G) : Prop :=
  ∃ U N : Subrepresentation ρ, U ⋖ N ∧
    IsIrreducible (sectionRepresentation ρ U N) ∧
    orderOf (actionHom (sectionRepresentation ρ U N) t) = 2 ∧
    Module.finrank (ZMod 2) (LinearMap.range
      (imageRepresentation (sectionRepresentation ρ U N)
        (actionHom (sectionRepresentation ρ U N) t) - 1)) ≤ 2 ∧
    quadraticRatio (imageRepresentation (sectionRepresentation ρ U N)) ≤ 2

/-- Preserve a given small-displacement involution on an actual irreducible section. -/
theorem exists_marked_chief_section_of_twoCore_eq_bot (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (t : G) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2) :
    ∃ U N : Subrepresentation ρ, U ⋖ N ∧
      IsIrreducible (sectionRepresentation ρ U N) ∧
      orderOf (actionHom (sectionRepresentation ρ U N) t) = 2 ∧
      Module.finrank (ZMod 2) (LinearMap.range
        (imageRepresentation (sectionRepresentation ρ U N)
          (actionHom (sectionRepresentation ρ U N) t) - 1)) ≤ 2 ∧
      quadraticRatio (imageRepresentation (sectionRepresentation ρ U N)) ≤ 2 := by
  classical
  have ht1 : t ≠ 1 := by intro he; simp [he] at ht
  let : Nontrivial G := ⟨⟨t,1,ht1⟩⟩
  let : Nontrivial V := by
    by_contra hn
    let : Subsingleton V := not_nontrivial_iff_subsingleton.mp hn
    have : Subsingleton G := Function.Injective.subsingleton hf
    exact not_subsingleton G inferInstance
  obtain ⟨c,n,hmono,hzero,hlast,hchief⟩ := exists_chief_flag ρ
  have hex : ∃ i, i < n ∧ t ∉ (sectionRepresentation ρ (c i) (c (i+1))).ker := by
    by_contra hbad
    have hall : ∀ i < n, t ∈ (sectionRepresentation ρ (c i) (c (i+1))).ker := by
      simpa only [not_exists,not_and,not_not] using hbad
    let K : Subgroup G := ⨅ i : Fin n, (sectionRepresentation ρ (c i) (c (i+1))).ker
    let : K.Normal := normal_iInf_normal fun i => inferInstance
    let W : Fin (n+1) → Submodule (ZMod 2) V := fun i => (c i).toSubmodule
    have hKF : K ≤ BinaryRadical.flagKernel ρ W := by
      intro g hg
      have hg' : ∀ i : Fin n, g ∈ (sectionRepresentation ρ (c i) (c (i+1))).ker :=
        mem_iInf.mp hg
      refine ⟨(BinaryRadical.mem_flagStabilizer ρ W).mpr (fun i v => ?_),?_⟩
      · constructor
        · intro hv
          have hh := (c i).apply_mem_toSubmodule g⁻¹ hv
          simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,
            Module.End.one_apply] using hh
        · intro hv
          exact (c i).apply_mem_toSubmodule g hv
      · intro i v hv
        exact (sectionRepresentation_trivial_iff ρ (c i) (c (i+1)) g).mp
          (fun w => LinearMap.congr_fun (hg' i) w) v hv
    have hKp := (BinaryRadical.flagKernel_isPGroup ρ hf W
      (by change (c 0).toSubmodule = ⊥; rw [hzero]; rfl)
      (by change (c n).toSubmodule = ⊤; rw [hlast]; rfl)).to_le hKF
    have hKcore : K ≤ pCore 2 G := le_sSup ⟨inferInstance,hKp⟩
    have htK : t ∈ K := mem_iInf.mpr (fun i => hall i i.isLt)
    exact ht1 (mem_bot.mp (hcore ▸ hKcore htK))
  obtain ⟨i,hi,hmove⟩ := hex
  let σ := sectionRepresentation ρ (c i) (c (i+1))
  let s := actionHom σ t
  have hs1 : s ≠ 1 := by
    intro he
    apply hmove
    exact LinearMap.ext ((actionHom_eq_one_iff σ t).mp he)
  have hs2 : s ^ 2 = 1 := by
    change (actionHom σ t)^2=1
    rw [←map_pow,show t^2=1 from ht ▸ pow_orderOf_eq_one t,map_one]
  have hs : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  have hd := fixedCodim_section_le ρ (c i) (c (i+1)) (zpowers t)
  rw [fixedCodim_zpowers_eq_displacement_rank,fixedCodim_zpowers_eq_displacement_rank] at hd
  have hr' : Module.finrank (ZMod 2) (LinearMap.range (imageRepresentation σ s - 1)) ≤ 2 :=
    hd.trans hr
  refine ⟨c i,c (i+1),hchief i hi,
    MathieuCode.Hexad.ChiefFlag.Actions.irreducible_section_of_covBy (hchief i hi),hs,hr',?_⟩
  obtain ⟨hA,hrA,hquad,_⟩ := involution_actor_rank_and_fixedCodim (imageRepresentation σ) s hs
  apply (quadraticRatio_le_two_iff (imageRepresentation σ)).mpr
  refine ⟨zpowers s,hA,hquad,?_⟩
  rw [hrA,Nat.mul_one,fixedCodim_zpowers_eq_displacement_rank]
  exact hr'

end Representation.BinaryOffender
