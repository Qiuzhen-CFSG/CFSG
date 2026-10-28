module
public import Theory.Representation.BinaryOffender.PerfectCentralizerDisplacement
public import Theory.Representation.NormalElementaryQuotient.CommonChief
public import Theory.Representation.BinaryOffender.UniformFixedSpace
public import Theory.Representation.BinaryOffender.SectionSaturation

/-!
# Sharp displacement on a common chief section

The first perfect factor forces a nontrivial commuting actor to move at least
three binary dimensions. Zero actor rank loss supplies nontriviality on the
section. If the second factor is simple and the actor is faithful on it, every
nonidentity actor element also acts nontrivially on the section. When ambient
displacement is three, all these elements have the same fixed space, and an
elementary binary actor is quadratic.

Source application: Aschbacher--Smith 13.1.9, printed p.871, the equality case
of (*). The argument retains the original restricted section and does not
require a tensor identification.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.CommonChief
variable {Q V : Type*} [Group Q] [Finite Q] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A common chief section with zero actor rank loss has displacement at least three. -/
theorem Data.actor_displacement {ρ : Representation (ZMod 2) Q V} {S K A : Subgroup Q}
    [Group.IsPerfect S] {support : Submodule (ZMod 2) V}
    (d : Data ρ S K A support) (hc : ⁅S,K ⊔ A⁆ = ⊥)
    (hA : IsElementaryTwo A) (he : d.movedSection.rankLoss = 0) :
    3 ≤ fixedCodim (sectionRepresentation (ρ.comp (actorGroup S K A).subtype)
      d.lower d.upper) (A.subgroupOf (actorGroup S K A)) := by
  let F := actorGroup S K A
  let S₀ := S.subgroupOf F
  let A₀ := A.subgroupOf F
  let σ := sectionRepresentation (ρ.comp F.subtype) d.lower d.upper
  have hS : S ≤ F := le_sup_left
  have hAF : A ≤ F := le_sup_right.trans le_sup_right
  have hFS : F ≤ normalizer (S : Set Q) := sup_le S.le_normalizer
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
      (Subgroup.centralizer_le_normalizer _))
  let : S₀.Normal := normal_subgroupOf_of_le_normalizer hFS
  let : Group.IsPerfect S₀ := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hS).symm.toMonoidHom)
    (subgroupOfEquivOfLe hS).symm.surjective
  let := d.irreducible
  have hAc : ¬ A₀ ≤ σ.ker := by
    intro hk
    have hz : RepeatedSectionBudget.actor ρ F A d.lower d.upper = ⊥ := by
      apply bot_unique
      rintro _ ⟨a,ha,rfl⟩
      apply mem_bot.mpr
      apply (actionHom_eq_one_iff σ a).mpr
      exact fun v => LinearMap.congr_fun (hk ha) v
    have hr := RepeatedSectionBudget.epsilon_add_rank (ρ := ρ) hAF d.lower d.upper
    have he' : RepeatedSectionBudget.epsilon ρ F A d.lower d.upper = 0 := he
    rw [he',hz,BinaryOffender.rank_bot,zero_add] at hr
    have hp := hA.rank_pos
    omega
  have hc₀ : ⁅S₀,A₀⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro s hs a ha
    exact Subtype.ext (commutator_eq_bot_iff_le_centralizer.mp hc hs a
      (show a.val ∈ K ⊔ A from mem_sup_right ha))
  exact three_le_fixedCodim_of_normal_perfect σ S₀ A₀ d.first_moves hAc hc₀

omit [Finite Q] in
/-- Displacement on the literal restricted section is bounded by ambient displacement. -/
theorem Data.actor_displacement_le {ρ : Representation (ZMod 2) Q V} {S K A : Subgroup Q}
    {support : Submodule (ZMod 2) V} (d : Data ρ S K A support) :
    fixedCodim (sectionRepresentation (ρ.comp (actorGroup S K A).subtype)
      d.lower d.upper) (A.subgroupOf (actorGroup S K A)) ≤ fixedCodim ρ A := by
  have hs := fixedCodim_section_le (ρ.comp (actorGroup S K A).subtype)
    d.lower d.upper (A.subgroupOf (actorGroup S K A))
  have he : fixedCodim (ρ.comp (actorGroup S K A).subtype)
      (A.subgroupOf (actorGroup S K A)) = fixedCodim ρ A := by
    unfold fixedCodim
    rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le
      (show A ≤ actorGroup S K A from le_sup_right.trans le_sup_right)]
  exact hs.trans_eq he

omit [Finite Q] in
/-- Faithfulness on a simple second factor makes every nonidentity actor element move
at least three dimensions of the original module. -/
theorem Data.element_displacement {ρ : Representation (ZMod 2) Q V} {S K A : Subgroup Q}
    [Group.IsPerfect S] [K.Normal] [IsSimpleGroup K]
    {support : Submodule (ZMod 2) V} (d : Data ρ S K A support)
    (hc : ⁅S,K ⊔ A⁆ = ⊥) (hf : A ⊓ centralizer (K : Set Q) = ⊥)
    {a : Q} (ha : a ∈ A) (hne : a ≠ 1) :
    3 ≤ fixedCodim ρ (zpowers a) := by
  let F := actorGroup S K A
  let S₀ := S.subgroupOf F
  let σ := sectionRepresentation (ρ.comp F.subtype) d.lower d.upper
  have hS : S ≤ F := le_sup_left
  have hAF : A ≤ F := le_sup_right.trans le_sup_right
  let a₀ : F := ⟨a,hAF ha⟩
  have hFS : F ≤ normalizer (S : Set Q) := sup_le S.le_normalizer
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
      (Subgroup.centralizer_le_normalizer _))
  let : S₀.Normal := normal_subgroupOf_of_le_normalizer hFS
  let : Group.IsPerfect S₀ := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hS).symm.toMonoidHom)
    (subgroupOfEquivOfLe hS).symm.surjective
  let := d.irreducible
  have hmove : ¬ zpowers a₀ ≤ σ.ker := by
    intro hk
    have he := simple_normal_inclusion_actor_faithful K F A
      (show K ≤ F from le_sup_left.trans le_sup_right) σ d.second_moves hf a₀ ha
      (fun v => LinearMap.congr_fun (hk (mem_zpowers a₀)) v)
    exact hne (congrArg Subtype.val he)
  have hc₀ : ⁅S₀,zpowers a₀⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro s hs b hb
    have hbA : b.val ∈ A := by
      have hle : zpowers a₀ ≤ A.subgroupOf F := zpowers_le.mpr ha
      exact hle hb
    exact Subtype.ext (commutator_eq_bot_iff_le_centralizer.mp hc hs b
      (show b.val ∈ K ⊔ A from mem_sup_right hbA))
  have hl := three_le_fixedCodim_of_normal_perfect σ S₀ (zpowers a₀)
    d.first_moves hmove hc₀
  have hu := fixedCodim_section_le (ρ.comp F.subtype) d.lower d.upper (zpowers a₀)
  have hr : fixedCodim (ρ.comp F.subtype) (zpowers a₀) = fixedCodim ρ (zpowers a) := by
    unfold fixedCodim
    rw [fixedSpace_comp_map,MonoidHom.map_zpowers]
    rfl
  exact hl.trans (hu.trans_eq hr)

omit [Finite Q] in
/-- Sharp displacement gives a quadratic action and a common fixed space. -/
theorem Data.sharp_quadratic {ρ : Representation (ZMod 2) Q V} {S K A : Subgroup Q}
    [Group.IsPerfect S] [K.Normal] [IsSimpleGroup K] [IsElementaryAbelian 2 A]
    {support : Submodule (ZMod 2) V} (d : Data ρ S K A support)
    (hc : ⁅S,K ⊔ A⁆ = ⊥) (hf : A ⊓ centralizer (K : Set Q) = ⊥)
    (hsharp : fixedCodim ρ A = 3) :
    IsQuadratic ρ A ∧ ∀ a ∈ A, a ≠ 1 →
      fixedCodim ρ (zpowers a) = 3 ∧ fixedSpace ρ A = fixedSpace ρ (zpowers a) := by
  have hsame (a : Q) (ha : a ∈ A) (hn : a ≠ 1) :
      fixedCodim ρ A = fixedCodim ρ (zpowers a) := by
    have hl := d.element_displacement hc hf ha hn
    have hfixle : fixedSpace ρ A ≤ fixedSpace ρ (zpowers a) :=
      fun v hv x => hv ⟨x,(zpowers_le.mpr ha) x.property⟩
    have hdimle := Submodule.finrank_mono hfixle
    have hfirst := fixedCodim_add_finrank ρ A
    have hsecond := fixedCodim_add_finrank ρ (zpowers a)
    omega
  refine ⟨isQuadratic_of_common_fixedCodim ρ hsame,?_⟩
  intro a ha hn
  exact ⟨(hsame a ha hn).symm.trans hsharp,
    fixedSpace_eq_of_fixedCodim_eq ρ (zpowers_le.mpr ha) (hsame a ha hn)⟩

omit [Finite Q] in
/-- Sharpness confines the simple factor's action to the same literal section. -/
theorem Data.factor_fixed_outside {ρ : Representation (ZMod 2) Q V} {S K A : Subgroup Q}
    [K.Normal] [IsSimpleGroup K]
    {support : Submodule (ZMod 2) V} (d : Data ρ S K A support)
    (hf : A ⊓ centralizer (K : Set Q) = ⊥) (hA : A ≠ ⊥)
    (he : fixedCodim (sectionRepresentation (ρ.comp (actorGroup S K A).subtype)
      d.lower d.upper) (A.subgroupOf (actorGroup S K A)) = fixedCodim ρ A) :
    d.lower.toSubmodule ≤ fixedSpace ρ K ∧
      ∀ k ∈ K.subgroupOf (actorGroup S K A), ∀ v, d.upper.quotientRepresentation k v = v := by
  let F := actorGroup S K A
  let K₀ := K.subgroupOf F
  let A₀ := A.subgroupOf F
  have hK : K ≤ F := le_sup_left.trans le_sup_right
  have hAF : A ≤ F := le_sup_right.trans le_sup_right
  let : IsSimpleGroup K₀ := (subgroupOfEquivOfLe hK).isSimpleGroup
  have hf₀ : A₀ ⊓ centralizer (K₀ : Set F) = ⊥ := by
    apply bot_unique
    intro a ha
    apply mem_bot.mpr
    apply Subtype.ext
    have hcent : (a : Q) ∈ centralizer (K : Set Q) := by
      intro k hk
      exact congrArg Subtype.val (ha.2 ⟨k,hK hk⟩ hk)
    exact mem_bot.mp (hf ▸ (show (a : Q) ∈ A ⊓ centralizer (K : Set Q) from ⟨ha.1,hcent⟩))
  have hA₀ : A₀ ≠ ⊥ := by
    intro hz
    apply hA
    have hh := congrArg (Subgroup.map F.subtype) hz
    simpa only [A₀,map_subgroupOf_eq_of_le hAF,Subgroup.map_bot] using hh
  have hcod : fixedCodim (ρ.comp F.subtype) A₀ = fixedCodim ρ A := by
    unfold fixedCodim
    rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le hAF]
  have hout := factor_fixed_outside_section_of_fixedCodim_eq (ρ.comp F.subtype)
    d.lower d.upper d.lower_le_upper K₀ A₀ hf₀ hA₀ (he.trans hcod.symm)
  have hfix : fixedSpace (ρ.comp F.subtype) K₀ = fixedSpace ρ K := by
    rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le hK]
  exact ⟨hout.1.trans_eq hfix,hout.2⟩
end Representation.CommonChief
