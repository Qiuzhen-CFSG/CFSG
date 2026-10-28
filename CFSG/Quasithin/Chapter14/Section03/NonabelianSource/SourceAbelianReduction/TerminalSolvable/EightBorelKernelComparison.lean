module
public import CFSG.Quasithin.Chapter13.Section01.RadicalQuotient
public import Theory.GroupTheory.CComponent.SimpleImageKernel
public import Theory.SpecificGroups.PSL2.EightCentralCovers
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelQuotientDefs

/-!
# The actual dotted kernel of the L₂(8) component

The simple dotted image identifies the kernel with the component's solvable
radical. If K/O₂(K) were not quasisimple, the complete A.3.6 theorem would
make K/O∞(K) a prime-field PSL₂(p), p > 3. Its order cannot be 504, the
order of the given dotted PSL₂(8). Thus K/O₂(K) is quasisimple.

The original dotted map factors through this quotient with central kernel.
The proved trivial universal-cover kernel of PSL₂(8) makes that very map
injective, proving that the original dotted kernel is exactly O₂(K).
No center bound or centralization assumption is used. In particular the
argument needs only the actual local-component lift and its image marking,
so applies under all of the original 14.3.15 hypotheses.

Source: Aschbacher--Smith 1.2.1(4),14.3.15, printed pp.504,994; A.3.6,
printed pp.43--45. The nonquasisimple alternatives use their radical
quotients, without the additional center--Frattini assertion of 1.2.1(4d).
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag

private theorem eight_card : Nat.card PSL(2, GaloisField 2 3) = 504 := by
  rw [← Nat.card_congr (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).toEquiv,
    GorensteinWalter.sl2_card_formula, GaloisField.card 2 3 (by decide)]
  norm_num

private theorem not_eight_prime_model {p : ℕ} (hp : p.Prime) (hl : 3 < p)
    (hm : ClassicalGroup.IsPSL PSL(2, GaloisField 2 3) 2 p) : False := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  have ho : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), by decide, by simpa using hcard⟩
  have hc := Nat.card_congr e.toEquiv
  rw [eight_card, GorensteinWalter.psl2_card_formula F ho, hcard] at hc
  have hbound : p < 11 := by
    by_contra hn
    have hp11 : 11 ≤ p := by omega
    have hs' : 121 ≤ p ^ 2 := Nat.pow_le_pow_left hp11 2
    have hs : 120 ≤ p ^ 2 - 1 := by omega
    have hm : 1320 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul hp11 hs
    omega
  interval_cases p <;> norm_num at hc

variable {G : Type*} [Group G] [Finite G]

/-- The actual intrinsic two-core quotient in the dotted eight row is
quasisimple, as required in the source appeal to 1.2.1(4). -/
theorem component_core_quotient_quasisimple_of_eight
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {V : Subgroup G} (F : InvariantFlag T V 2)
    {g : G} {K : Subgroup G} (hK : ComponentLift F g K) (h8 : EightImageRow F K) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  classical
  obtain ⟨e⟩ := h8.2
  let : IsSimpleGroup PSL(2, GaloisField 2 3) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card 2 3 (by decide)]; decide)
  let f := e.toMonoidHom.comp (componentDotMap F hK.le_pointNormalizer)
  have hf : Function.Surjective f := e.surjective.comp
    (componentDotMap_surjective F hK.le_pointNormalizer)
  have ht : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using
      hK.component.subgroupOf_of_le le_rfl hK.le_pointNormalizer
  have hk := kernel_eq_solvableRadical_of_top_isCComponent ht f hf
  let er : (K ⧸ solvableRadical K) ≃* PSL(2, GaloisField 2 3) :=
    QuotientGroup.liftEquiv _ hf hk.symm
  by_contra hn
  have hlocal : K ∈ Chapter1.L G (T : Subgroup G) := by
    refine ⟨hK.local_component.1, ⟨T.subtype le_sup_right, ?_⟩, ?_⟩
    · exact map_subgroupOf_eq_of_le le_sup_right
    · intro hb
      exact hK.local_component.2 ((map_eq_bot_iff_of_injective
        (pCore 2 ↥(K ⊔ (T : Subgroup G)))
        (K ⊔ (T : Subgroup G)).subtype_injective).mp hb)
  obtain ⟨p, hp, hl, hm⟩ :=
    Chapter13.Section01.nonquasisimple_local_radical_quotient hG T hlocal hn
  exact not_eight_prime_model hp hl (hm.of_mulEquiv er.symm)

/-- The canonical map to the dotted component has exactly the intrinsic
two-core as its kernel. -/
theorem componentDotMap_ker_eq_twoCore_of_eight
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {V : Subgroup G} (F : InvariantFlag T V 2)
    {g : G} {K : Subgroup G} (hK : ComponentLift F g K) (h8 : EightImageRow F K) :
    (componentDotMap F hK.le_pointNormalizer).ker = pCore 2 K := by
  obtain ⟨e⟩ := h8.2
  let : IsSimpleGroup PSL(2, GaloisField 2 3) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card 2 3 (by decide)]; decide)
  let f := e.toMonoidHom.comp (componentDotMap F hK.le_pointNormalizer)
  have hf : Function.Surjective f := e.surjective.comp
    (componentDotMap_surjective F hK.le_pointNormalizer)
  have ht : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using
      hK.component.subgroupOf_of_le le_rfl hK.le_pointNormalizer
  have hk := kernel_eq_solvableRadical_of_top_isCComponent ht f hf
  have hcore : pCore 2 K ≤ f.ker := by
    rw [hk]
    let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
    exact le_solvableRadical _ inferInstance inferInstance
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    component_core_quotient_quasisimple_of_eight hG F hK h8
  let a := QuotientGroup.lift (pCore 2 K) f hcore
  have ha : Function.Surjective a :=
    QuotientGroup.lift_surjective_of_surjective _ _ hf _
  have hak : a.ker ≤ center (K ⧸ pCore 2 K) := by
    rcases IsQuasisimple.normal_le_center_or_eq_top a.ker with hc | ht
    · exact hc
    · obtain ⟨s, hs⟩ := exists_ne (1 : PSL(2, GaloisField 2 3))
      obtain ⟨d, rfl⟩ := ha s
      exact (hs (show a d = 1 from (ht ▸ mem_top d : d ∈ a.ker))).elim
  let c : PerfectCentralCovering.Cover (K ⧸ pCore 2 K) PSL(2, GaloisField 2 3) :=
    { toMonoidHom := a
      surjective := ha
      isPerfect := inferInstance
      ker_le_center := hak }
  have hinj := Theory.SpecificGroups.PSL2Eight.cover_injective c
  have hfker : f.ker = pCore 2 K := by
    apply le_antisymm ?_ hcore
    intro k hk
    apply (QuotientGroup.eq_one_iff k).mp
    apply hinj
    change f k = a 1
    simpa only [map_one] using (show f k = 1 from hk)
  have he : f.ker = (componentDotMap F hK.le_pointNormalizer).ker :=
    MonoidHom.ker_comp_of_injective (componentDotMap F hK.le_pointNormalizer)
      e.toMonoidHom e.injective
  exact he.symm.trans hfker

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
