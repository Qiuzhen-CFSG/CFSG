module
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.UnitaryFiveLine
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.ParabolicPlacement
public import CFSG.Quasithin.Chapter4.Section04.OddActorOddCore
public import Theory.SpecificGroups.ClassicalUnitary.FiveLineCentered
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTwoLocal

/-!
# Excluding the PSU₅(4) component with the original centered module

Residual uniqueness places the full line-parabolic preimage in N(L).
It normalizes the fixed odd-actor residual, so the image of that residual
is normal in the literal line parabolic. The matrix parabolic calculation
identifies its perfect nonsolvable image. Passing through the central
kernel forces every centered commutator module to be zero.
The original residual, its inclusion and the central quotient map are retained.
Source: Aschbacher--Smith 4.4.12, printed pp.621--622.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl

/-- The full parabolic preimage normalizes the original residual. Normality
of its quotient image is relative to this parabolic. -/
theorem central_quotient_parabolic_normality
    {G Q : Type*} [Group G] [Finite G] [Group Q]
    {L A K : Subgroup G} (hKN : K ≤ normalizer (A : Set G))
    (hFK : oddActorResidual L A ≤ K)
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (q : K →* Q) (hq : Function.Surjective q) (hker : q.ker ≤ center K)
    (P : Subgroup Q) (hP : IsTwoLocal P)
    (hFP : (q.comp (inclusion hFK)).range ≤ P) :
    (P.comap q).map K.subtype ≤ normalizer (L : Set G) ∧
      ((q.comp (inclusion hFK)).range.subgroupOf P).Normal := by
  obtain ⟨R,hn,hp,he⟩ := hP
  have hPM := central_preimage_le_of_unique_maximalTwoLocal hFK hu.2.2 q hq hker
    P R hp hn (by rw [he]) hFP
  refine ⟨hPM,image_normal_in_of_preimage_normalizes hFK q hq P hFP ?_⟩
  exact (le_inf hPM ((map_subtype_le _).trans hKN)).trans (normalizes_oddActorResidual L A)

/-- A nontrivial centered commutator module rules out the actual PSU₅(4)
cover containing the odd-actor residual with its unitary quotient. -/
theorem no_unitary_five_centered_residual
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    {L A K W : Subgroup G} (hKN : K ≤ normalizer (A : Set G))
    (hFK : oddActorResidual L A ≤ K)
    (hWF : W ≤ (oddActorResidual L A).pCoreIn 2) (hne : W ≠ ⊥)
    (hcomm : W = ⁅W,oddActorResidual L A⁆)
    (hcent : W ≤ centralizer ((oddActorResidual L A).pCoreIn 2 : Set G))
    (hS : ¬ Group.IsSolvable S)
    (π : oddActorResidual L A →* S) (hπ : Function.Surjective π)
    {s : ℕ} (hs : 2 ≤ s) (hsu : ClassicalGroup.IsPSU S 3 (2 ^ s))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hmodel : ClassicalGroup.IsPSU (K ⧸ center K) 5 4) : False := by
  obtain ⟨E,hE,hfin,J,hcard,hconj,⟨e⟩⟩ := hmodel
  have hc : Nat.card E = 16 := hcard
  let := Theory.SpecificGroups.UnitaryFive.charP_two_of_card_sixteen hc
  obtain ⟨a⟩ := Theory.SpecificGroups.UnitaryFive.projective_equiv_identity_four J hc hconj
  let t := e.trans a
  let r := residualQuotientMap hFK t
  let := residualQuotientMap_kernel_solvable hFK t
  obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm t
  obtain ⟨_,g,hg⟩ := unitary_five_line_representation hS π hπ hs hsu
    (HermitianForm.IdentityGram.identityGram J) hc hconj rfl _ hp hpne r hnorm
  let q := (MulAut.conj g).toMonoidHom.comp (t.toMonoidHom.comp (QuotientGroup.mk' (center K)))
  have hq : Function.Surjective q := (MulAut.conj g).surjective.comp
    (t.surjective.comp (QuotientGroup.mk'_surjective _))
  have hk : q.ker ≤ center K := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply t.injective
    apply (MulAut.conj g).injective
    exact hx.trans (by simp only [map_one])
  let P := Theory.SpecificGroups.UnitaryFive.lineParabolic (HermitianForm.IdentityGram.identityGram J)
  let v := q.comp (inclusion hFK)
  have hv : v.range ≤ P := by
    simpa only [v,q,r,residualQuotientMap,MonoidHom.comp_assoc,MonoidHom.range_comp] using hg
  have hnormP := (central_quotient_parabolic_normality hKN hFK hu q hq hk P
    (Theory.SpecificGroups.UnitaryFive.lineParabolic_isTwoLocal _ rfl) hv).2
  let f := v.codRestrict P (fun x => hv ⟨x,rfl⟩)
  have hfRange : f.range = v.range.subgroupOf P := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨y,rfl⟩
    · rintro ⟨y,hy⟩
      exact ⟨y,Subtype.ext hy⟩
  let : f.range.Normal := hfRange.symm ▸ hnormP
  let F := oddActorResidual L A
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  have hfker : f.ker ≤ center F := by
    intro x hx
    have hxk : inclusion hFK x ∈ center K := hk (congrArg Subtype.val hx)
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (congrArg K.subtype (mem_center_iff.mp hxk (inclusion hFK y)))
  have hFn : ¬ Group.IsSolvable F := fun hh => by
    let := hh
    exact hS (Group.isSolvable_of_surjective hπ)
  have hWF' : W ≤ F := hWF.trans (pCoreIn_le 2 F)
  have hWc : W.subgroupOf F ≤ centralizer (pCore 2 F : Set F) := by
    intro w hw x hx
    exact Subtype.ext (hcent hw _ (mem_map_of_mem F.subtype hx))
  have he : W.subgroupOf F = ⁅W.subgroupOf F,⊤⁆ := by
    apply map_injective F.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWF',← MonoidHom.range_eq_map,range_subtype]
    exact hcomm
  have hb := Theory.SpecificGroups.UnitaryFive.line_no_centered_commutator
    (HermitianForm.IdentityGram.identityGram J) hconj hc rfl hFn f hfker
    (W.subgroupOf F) hWc he
  apply hne
  have hm := congrArg (map F.subtype) hb
  simpa only [map_subgroupOf_eq_of_le hWF',Subgroup.map_bot] using hm

end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
