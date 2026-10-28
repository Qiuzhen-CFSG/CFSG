module
public import CFSG.Quasithin.Chapter4.Section04.OddActorResidual
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The literal component quotient of the odd-actor residual

The source factorization L = L_A O₂(L) makes restriction of the original
quotient map onto L/O₂(L) surjective. Its kernel embeds in O₂(L), so lifting
the trivial two-core of L/O₂(L) identifies that kernel with O₂(L_A).
The induced isomorphism retains the original quotient formula on every
element of L_A; no replacement of the perfect residual by a two-core occurs.

Source: Aschbacher--Smith 4.4.5--6, p.620, and 4.2.12--13, pp.610--612.
-/

public section
namespace CFSG.Quasithin.Chapter4.Section04
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- Restricting the actual quotient map identifies L_A/O₂(L_A) with
L/O₂(L), compatibly with the original ambient inclusion. -/
theorem chosen_oddActorResidual_quotient
    {κ : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 κ T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G)) :
    ∃ e : (oddActorResidual L A ⧸ pCore 2 (oddActorResidual L A)) ≃* (L ⧸ pCore 2 L),
      ∀ x : oddActorResidual L A,
        e (QuotientGroup.mk' (pCore 2 (oddActorResidual L A)) x) =
          QuotientGroup.mk' (pCore 2 L)
            ⟨x.val,((oddActorResidual_le L A).trans inf_le_left) x.property⟩ := by
  let R := oddActorResidual L A
  have hRL : R ≤ L := (oddActorResidual_le L A).trans inf_le_left
  let f : R →* L ⧸ pCore 2 L := (QuotientGroup.mk' (pCore 2 L)).comp (inclusion hRL)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) y
    obtain ⟨hc,_,_,_⟩ := chosen_oddActorResidual_cover h D A hAN hcomm hodd hAV
    have hl : l.val ∈ (L : Set G) := l.property
    have hlc : l.val ∈ (R : Set G) * (L.pCoreIn 2 : Set G) := hc ▸ hl
    obtain ⟨r,hr,c,hc,he⟩ := hlc
    refine ⟨⟨r,hr⟩,QuotientGroup.eq.mpr ?_⟩
    obtain ⟨c',hc',hec⟩ := hc
    have heq : (⟨r,hRL hr⟩ : L)⁻¹ * l = c' := by
      apply Subtype.ext
      change r⁻¹ * l.val = c'.val
      rw [← he,← hec]
      simp
    change (⟨r,hRL hr⟩ : L)⁻¹ * l ∈ pCore 2 L
    rwa [heq]
  let j : f.ker →* pCore 2 L :=
    { toFun := fun x => ⟨⟨x.val.val,hRL x.val.property⟩,
        (QuotientGroup.eq_one_iff _).mp x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : pCore 2 L => z.val.val) he))
  have hk : IsPGroup 2 f.ker := pCore_isPGroup.of_injective j hj
  have hker : f.ker = pCore 2 R := by
    have hh := f.comap_pCore_of_ker_isPGroup hf hk
    simpa only [pCore_quotient_pCore_eq_bot,MonoidHom.comap_bot] using hh
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf),?_⟩
  intro x
  rfl

end CFSG.Quasithin.Chapter4.Section04
