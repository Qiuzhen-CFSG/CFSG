module
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.NormalizerAction
public import Theory.GroupTheory.NormalCentralQuotientAction

/-!
# The kernel Sylow in the literal component quotient action

The kernel of conjugation on X/O₂(X) is exactly the source section
centralizer. For a normal perfect X and an ambient Sylow T, A.4.2(4--5)
identifies O₂(XT) with the image of a Sylow subgroup of this kernel.
No centerlessness of X/O₂(X) is required.

Source: Aschbacher--Smith A.4.2, printed p.57; the application in the
paragraph preceding original 4.3.15, printed p.618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The full quotient action has exactly the literal section-centralizer kernel. -/
theorem normalQuotientAction_ker (X : Subgroup G) [X.Normal] :
    (normalQuotientAction X (pCore 2 X)).ker = twoSectionCentralizer X ⊤ := by
  ext g
  constructor
  · intro hg
    refine ⟨mem_top _, le_normalizer_of_normal (mem_top g), ?_⟩
    intro x hx
    let x' : X := ⟨x,hx⟩
    let b : X := MulAut.conjNormal g x' * x'⁻¹
    have hb : b ∈ pCore 2 X := by
      apply (QuotientGroup.eq_one_iff b).mp
      have h := DFunLike.congr_fun (show normalQuotientAction X (pCore 2 X) g = 1 from hg)
        (QuotientGroup.mk' (pCore 2 X) x')
      rw [normalQuotientAction_apply_mk] at h
      change QuotientGroup.mk' (pCore 2 X) b = 1
      simp only [b,map_mul,map_inv,MulAut.one_apply,h,mul_inv_cancel]
    exact ⟨b,hb,rfl⟩
  · intro hg
    apply MulEquiv.ext
    intro q
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) q
    rw [normalQuotientAction_apply_mk]
    change QuotientGroup.mk' (pCore 2 X) (MulAut.conjNormal g x) =
      QuotientGroup.mk' (pCore 2 X) x
    apply mul_inv_eq_one.mp
    rw [← map_inv, ← map_mul]
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨z,hz,he⟩ := hg.2.2 x x.property
    exact (Subtype.ext he : z = MulAut.conjNormal g x * x⁻¹) ▸ hz

private theorem perfect_twoPerfect {H : Type*} [Group H] [Finite H]
    [Group.IsPerfect H] : IsPPerfect 2 H := by
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (H ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (H ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (H ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (H ⧸ N) inferInstance

/-- A.4.2 supplies a Sylow subgroup of the actual action kernel. -/
theorem sylow_normalQuotientAction_ker (X : Subgroup G) [X.Normal]
    [Group.IsPerfect X] (T : Sylow 2 G) :
    ∃ P : Sylow 2 (normalQuotientAction X (pCore 2 X)).ker,
      (P : Subgroup _).map (normalQuotientAction X (pCore 2 X)).ker.subtype =
        (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have h := sylow_core_sectionCentralizer T X perfect_twoPerfect le_normalizer_of_normal
  rwa [normalizer_eq_top, ← normalQuotientAction_ker] at h
end CFSG.Quasithin.ChapterA.Section04

end
