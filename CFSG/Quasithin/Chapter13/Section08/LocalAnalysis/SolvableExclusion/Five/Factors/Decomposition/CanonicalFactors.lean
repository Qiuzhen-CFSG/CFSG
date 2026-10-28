module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Lift
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDecomposition

/-!
# The canonical five-factors in the actual star action

These are precisely the subgroups of P* of order five lying in F(H*)
whose actual moved subgroup on UH/V₁ has order sixteen. The action
is the specified `StarAction`, pulled back to H*, and its supports
agree with those of the literal images in the quotient automorphism group.
Conjugation preserves the family whenever P* is normal, so its generated
subgroup is normal and lies in P*.

These definitions do not assert that this family generates P*. That
is the remaining offender reduction required before applying the
factorization assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), D.2.12,
printed pp.183–184, and 13.8.13, p.951.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
open ChapterD
variable {G : Type*} [Group G]
variable {H UH V₁ : Subgroup G} [(V₁.subgroupOf UH).Normal]

@[instance_reducible] def StarAction.starMulAction (a : StarAction H UH V₁) :
    MulDistribMulAction (Source.Hstar H) (UH ⧸ V₁.subgroupOf UH) :=
  MulDistribMulAction.compHom _ a.action

theorem StarAction.starMulAction_faithful (a : StarAction H UH V₁)
    (hf : Function.Injective a.action) :
    letI := a.starMulAction
    FaithfulSMul (Source.Hstar H) (UH ⧸ V₁.subgroupOf UH) := by
  let := a.starMulAction
  exact ⟨fun he => hf (MulEquiv.ext he)⟩

theorem StarAction.star_support_eq (a : StarAction H UH V₁)
    (X : Subgroup (Source.Hstar H)) :
    letI := a.starMulAction
    commutatorAction X (UH ⧸ V₁.subgroupOf UH) =
      commutatorAction (X.map a.action) (UH ⧸ V₁.subgroupOf UH) := by
  let := a.starMulAction
  unfold commutatorAction commutatorSubgroup
  congr 1
  ext w
  constructor
  · rintro ⟨x, u, hu, rfl⟩
    exact ⟨⟨a.action x, mem_map_of_mem _ x.property⟩, u, hu, rfl⟩
  · rintro ⟨x, u, hu, rfl⟩
    obtain ⟨y, hy, he⟩ := x.property
    refine ⟨⟨y, hy⟩, u, hu, ?_⟩
    change u⁻¹ * (x : MulAut _) u = u⁻¹ * a.action y u
    rw [he]

def StarAction.canonicalFiveFactors (a : StarAction H UH V₁) (P : Subgroup G) :
    Set (Subgroup (Source.Hstar H)) :=
  {X | X ≤ Source.starImage H P ∧ X ≤ fittingSubgroup (Source.Hstar H) ∧
    Nat.card X = 5 ∧
    Nat.card (commutatorAction (X.map a.action) (UH ⧸ V₁.subgroupOf UH)) = 16}

def StarAction.canonicalFiveGroup (a : StarAction H UH V₁) (P : Subgroup G) :
    Subgroup (Source.Hstar H) := sSup (a.canonicalFiveFactors P)

theorem StarAction.canonicalFiveGroup_eq_iSup (a : StarAction H UH V₁) (P : Subgroup G) :
    a.canonicalFiveGroup P = ⨆ X : a.canonicalFiveFactors P, X.val := sSup_eq_iSup' _

theorem StarAction.canonicalFiveFactors_iff (a : StarAction H UH V₁) (P : Subgroup G)
    (X : Subgroup (Source.Hstar H)) :
    letI := a.starMulAction
    X ∈ a.canonicalFiveFactors P ↔
      X ≤ Source.starImage H P ∧
      X ∈ smallSupportFactors (Source.Hstar H) (UH ⧸ V₁.subgroupOf UH) 2 := by
  let := a.starMulAction
  simp only [canonicalFiveFactors, Set.mem_ofPred_eq, smallSupportFactors, a.star_support_eq]
  rfl

theorem StarAction.canonicalFiveGroup_le (a : StarAction H UH V₁) (P : Subgroup G) :
    a.canonicalFiveGroup P ≤ Source.starImage H P :=
  sSup_le fun _ hX => hX.1

theorem StarAction.canonicalFiveFactors_conjBy (a : StarAction H UH V₁)
    (P : Subgroup G) [(Source.starImage H P).Normal]
    {X : Subgroup (Source.Hstar H)} (hX : X ∈ a.canonicalFiveFactors P)
    (g : Source.Hstar H) : X.conjBy g ∈ a.canonicalFiveFactors P := by
  let := a.starMulAction
  rw [a.canonicalFiveFactors_iff] at hX ⊢
  refine ⟨?_, smallSupportFactors_conjBy hX.2 g⟩
  rintro x ⟨y, hy, rfl⟩
  exact (inferInstance : (Source.starImage H P).Normal).conj_mem y (hX.1 hy) g

instance StarAction.canonicalFiveGroup_normal (a : StarAction H UH V₁)
    (P : Subgroup G) [(Source.starImage H P).Normal] :
    (a.canonicalFiveGroup P).Normal := by
  constructor
  intro x hx g
  have hm : (a.canonicalFiveGroup P).map (MulAut.conj g).toMonoidHom ≤
      a.canonicalFiveGroup P := by
    rw [a.canonicalFiveGroup_eq_iSup, Subgroup.map_iSup]
    apply iSup_le
    intro X
    exact le_iSup_of_le ⟨X.val.conjBy g, a.canonicalFiveFactors_conjBy P X.property g⟩ le_rfl
  exact hm (mem_map_of_mem _ hx)

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
