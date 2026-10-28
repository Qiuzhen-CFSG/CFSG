module

public import Theory.Representation.NormalElementaryQuotient.BestOffender
public import Theory.GroupTheory.ElementaryThompsonFrattini

/-!
# Thompson normality from a non-FF conjugation quotient

If the faithful action on a normal elementary subgroup has no FF offender,
every maximum elementary subgroup of the Sylow lies in the action kernel.
When that kernel is a two-group, Thompson heredity identifies the Sylow
Thompson subgroup with that of the normal kernel, proving normality.
The quotient homomorphism and its literal centralizer kernel are retained.

Source: Aschbacher--Smith B.2.5--8, printed p.76; application in 14.3.29(2),
printed p.1002, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.NormalElementaryQuotient

/-- A two-group centralizer kernel and a non-FF quotient force Thompson normality. -/
theorem thompson_normal_of_nonFF {A Q : Type*} [Group A] [Finite A] [Group Q]
    (S : Sylow 2 A) (E : Subgroup A) [E.Normal] [IsElementaryAbelian 2 E]
    (f : A →* Q) (hf : Function.Surjective f)
    (hk : f.ker = centralizer (E : Set A)) (hk2 : IsPGroup 2 f.ker) (hES : E ≤ S)
    (hn : ¬ IsFFModule (NormalElementaryQuotient.representation E f hf hk)) :
    (elementaryAbelianMaxJ (S : Subgroup A)).Normal := by
  let : Finite Q := Finite.of_surjective f hf
  have hJ : elementaryAbelianMaxJ (S : Subgroup A) ≤ f.ker := by
    apply sSup_le
    intro B hB
    apply (map_eq_bot_iff B).mp
    by_contra hne
    exact hn ⟨B.map f, (NormalElementaryQuotient.maxElementary_isBestOffender
      E f hf hk S B hES hB hne).isOffender _⟩
  have hKS : f.ker ≤ (S : Subgroup A) := hk2.le_sylow_of_normal S
  rw [← elementaryAbelianMaxJ_eq_of_intermediate (S : Subgroup A) f.ker hJ hKS]
  apply normal_iff_map_conj_eq.mpr
  intro g
  change (elementaryAbelianMaxJ f.ker).map (MulAut.conj g).toMonoidHom = _
  rw [← elementaryAbelianMaxJ_map_equiv (MulAut.conj g) f.ker]
  congr 1
  exact (normal_iff_map_conj_eq.mp f.normal_ker) g


end Representation.NormalElementaryQuotient
