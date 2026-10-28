module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.Source
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.SourceInputs
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs

/-!
# The intrinsic three-complement sieve from genuine Theorems A and C

Theorem A gives strong quasithinness of the actual semisimple central
quotient of L/O₂(L). The inherited K-group property and quasisimplicity
then satisfy every genuine Theorem C hypothesis. The source-model adapter
and complete invariant-three dispatcher give the adequate conclusion.

Source: Aschbacher–Smith A.2.1–3 and Proposition 1.3.4, pp.33,511.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.Source
universe u

/-- Genuine A and C, applied to the literal component quotient, supply the
complete model conclusion needed by the intrinsic p=3 sieve. -/
theorem alternatives_of_theoremAC {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {T X P H L : Subgroup G}
    (h : LocalInput 3 T X P H) (hH : IsSQTK κ H)
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hq : IsQuasisimple (XiQuotient L)) (hPL : P ≤ L) (hcomm : ⁅L, P⁆ = L)
    (hA : ChapterA.Section02.TheoremA κ (XiQuotient L))
    (hC : ChapterA.Section02.TheoremC κ (XiQuotient L ⧸ center (XiQuotient L))) :
    Alternatives 3 T P L ∨ HeldAlternative 3 T P L := by
  let _ : IsQuasisimple (XiQuotient L) := hq
  let _ : IsSimpleGroup (XiQuotient L ⧸ center (XiQuotient L)) := hq.simple
  let _ : Group.IsPerfect (XiQuotient L ⧸ center (XiQuotient L)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hna : ¬ IsMulCommutative (XiQuotient L ⧸ center (XiQuotient L)) :=
    Group.IsPerfect.not_isMulCommutative _
  exact alternatives_of_local_input h hH hT hLH hLn hq hPL hcomm
    (ChapterA.Section03.SourceComponents.sourceTheoremC_to_local hna
      (QuasisimpleInvolutions.quotient_model (component_quotient_sqtk hH hLH) hA hC))

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.Source
