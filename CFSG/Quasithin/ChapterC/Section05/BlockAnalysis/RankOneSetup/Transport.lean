module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Setup
/-!
# Transporting a marked rank-one setup through Baumann heredity

All fields of the setup depend on R through its literal Baumann subgroup.
Equality of that subgroup therefore preserves the original parameter map,
module projection and quotient action. The proof reassembles those same
fields after dependent transport; no new coordinate choice is made.

Source: Aschbacher–Smith C.5.4, printed p.155.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
open ConjugateSource.RankOne
variable {G F : Type*} [Group G] [Field F]
theorem setup_of_baumann_eq (R T K : Subgroup G) (heq : S T = S R) (h : Setup T K F) :
    Nonempty (Setup R K F) := by
  rcases h with ⟨c,hb,hm,hn,hcore,q,hq,hker,himage⟩
  rcases c with ⟨hnU,param,hparam,hparamker,proj,hproj,hprojker,he⟩
  simp only [ActionCoordinates.IsInternal] at hb
  dsimp only [Q] at hcore hker
  have he' : ∀ (s : S T) (v : U K)
      (hv : (s : G) * (v : G) * (s : G)⁻¹ ∈ U K),
      (proj ⟨_,hv⟩).toAdd =
        ![(proj v).toAdd 0 + (param s).toAdd * (proj v).toAdd 1,(proj v).toAdd 1] := by
    intro s v hv
    exact he s v
  clear he
  revert hnU param hparam hparamker proj hproj hprojker he' hb hm hn hcore q hq hker himage
  rw [heq]
  intro hm hn hcore q hq hker himage hnU param hparam hparamker proj hproj hprojker hb he
  exact ⟨⟨⟨hnU,param,hparam,hparamker,proj,hproj,hprojker,fun s v => he s v _⟩,hb,hm,hn,hcore,q,hq,hker,himage⟩⟩
end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
