module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.WeakClosureKernel
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.WeakClosureRank

/-!
# WeakClosureKernel at the original ambient group and Sylow subgroup

These are the same source arguments as `WeakClosureKernel`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 ChapterE BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable (S : Setup T L V) (D : S.LocalAnalysis)

variable (structural : Structural1222At KnownSimple.IsKnownSimple T)

omit [Finite G] in

private theorem centralizer_map_at (U : Subgroup G) (e : G ≃* G) :
    (centralizer (U : Set G)).map e.toMonoidHom = centralizer (U.map e.toMonoidHom : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro y hy
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

include S D structural in

theorem conjugate_rank_three_centralizer_at (g : G) {U : Subgroup G}
    (hUV : U ≤ V.map (MulAut.conj g).toMonoidHom)
    (hr : Nat.log 2 (Nat.card U) = 3)
    (hesc : ¬ centralizer (U : Set G) ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) ⊓ centralizer (U : Set G) =
      centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  let e := MulAut.conj g
  let U₀ := U.comap e.toMonoidHom
  have hm : U₀.map e.toMonoidHom = U := map_comap_eq_self_of_surjective e.surjective U
  have h₀ : U₀ ≤ V := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hUV hx
    exact (e.injective he) ▸ hy
  have he₀ : ¬ centralizer (U₀ : Set G) ≤ normalizer (V : Set G) := by
    intro h
    apply hesc
    have hh := map_mono (f := e.toMonoidHom) h
    rwa [centralizer_map_at, hm, map_equiv_normalizer_eq] at hh
  have hr₀ : Nat.log 2 (Nat.card U₀) = 3 := by
    rw [← hm, card_map_of_injective e.injective] at hr
    exact hr
  have he := D.model.normalizer_inf_centralizer_of_weight_four_rank_three h₀
    (weight_four_of_escaping_centralizer_at S D structural h₀ he₀) hr₀
  have hh := congrArg (fun H : Subgroup G => H.map e.toMonoidHom) he
  rwa [map_inf _ _ _ e.injective, centralizer_map_at, centralizer_map_at,
    map_equiv_normalizer_eq, hm] at hh

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

