module
public import Theory.GroupTheory.SylowKernelCore
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Assembly
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.FourModuleOrbit

/-!
# The actual rank-one blocks in the four-module orbit

Transporting the characteristic commutator layer carries the original
TH-action on the blocks to the literal modules. Their elementarity and
commuting block supports supply the first two commutator facts. The
proved C.5.6(1) centralizer supplies the cross-commutation fact, so the
four-module theorem eliminates the cyclic and dihedral alternatives
without assuming a permutation table or either of those conclusions.

Source: Aschbacher–Smith, C.5.6(7), printed p.158.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G]
private theorem U_eq (K : Subgroup G) : U K = ⁅K.pCoreIn 2, K⁆ := by
  unfold U blockU
  rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  rfl

theorem U_map_equiv (K : Subgroup G) (e : G ≃* G) :
    (U K).map e.toMonoidHom = U (K.map e.toMonoidHom) := by
  rw [U_eq, U_eq, map_commutator,
    map_pCoreIn_of_injective 2 K e.toMonoidHom e.injective]

variable [Finite G] {R K L : Subgroup G} {F : Type*} [Field F]

theorem Setup.fourModuleSourceInputs
    (h : Setup R K F) (hKL : L ≤ centralizer (K : Set G)) (hLS : U L ≤ ChapterB.baumann R)
    (M₀ T_H : Subgroup G) (x : G) (hx : x ∈ M₀)
    (hxR : x ∈ normalizer (R : Set G)) (hindex : T_H.relIndex M₀ = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M₀, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    FourModuleOrbit.SourceInputs M₀ T_H (U K) (U L) x := by
  have hm (g : G) : (U K).conjBy g = U (K.conjBy g) :=
    U_map_equiv K (MulAut.conj g)
  refine ⟨hindex, hx, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases hpair g hg with he | he
    · exact Or.inl ((hm g).trans (congrArg U he))
    · exact Or.inr ((hm g).trans (congrArg U he))
  · obtain ⟨t, ht, he⟩ := ht
    exact ⟨t, ht, (hm t).trans (congrArg U he)⟩
  · let : IsElementaryAbelian 2 (U K) := h.elementary
    exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer _)
  · intro he
    apply hnc
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
  · apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    exact (map_subtype_le _).trans (hKL.trans (centralizer_le (map_subtype_le _)))
  · apply commutator_eq_bot_iff_le_centralizer.mpr
    exact le_centralizer_iff.mp ((le_inf hLS ((map_subtype_le _).trans hKL)).trans
      (h.factorization hxR hnc).centralizes)
omit [Finite G] in
theorem second_noncommuting {M T U V : Subgroup G} {x : G}
    (h : FourModuleOrbit.SourceInputs M T U V x) :
    ¬ V.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (V : Set G) := by
  obtain ⟨t, ht⟩ := FourModuleOrbit.source_setup h.toInputs
  have htable := ht.table t
  have h02 : FourModuleOrbit.action h.toInputs t 0 = 1 ∧
      FourModuleOrbit.action h.toInputs t 2 = 3 := by
    rcases htable with h0 | h1 | h2 | h3
    · have hh := ht.t_zero
      rw [h0.1] at hh
      contradiction
    · exact ⟨h1.1, h1.2.2.1⟩
    · have hh := ht.t_zero
      rw [h2.1] at hh
      contradiction
    · have hh := ht.t_zero
      rw [h3.1] at hh
      contradiction
  have hh := ht.invariant t 0 2 ht.noncommuting
  rw [h02.1, h02.2] at hh
  change ⁅V, V.map (MulAut.conj x⁻¹).toMonoidHom⁆ ≠ ⊥ at hh
  exact fun hc => hh (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G} {F : Type*} [Field F]

/-- The original two rank-one blocks yield the regular Klein-four action and
commuting conjugate-generated factors in C.5.6(7). -/
theorem Setup.four_module_geometry
    (h : Setup R K F) (hKL : L ≤ centralizer (K : Set G)) (hLS : U L ≤ ChapterB.baumann R)
    (M₀ T_H : Subgroup G) (x : G) (hx : x ∈ M₀)
    (hxR : x ∈ normalizer (R : Set G)) (hindex : T_H.relIndex M₀ = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M₀, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let d := h.fourModuleSourceInputs hKL hLS M₀ T_H x hx hxR hindex hpair ht hnc
    IsKleinFour (FourModuleOrbit.action d.toInputs).range ∧
      IsKleinFour (M₀ ⧸ (FourModuleOrbit.action d.toInputs).ker) ∧
      (∀ i : Fin 4,
        (FourModuleOrbit.modules (U K) (U L) x i).conjBy (x ^ 2) =
          FourModuleOrbit.modules (U K) (U L) x i) ∧
      ⁅U K ⊔ (U K).conjBy x⁻¹,
        U L ⊔ (U L).conjBy x⁻¹⁆ = ⊥ := by
  have he := (h.fourModuleSourceInputs hKL hLS M₀ T_H x hx hxR hindex hpair ht hnc).conclusion
  exact ⟨he.1, he.2.1, he.2.2.2.2.1, he.2.2.2.2.2⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
