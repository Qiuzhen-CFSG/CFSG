module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.Frame
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveTypes
public import Theory.SpecificGroups.Alternating.DihedralFiveCentralizer

/-!
# The literal centralizer of the dihedral edge subgroup

Choose the order-five rotation subgroup E of the frame's D₁₀ subgroup B.
Both B and C_G(B) lie in N_G(E). The adjacent endpoints generate an A₄
inside C_G(B), excluding the `D₁₀ × D₁₀` normalizer by divisibility by three.
Inside the remaining `D₁₀ × A₅` normalizer the commuting A₄ forces B to be
the first factor. Hence the literal ambient centralizer is A₅.

Source: Aschbacher, *Sporadic Groups* (1994), 47.10, printed p.266.
The two normalizer alternatives from 47.2 remain an explicit premise;
their construction from 47.1 belongs to the prime-local source calculation.
-/

public section

open Subgroup Theory.GroupTheory.GraphUniquenessSystem
open Theory.SpecificGroups.Alternating.DihedralFiveCentralizer
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers

/-- The five-local normalizers identify the actual subgroup `F.K = C_G(F.B)`.
The inclusions of both endpoints are the literal `F.endpoints_le he` maps. -/
theorem edgeFrame_centralizer_equiv {G : Type*} [Group G] [Finite G] {D : Seed G}
    (F : EdgeFrame D)
    (he : Nonempty (edgeFixer G D.base F.y ≃* alternatingGroup (Fin 5)))
    (h₅ : FiveNormalizerTypes G) : Nonempty (F.K ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨E, hE, hEB, hBN⟩ := exists_five_subgroup F.B F.dihedral.some
  have hKN : F.K ≤ normalizer (E : Set G) :=
    (centralizer_le (show (E : Set G) ⊆ (F.B : Set G) from hEB)).trans
      (centralizer_le_normalizer _)
  have hAN : D.X ⊔ F.y.val ≤ normalizer (E : Set G) := (F.endpoints_le he).trans hKN
  rcases h₅ E hE with eN | eN
  · exact centralizer_equiv_of_commuting_four (D.X ⊔ F.y.val) F.B (normalizer (E : Set G))
      hAN hBN hKN F.adjacent.2.some F.dihedral.some eN.some (F.endpoints_le he)
  · have hdiv := card_dvd_of_le ((show D.X ≤ D.X ⊔ F.y.val from le_sup_left).trans hAN)
    rw [D.card_X, Nat.card_congr eN.some.toEquiv, Nat.card_prod, DihedralGroup.nat_card] at hdiv
    norm_num at hdiv

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers
