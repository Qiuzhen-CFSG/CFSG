module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.OrbitDegree
public import Theory.SpecificGroups.Suzuki.TwoRank
public import Theory.SpecificGroups.Suzuki.RootOvoidGeometry

/-!
# The normal Suzuki Borel orbit bound

The two-core quotient of a normal Sylow supplement acts faithfully on its
centerless Suzuki image. Its elementary two-rank is therefore at most the
Suzuki field degree. The ovoid gives the actual doubly transitive Borel orbit
used to exclude this row for the nonabelian closure in Chapter 14.

Source: Aschbacher--Smith, the normal Bender alternatives preceding 14.2.16,
printed pp.982--986.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]

/-- The original two-core quotient has Suzuki automorphism two-rank. -/
theorem ModelBorelPair.suzuki_actor_two_rank
    (S : Sylow 2 H) (N K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (S : Subgroup H) = ⊤) (hcore : sourceKernel N = pCore 2 H)
    {m : ℕ} (hmpos : 0 < m)
    (hm : ModelBorelPair N K (SuzukiBorelSubgroup m)) :
    primeRank 2 (H ⧸ pCore 2 H) ≤ 2*m+1 := by
  obtain ⟨e,_⟩ := hm
  let q := QuotientGroup.mk' (pCore 2 H)
  let L := K.map q
  let S' := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have he : Nonempty (L ≃* SuzukiMatrixGroup m) := by
    have transport (J J' : Subgroup H) [J.Normal] [J'.Normal] (heq : J = J') :
        Nonempty (K.map (QuotientGroup.mk' J) ≃* SuzukiMatrixGroup m) →
        Nonempty (K.map (QuotientGroup.mk' J') ≃* SuzukiMatrixGroup m) := by
      subst J'
      exact id
    exact transport (sourceKernel N) (pCore 2 H) hcore ⟨e⟩
  obtain ⟨eL⟩ := he
  have hLs : L ⊔ (S' : Subgroup (H ⧸ pCore 2 H)) = ⊤ := by
    change K.map q ⊔ (S : Subgroup H).map q = ⊤
    rw [←Subgroup.map_sup,hgen]
    exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)
  have hmodel : BenderSuzuki.IsSimpleBenderGroup (SuzukiMatrixGroup m) :=
    .isSuzuki ⟨m, hmpos, ⟨MulEquiv.refl _⟩⟩
  have hSZ : center (SuzukiMatrixGroup m) = ⊥ := by
    let := hmodel.isSimple
    rcases (inferInstance : (center (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact False.elim (hmodel.not_commutative (fun x y => by
        have hx : x ∈ center (SuzukiMatrixGroup m) := by rw [h]; trivial
        exact (mem_center_iff.mp hx y).symm))
  have hLZ : center L = ⊥ := by
    apply le_bot_iff.mp
    intro k hk
    have hh : eL k ∈ center (SuzukiMatrixGroup m) := (centerCongr eL ⟨k,hk⟩).property
    rw [hSZ,mem_bot] at hh
    exact mem_bot.mpr (eL.injective (by simpa only [map_one] using hh))
  let C := centralizer (L : Set (H ⧸ pCore 2 H))
  have hCL : C ≤ S' := centralizer_le_sylow_of_centerless_supplement L S' hLs hLZ
  have hCP : IsPGroup 2 C := S'.isPGroup'.of_injective
    (inclusion hCL) (inclusion_injective hCL)
  have hCp : C ≤ pCore 2 (H ⧸ pCore 2 H) := le_sSup ⟨inferInstance,hCP⟩
  have hC : C = ⊥ := le_bot_iff.mp (hCp.trans_eq (pCore_quotient_pCore_eq_bot 2))
  let a : (H ⧸ pCore 2 H) →* MulAut (SuzukiMatrixGroup m) :=
    (MulAut.congr eL).toMonoidHom.comp MulAut.conjNormal
  have ha : Function.Injective a := (MulAut.congr eL).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot L hC)
  exact (Theory.GroupTheory.primeRank_le_of_injective 2 a ha).trans
    (suzuki_automorphism_two_rank m hmpos)

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
