module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori.RankOne
public import Theory.SpecificGroups.Suzuki.SplitNormalizerGeometry
/-!
# Reflections of the marked rank-one tori

The existing projective PSL₂ Weyl element lies outside the triangular Borel
and inverts its specified diagonal embedding. The actual Suzuki Weyl element
swaps the two distinguished ovoid points and inverts every element of the
named split torus, hence also the chosen units parametrization. The Suzuki
parameter remains 2m+1 with m>0; no alternative Borel or torus is selected.

Source: Aschbacher--Smith E.6.27, printed p.257, with the marked Borel
models from E.2.2. These witnesses feed the same chosen cyclic subgroup
and Hall-subgroup lifting in the original parabolic consumer.
-/
public section
open Subgroup BenderSuzuki.Converse BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori
variable {F : Type*} [Field F]

theorem exists_psl2Torus_reflection [CharP F 2] :
    ∃ w : PSL2 F, w ∉ PBorel F ∧ ∀ a : Fˣ,
      w * (psl2Torus a : PSL2 F) * w⁻¹ = (psl2Torus a : PSL2 F)⁻¹ := by
  refine ⟨PWeyl F, PWeyl_notMem_PBorel, ?_⟩
  intro a
  change pi F (weyl F) * pi F (torHom F a) * (pi F (weyl F))⁻¹ = (pi F (torHom F a))⁻¹
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
  apply congrArg (pi F)
  rw [weyl_inv,← map_inv]
  apply Subtype.ext
  change (!![0,1;1,0] : Matrix (Fin 2) (Fin 2) F) *
    !![(a:F),0;0,((a⁻¹:Fˣ):F)] * !![0,1;1,0] =
    !![((a⁻¹:Fˣ):F),0;0,(a:F)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]

theorem exists_suzukiTorus_reflection (m : ℕ) (hm : 0 < m) :
    ∃ w : SuzukiMatrixGroup m, w ∉ SuzukiBorelSubgroup m ∧
      ∀ a, w * (suzukiTorus m hm a : SuzukiMatrixGroup m) * w⁻¹ =
        (suzukiTorus m hm a : SuzukiMatrixGroup m)⁻¹ := by
  refine ⟨suzukiWeyl m, ?_, ?_⟩
  · intro hw
    have he : suzukiWeyl m • suzukiOvoidInfinity m = suzukiOvoidInfinity m := by
      simpa only [suzukiBorelSubgroup_eq_stabilizer m hm,MulAction.mem_stabilizer_iff] using hw
    rw [suzukiWeyl_smul_infinity] at he
    exact suzukiOvoidInfinity_ne_zero m he.symm
  · intro a
    rw [suzukiWeyl_inv]
    exact suzukiWeyl_conj_splitTorus m ((suzukiSplitTorus_equiv_units m hm).some a)
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori
