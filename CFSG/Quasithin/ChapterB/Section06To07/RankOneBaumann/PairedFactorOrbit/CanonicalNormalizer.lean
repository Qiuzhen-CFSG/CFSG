module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.Residuals
public import Theory.GroupTheory.SolvableResidual
/-!
# Normalization of the selected canonical factor

The solvable residual of a factor preimage is characteristic in that
preimage. Its normality in the offender preimage therefore survives the
canonical selection. If two conjugates cover the ambient two-residual,
that residual normalizes the selected factor and every conjugate of it.
This keeps the selected component in the original paired E.2.3 argument.
Source: Aschbacher--Smith E.2.3 and 10.2.3(4), pp.216--217 and746--747.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
variable {G H : Type*} [Group G] [Group H]

/-- The offender preimage normalizes the actual selected solvable-residual lift. -/
theorem canonical_factor_normalized (q : G →* H) (Y : Subgroup H)
    (A : Subgroup Y) [A.Normal] (K : Subgroup G)
    (hK : (solvableResidual (factorPreimage q Y A)).map
      (factorPreimage q Y A).subtype = K) :
    Y.comap q ≤ normalizer (K : Set G) := by
  have hA : factorPreimage q Y A ≤ Y.comap q :=
    comap_mono (map_subtype_le A)
  have hn := (normal_subgroupOf_iff_le_normalizer hA).mp (factorPreimage_normal q Y A)
  rw [← hK]
  exact hn.trans (normalizer_le_normalizer_characteristic_image
    (factorPreimage q Y A) (solvableResidual (factorPreimage q Y A)))

/-- The original two-conjugate cover supplies residual normality, including
all subsequent conjugates of the same selected factor. -/
theorem canonical_factor_residual_normalizes_conjugates
    (q : G →* H) (Y : Subgroup H) [Y.Normal]
    (A : Subgroup Y) [A.Normal] (K : Subgroup G)
    (hK : (solvableResidual (factorPreimage q Y A)).map
      (factorPreimage q Y A).subtype = K)
    (hcover : ∃ t : G, pResidual 2 G = K ⊔ K.map (MulAut.conj t).toMonoidHom) :
    pResidual 2 G ≤ normalizer (K : Set G) ∧
      ∀ t : G, pResidual 2 G ≤ normalizer (K.map (MulAut.conj t).toMonoidHom : Set G) := by
  have hKY : K ≤ Y.comap q := by
    rw [← hK]
    exact (map_subtype_le _).trans (comap_mono (map_subtype_le A))
  have hRY : pResidual 2 G ≤ Y.comap q := by
    obtain ⟨t,ht⟩ := hcover
    rw [ht]
    refine sup_le hKY ?_
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hKY
    rwa [show (Y.comap q).map (MulAut.conj t).toMonoidHom = Y.comap q from
      Subgroup.Normal.map_conj_eq (Y.comap q) t] at hh
  have hn := hRY.trans (canonical_factor_normalized q Y A K hK)
  refine ⟨hn,fun t => ?_⟩
  have hh := (map_mono (f := (MulAut.conj t).toMonoidHom) hn).trans
    (K.le_normalizer_map (MulAut.conj t).toMonoidHom)
  rwa [show (pResidual 2 G).map (MulAut.conj t).toMonoidHom = pResidual 2 G from
    Subgroup.Normal.map_conj_eq (pResidual 2 G) t] at hh
end CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
