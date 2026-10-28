module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.ThirdExclusion.Geometry
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.FusionConstraints

/-!
# Exclusion of the third nonsplit Held centralizer

The actual third permutation carrier contains the certified group of order
128. An isomorphism from the specified involution centralizer into that
carrier therefore identifies the original Sylow two-subgroup with this model:
its order is already 128 by the original quotient hypotheses.

In the model, square-root counts characterize the central involution inside
every other involution centralizer. Their ambient normalizers consequently
fix it, and the maximal-centralizer argument gives weak closure. This
contradicts the Z-star consequence of the original finite simple hypotheses.
No splitting, recognition, or local-extension classification is assumed.

This excludes one concrete case needed for Huppert--Blackburn, *Finite Groups
III*, XII.1.18(b), p.314, citing Held, J. Algebra 8 (1968), 436--449,
DOI 10.1016/0021-8693(68)90054-9. It does not assert that the list of local
extension candidates is complete.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.ThirdExclusion
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The certified two-subgroup identifies the Sylow type of the actual centralizer. -/
public noncomputable def sylowEquiv (D : LocalData G) (e : D.centralizer ≃* NonsplitModels.Third) :
    D.sylow ≃* Model := by
  let f : Model →* D.centralizer := e.symm.toMonoidHom.comp embedding
  have hf : Function.Injective f := e.symm.injective.comp embedding_injective
  have hcard : Nat.card f.range = 128 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans model_card
  have hp : IsPGroup 2 f.range := IsPGroup.of_card (n := 7) hcard
  let P := Classical.choose hp.exists_le_sylow
  have hP : f.range ≤ (P : Subgroup D.centralizer) :=
    Classical.choose_spec hp.exists_le_sylow
  have hlocal : Nat.card D.localSylow = 128 :=
    (Nat.card_congr (subgroupOfEquivOfLe D.sylow_le_centralizer).toEquiv).trans D.sylow_card
  have hPcard : Nat.card P = 128 :=
    (Nat.card_congr (P.equiv D.localSylow).toEquiv).trans hlocal
  have heq : f.range = (P : Subgroup D.centralizer) :=
    eq_of_le_of_card_ge hP (by rw [hPcard, hcard])
  exact (subgroupOfEquivOfLe D.sylow_le_centralizer).symm.trans
    ((D.localSylow.equiv P).trans
      ((MulEquiv.subgroupCongr heq).symm.trans (MonoidHom.ofInjective hf).symm))

omit [Finite G] in
private theorem involution_image (D : LocalData G) (e : D.sylow ≃* Model) :
    e (D.involution : D.sylow) = modelZ := by
  have he : e (D.involution : D.sylow) ∈ center Model := by
    apply mem_center_iff.mpr
    intro x
    obtain ⟨x, rfl⟩ := e.surjective x
    simpa only [map_mul] using congrArg e (mem_center_iff.mp D.involution.property x)
  apply (model_center _ he).resolve_left
  intro h
  have h' : (D.involution : D.sylow) = 1 := e.injective (h.trans e.map_one.symm)
  exact D.z_ne_one (congrArg Subtype.val h')

/-- The third concrete nonsplit carrier cannot be the actual involution
centralizer under the original finite simple Held hypotheses. -/
public theorem not_nonempty_centralizer_equiv_third [IsSimpleGroup G] (D : LocalData G) :
    ¬ Nonempty (D.centralizer ≃* NonsplitModels.Third) := by
  rintro ⟨e⟩
  let f := sylowEquiv D e
  have hfz := involution_image D f
  have hz2 : (D.involution : D.sylow) * (D.involution : D.sylow) = 1 := by
    apply f.injective
    rw [map_mul, map_one, hfz, modelZ_square]
  have hz1 : (D.involution : D.sylow) ≠ 1 :=
    fun h => D.z_ne_one (congrArg Subtype.val h)
  obtain ⟨t, htz, hconj⟩ := D.exists_distinct_sylow_conjugate
  apply htz
  apply eq_of_isConj_of_squareRootCount D.sylow (D.involution : D.sylow)
    D.involution.property hz2 hz1 _ _ t hconj
  · intro w hw hw2 hw1
    have hwC : f w ∈ center Model := by
      apply mem_center_iff.mpr
      intro x
      obtain ⟨x, rfl⟩ := f.surjective x
      simpa only [map_mul] using congrArg f (mem_center_iff.mp hw x)
    apply f.injective
    rw [hfz]
    apply (model_center _ hwC).resolve_left
    intro h
    exact hw1 (f.injective (h.trans f.map_one.symm))
  · intro v hv hv1 hvz w hw1 hw hc hn
    apply f.injective
    rw [hfz]
    apply model_rigidity (f v) _ _ _ (f w) _ _ _ _
    · simpa only [map_mul, map_one] using congrArg f hv
    · exact fun h => hv1 (f.injective (h.trans f.map_one.symm))
    · exact fun h => hvz (f.injective (h.trans hfz.symm))
    · exact fun h => hw1 (f.injective (h.trans f.map_one.symm))
    · simpa only [map_mul, map_one] using congrArg f hw
    · intro x hx
      obtain ⟨x, rfl⟩ := f.surjective x
      have hx' : x * v = v * x := f.injective (by simpa only [map_mul] using hx)
      simpa only [map_mul] using congrArg f (hc x hx')
    · rw [← hfz, squareRootCount_equiv, squareRootCount_equiv]
      exact hn

end Theory.GroupTheory.HeldM22A10.ThirdExclusion
