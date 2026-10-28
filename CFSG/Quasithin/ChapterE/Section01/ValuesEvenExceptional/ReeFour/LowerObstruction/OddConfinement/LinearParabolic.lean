module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.ReeFour.LowerObstruction.Kernel
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.UnipotentCenter
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.Normality
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.ReeFour.LowerObstruction.OddConfinement.LinearParabolic.RootOrbit

/-!
# The linear-parabolic E1 exclusion in the positive Ree group

The long-root group is the full center of the marked positive subgroup, so
its Borel normalizes it. The genuine Ree Tits system writes an arbitrary
conjugator as Borel--Weyl--Borel. The right Borel factor fixes the root group;
the left factor preserves the full linear parabolic and its radical. The
proved Weyl root-pair calculation therefore puts every root-family member
contained in the full linear parabolic inside its specified radical.

For K in that parabolic, the radical intersection with K is a normal
two-subgroup of K. Thus the root-family member has trivial image under the
literal map to K/O₂(K), and its image has rank zero, excluding rank one.
No assumption of ambient simplicity or geometric containment remains.

Source application: Aschbacher--Smith E.1.14(1), printed p.214/PDF p.225 of
`refs/quasithin.pdf`, citing Aschbacher (1982), Lemma 4.7,
DOI 10.2307/2374202. This supplies the linear input to the independent
`OddConfinement` assembly while preserving the full parabolic and the
intrinsic two-core quotient conventions.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.LowerObstruction
open Subgroup ReeF4 ReeF4.Parabolics ReeF4.EvenInvolutionGeometry
open ReeF4.Parabolics.Binary.FixedGeometry
open ReeF4.SectionGeometry.BNPair

/-- The Borel normalizes the actual root group, since it is the full center of U. -/
theorem borel_le_longRootGroup_normalizer (m : ℕ) (hm : 0 < m) :
    borel m ≤ normalizer (longRootGroup m : Set (Model m)) := by
  rw [← unipotent_center_eq_longRootGroup m hm]
  apply (borel_le_unipotent_normalizer m).trans
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := hx
  let f := (unipotent m).normalizerMonoidHom ⟨g, hg⟩
  have hfy : f y ∈ center (unipotent m) :=
    characteristic_iff_le_comap.mp inferInstance f hy
  exact ⟨f y, hfy, rfl⟩

/-- Bruhat factorization with representatives in the two-generator Weyl subgroup. -/
theorem exists_borel_weyl_borel (m : ℕ) (g : Model m) :
    ∃ b w c : Model m, b ∈ borel m ∧ w ∈ weylSubgroup m ∧ c ∈ borel m ∧
      g = b * w * c := by
  obtain ⟨q, hq⟩ := (titsSystem m).exists_mem_doubleCoset g
  obtain ⟨x, hx, c, hc, rfl⟩ := Set.mem_mul.mp hq
  obtain ⟨b, hb, n, ⟨nN, _, rfl⟩, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨t, ht, l, he⟩ := QuotientGeometry.exists_torus_mul_simpleWord m
    (fun _ hn => Overlap.normalizerWords_weylMonomial (splitTorus_eq_diagonalTorus m) hn)
    (fun _ hn => Overlap.normalizerWord_mem_diagonalTorus_of_heightTriangular
      (splitTorus_eq_diagonalTorus m) hn) nN.property
  have hf := QuotientGeometry.simpleWord_fixed_of_torus_mul m ht he
  obtain ⟨w, hw, hwval⟩ := QuotientGeometry.fixed_simpleWord_mem_map m l hf
  have ht' : (nN : Model m) * w⁻¹ ∈ fixedTorus m := by
    change toSplitGroup m ((nN : Model m) * w⁻¹) ∈ splitTorus m
    rw [map_mul, map_inv, hwval, he, mul_inv_cancel_right]
    exact ht
  refine ⟨b * ((nN : Model m) * w⁻¹), w, c,
    (borel m).mul_mem hb (fixedTorus_le_borel m ht'), hw, hc, ?_⟩
  group

private theorem map_conj_mul {m : ℕ} (H : Subgroup (Model m)) (x y : Model m) :
    H.map (MulAut.conj (x * y)).toMonoidHom =
      (H.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [map_map]
  congr 1
  ext z
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

/-- Every full root-family member in the full linear parabolic lies in its
specified radical. Bruhat reduction and the root-pair computation discharge
all geometric premises; ambient simplicity is unnecessary. -/
theorem rootFamily_le_linear_radical {m : ℕ} (hm : 0 < m)
    {A : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hAP : A ≤ parabolic m .linear) : A ≤ radical m .linear := by
  obtain ⟨g, rfl⟩ := hA
  obtain ⟨b, w, c, hb, hw, hc, rfl⟩ := exists_borel_weyl_borel m g
  have hcZ := mem_normalizer_iff_map_conj_eq.mp
    (borel_le_longRootGroup_normalizer m hm hc)
  rw [← MulEquiv.toMonoidHom_eq_coe] at hcZ
  change (longRootGroup m).map (MulAut.conj (b * w * c)).toMonoidHom ≤
    parabolic m .linear at hAP
  change (longRootGroup m).map (MulAut.conj (b * w * c)).toMonoidHom ≤ radical m .linear
  rw [map_conj_mul, hcZ, map_conj_mul] at hAP ⊢
  have hbP := borel_le_parabolic m .linear hb
  have hwP : (longRootGroup m).map (MulAut.conj w).toMonoidHom ≤
      parabolic m .linear := by
    intro x hx
    have hh := hAP (mem_map_of_mem (MulAut.conj b).toMonoidHom hx)
    have hh' := (parabolic m .linear).mul_mem
      ((parabolic m .linear).mul_mem ((parabolic m .linear).inv_mem hbP) hh) hbP
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hh'
  have hbR := SectionGeometry.LinearRadical.parabolic_le_radical_normalizer m .linear hbP
  have hbReq := mem_normalizer_iff_map_conj_eq.mp hbR
  rw [← MulEquiv.toMonoidHom_eq_coe] at hbReq
  rw [← hbReq]
  exact map_mono (LinearRootOrbit.weyl_conjugate_le_linear_radical m w hw hwP)

/-- Relative normality in the full parabolic puts its radical intersection
with K inside the intrinsic two-core of K. -/
theorem root_image_eq_bot_of_le_linear_radical {m : ℕ}
    {A K : Subgroup (Model m)} (hKP : K ≤ parabolic m .linear)
    (hAR : A ≤ radical m .linear) :
    (A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) = ⊥ := by
  let R := (radical m .linear).subgroupOf K
  let : R.Normal := normal_subgroupOf_of_le_normalizer
    (hKP.trans (SectionGeometry.LinearRadical.parabolic_le_radical_normalizer m .linear))
  have hp : IsPGroup 2 R := (radical_isPGroup m .linear).comap_of_injective
    K.subtype K.subtype_injective
  have hR : R ≤ pCore 2 K := le_sSup ⟨inferInstance, hp⟩
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [QuotientGroup.ker_mk']
  exact (subgroupOf_mono K hAR).trans hR

/-- The literal image in the intrinsic two-core quotient is trivial, so
its generator rank is zero. -/
theorem linear_root_rank_eq_zero {m : ℕ} (hm : 0 < m)
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hAK : A ≤ K) (hKP : K ≤ parabolic m .linear) :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) = 0 := by
  rw [root_image_eq_bot_of_le_linear_radical hKP
    (rootFamily_le_linear_radical hm hA (hAK.trans hKP)), Group.rank_eq_zero]

/-- The linear-parabolic input to the E1 confinement consumer, on its exact
subgroup and quotient maps. This includes the smallest positive case q = 8. -/
theorem linear_root_rank_ne_one {m : ℕ} (hm : 0 < m)
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hAK : A ≤ K) (hKP : K ≤ parabolic m .linear) :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ≠ 1 := by
  rw [linear_root_rank_eq_zero hm hA hAK hKP]
  exact Nat.zero_ne_one

end CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.LowerObstruction
