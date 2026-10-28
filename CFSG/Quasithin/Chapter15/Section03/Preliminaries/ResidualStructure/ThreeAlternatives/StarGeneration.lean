module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.ThreeAlternatives.StarGeometry
public import Theory.GroupTheory.InvolutiveCubicLift
public import Theory.GroupTheory.PResidual.NormalClosureCover

/-!
# Order-three generation of the actual star residual

For Y = O²(⟨Rcᴹ⟩), this proves Ω₁(Y*) = Y*, where stars are images in
M/O₂(M). The equality Rc ∩ ker(actor) = O₂(M) makes the specified inverter
an actual involution in this quotient. The cubic-lift construction then
shows that Ω₁(Y*) has the full E₉ action image.

Write W for the image of Ω₁(Y*) inside M*. The residual/Sylow supplement
in the action image gives M* = W C* T*. Since C* centralizes Rc* and T*
normalizes Rc*, the normal closure of Rc* lies in W Rc*. The latter has
a two-group quotient modulo W, so its two-residual lies in W. Functoriality
identifies the residual of the normal closure with the literal Y*, giving
the required generation. In particular no three-group conclusion or
two-group action kernel is assumed.

The three-group deduction, A.1.24, and both complete source alternatives
are assembled by the parent module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemmas
14.1.17 and 15.3.7, printed pp.980 and 1122 (PDF pp.997 and 1139).
-/

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives
variable {G : Type*} [Group G] [Finite G]

private theorem star_residual_normal (M Mc : Subgroup G) :
    (star M (residualY M Mc)).Normal := by
  let : ((residualY M Mc).subgroupOf M).Normal := residualY_normal M Mc
  exact Subgroup.Normal.map inferInstance (QuotientGroup.mk' (pCore 2 M))
    (QuotientGroup.mk'_surjective _)

/-- The exact intersection kernel turns the source inverter into a star involution. -/
public theorem star_inverter {M Mc V : Subgroup G} {T : Sylow 2 G}
    {d : NaturalOrthogonalAction M V} (h : SourceInputs M Mc V T d) :
    ∃ w ∈ star M (Rc M Mc), orderOf w = 2 ∧
      ∀ y ∈ star M (residualY M Mc),
        starActor d h.core_le_kernel (w * y * w⁻¹) =
          (starActor d h.core_le_kernel y)⁻¹ := by
  let q := QuotientGroup.mk' (pCore 2 M)
  obtain ⟨r, hr, hrne, hr2, hri⟩ := h.inverter
  refine ⟨q r, mem_map_of_mem q hr, orderOf_eq_prime ?_ ?_, ?_⟩
  · rw [← map_pow]
    apply (QuotientGroup.eq_one_iff (r ^ 2)).mpr
    rw [← h.core_inter_kernel]
    refine ⟨((Rc M Mc).subgroupOf M).pow_mem hr _, ?_⟩
    change d.actor (r ^ 2) = 1
    rwa [map_pow]
  · intro hr1
    exact hrne (h.core_le_kernel ((QuotientGroup.eq_one_iff r).mp hr1))
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hy
    change starActor d h.core_le_kernel (q r * q u * (q r)⁻¹) =
      (starActor d h.core_le_kernel (q u))⁻¹
    rw [← map_inv q, ← map_mul q, ← map_mul q]
    exact hri u hu

/-- Cubic elements of the actual star residual cover its full action image. -/
public theorem star_omega_image {M Mc V : Subgroup G} {T : Sylow 2 G}
    {d : NaturalOrthogonalAction M V} (h : SourceInputs M Mc V T d) :
    ((omega₁ (star M (residualY M Mc)) (p := 3)).map
      (star M (residualY M Mc)).subtype).map (starActor d h.core_le_kernel) =
        (star M (residualY M Mc)).map (starActor d h.core_le_kernel) := by
  let P := star M (residualY M Mc)
  let f := starActor d h.core_le_kernel
  let : P.Normal := star_residual_normal M Mc
  obtain ⟨w, hwR, hwo, hwi⟩ := star_inverter h
  have hw2 : w ^ 2 = 1 := by simpa only [hwo] using pow_orderOf_eq_one w
  have hc : ∀ k ∈ f.ker, w * k = k * w := by
    intro k hk
    rw [ker_starActor] at hk
    exact mem_centralizer_iff.mp (h.star_centralizes hk) w
      ((show star M (Rc M Mc) ≤ P ⊔ star M (Rc M Mc) from le_sup_right) hwR)
  obtain ⟨e⟩ := h.image_model
  let e' : P.map f ≃* ElementaryNine :=
    (MulEquiv.subgroupCongr (map_starActor d h.core_le_kernel _)).trans e
  have hexp : ∀ y ∈ P, (f y) ^ 3 = 1 := by
    intro y hy
    let a : P.map f := ⟨f y, mem_map_of_mem f hy⟩
    have he : ∀ a : ElementaryNine, a ^ 3 = 1 := by decide +kernel
    have ha : a ^ 3 = 1 := e'.injective (by rw [map_pow, he, map_one])
    exact congrArg Subtype.val ha
  apply le_antisymm (map_mono (map_subtype_le _))
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hz3, hfz⟩ := exists_cubic_lift_of_involutive_inverter f P w hw2 hc hwi hexp y hy
  have hzO : (⟨z, hz⟩ : P) ∈ omega₁ P (p := 3) :=
    subset_closure (by
      simpa only [Set.mem_ofPred_eq, pow_one] using (Subtype.ext hz3 : (⟨z, hz⟩ : P) ^ 3 = 1))
  exact mem_map.mpr ⟨z, mem_map_of_mem P.subtype hzO, hfz⟩

private theorem twoResidualAmbient_eq_pResidual (H : Subgroup G) :
    twoResidualAmbient H = (pResidual 2 H).map H.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 2
  ext N
  constructor
  · rintro ⟨hN, n, hn⟩
    refine ⟨hN, ?_⟩
    let := hN
    exact IsPGroup.iff_card.mpr ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩
  · rintro ⟨hN, hp⟩
    let := hN
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    exact ⟨hN, n, by simpa [Subgroup.index_eq_card] using hn⟩

private theorem star_residual_eq (M Mc : Subgroup G) :
    star M (residualY M Mc) =
      (pResidual 2 (normalClosure (star M (Rc M Mc) : Set (StarGroup M)))).map
        (normalClosure (star M (Rc M Mc) : Set (StarGroup M))).subtype := by
  rw [← twoResidualAmbient_eq_pResidual]
  unfold star residualY Chapter14.SourcePreliminaries.sourceResidual
  rw [← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective]
  rw [map_twoResidualAmbient_of_subgroup_image _ (QuotientGroup.mk' (pCore 2 M)) _ rfl,
    map_normalClosure _ _ (QuotientGroup.mk'_surjective _)]
  rfl

/-- The actual star residual is generated by elements whose cubes are one. -/
public theorem star_omega_eq_top {M Mc V : Subgroup G} {T : Sylow 2 G}
    {d : NaturalOrthogonalAction M V} (h : SourceInputs M Mc V T d) :
    omega₁ (star M (residualY M Mc)) (p := 3) = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 M)
  let P := star M (residualY M Mc)
  let R := star M (Rc M Mc)
  let W := (omega₁ P (p := 3)).map P.subtype
  let f := starActor d h.core_le_kernel
  let S := (T.subtype h.sylow_le : Subgroup M).map q
  let : P.Normal := star_residual_normal M Mc
  let : (omega₁ P (p := 3)).Characteristic := omega₁_characteristic P
  let : W.Normal := ConjAct.normal_of_characteristic_of_normal
  have hcover : W ⊔ f.ker ⊔ S = ⊤ := by
    have hm : (W ⊔ S).map f = ⊤ := by
      rw [Subgroup.map_sup, star_omega_image h, map_starActor, h.residual_image]
      change twoResidualAmbient (⊤ : Subgroup OrthogonalActor) ⊔
        ((T.subtype h.sylow_le : Subgroup M).map q).map f = ⊤
      rw [map_map, show f.comp q = d.actor from QuotientGroup.lift_comp_mk' _ _ _]
      exact twoResidualAmbient_top_sup_sylow ((T.subtype h.sylow_le).mapSurjective d.onto)
    have hm' := congrArg (Subgroup.comap f) hm
    simpa only [comap_map_eq, comap_top, sup_assoc, sup_left_comm, sup_comm] using hm'
  have hc : f.ker ≤ centralizer (R : Set (StarGroup M)) := by
    rw [ker_starActor]
    exact h.star_centralizes.trans (centralizer_le
      (show R ≤ P ⊔ R from le_sup_right))
  have ht : S ≤ normalizer (R : Set (StarGroup M)) := by
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    have hRcM : Rc M Mc ≤ M := (pCoreIn_le 2 (M ⊓ Mc)).trans inf_le_left
    rw [← subgroupOf_normalizer_eq hRcM]
    change (T : Subgroup G).subgroupOf M ≤ (normalizer (Rc M Mc : Set G)).subgroupOf M
    apply comap_mono
    exact (le_inf h.sylow_le h.sylow_le_partner).trans
      ((M ⊓ Mc).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (M ⊓ Mc) (pCore 2 (M ⊓ Mc : Subgroup G))))
  have hR : IsPGroup 2 R := ((isPGroup_pCoreIn 2 (M ⊓ Mc)).comap_subtype).map q
  have hPW : P ≤ W := by
    rw [show P = _ from star_residual_eq M Mc]
    exact embedded_pResidual_le_of_normal_sup_pGroup W R _ hR
      (normalClosure_le_sup_of_normalizing_cover W R f.ker S hc ht hcover)
  apply (map_injective P.subtype_injective)
  rw [← MonoidHom.range_eq_map, range_subtype]
  exact le_antisymm (map_subtype_le _) hPW

end CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives
