module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Residual.Frattini
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# C-components from the residual Frattini factorization

A solvable normal supplement preserves the property that the solvable residual
is a C-component. Applying this to C_LT(X/O₂(X)) and N_LT(R) gives the actual
C-component Y, and also gives the C-components N_L(C)^∞ for C characteristic
inside R. The latter normalizers have nontrivial two-core because they contain
the nontrivial normal two-subgroup C. Thus their residuals belong to L(G,T).

Finally, if a C-component contains a nontrivial perfect subgroup Y, its
commutator with Y is the whole component: that commutator is normal and contains
Y, so it cannot be a proper, hence solvable, subnormal subgroup.

The solvability of C_LT(X/O₂(X)) is an explicit unresolved structural input.
These deductions do not assert it or complete the source residual construction.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.8, printed pp.512–513, using A.3.3(1)–(4), pp.42–43.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.RadicalNormalizers
open CFSG.Quasithin.ChapterA.Section04

namespace CFSG.Quasithin.Chapter1.RadicalNormalizers

private theorem residual_cComponent_of_surjective
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (hB : (solvableResidual B).IsCComponent) : (solvableResidual A).IsCComponent := by
  have hne : solvableResidual A ≠ ⊥ := by
    intro he
    have hh := map_solvableResidual_eq f hf
    rw [he, Subgroup.map_bot] at hh
    exact hB.ne_bot hh.symm
  obtain ⟨K, hKR, hK⟩ := exists_isCComponent_le hne inferInstance
    (inferInstance : (solvableResidual A).Normal).isSubnormal
  have hm : K.map f = (solvableResidual A).map f := by
    rw [map_solvableResidual_eq f hf]
    exact (cComponent_map_of_solvable_ker hK f hf).eq_of_le hB
      ((map_mono hKR).trans_eq (map_solvableResidual_eq f hf))
  have hcover : solvableResidual A ≤ K ⊔ f.ker := by
    have h := congrArg (comap f) hm
    rw [comap_map_eq, comap_map_eq] at h
    exact le_sup_left.trans h.ge
  have hle := le_map_solvableResidual_of_isPerfect (solvableResidual A) (K ⊔ f.ker) hcover
  rw [hK.solvableResidual_sup_eq f.ker le_normalizer_of_normal] at hle
  exact (le_antisymm hKR hle) ▸ hK

private theorem cComponent_commutator
    {G : Type*} [Group G] [Finite G] {L Y : Subgroup G}
    (hL : L.IsCComponent) (hYL : Y ≤ L) (hY : Y ≠ ⊥) [Group.IsPerfect Y] :
    ⁅L,Y⁆ = L := by
  have hD : ⁅L,Y⁆ ≤ L := (commutator_mono le_rfl hYL).trans L.commutator_le_self
  have hYD : Y ≤ ⁅L,Y⁆ := Y.commutator_eq_self.symm.le.trans (commutator_mono hYL le_rfl)
  let D := ⁅L,Y⁆.subgroupOf L
  have hn : D.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left L Y)
  have ht : D = ⊤ := by
    by_contra he
    let : Group.IsSolvable D := hL.isSolvable_of_subnormal_lt_top hn.isSubnormal he
    have hsol : Group.IsSolvable Y := Group.isSolvable_of_isSolvable_injective
      (f := ((subgroupOfEquivOfLe hD).symm.toMonoidHom).comp (inclusion hYD))
      ((subgroupOfEquivOfLe hD).symm.injective.comp (inclusion_injective hYD))
    let : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hY
    exact Group.IsPerfect.not_isSolvable Y hsol
  have hm := congrArg (map L.subtype) ht
  simpa only [D, map_subgroupOf_eq_of_le hD, ← MonoidHom.range_eq_map, range_subtype] using hm

private theorem join_residual_cComponent
    {G : Type*} [Group G] [Finite G] (L T : Subgroup G)
    (hL : L ∈ CFSG.Quasithin.Chapter1.L G T)
    (hT : T ≤ normalizer (L : Set G)) :
    (solvableResidual (L ⊔ T : Subgroup G)).IsCComponent := by
  let := mem_L_isPerfect hL
  have hb : normalizer ((⊥ : Subgroup G) : Set G) = ⊤ := (⊥ : Subgroup G).normalizer_eq_top
  have hm : (solvableResidual (L ⊔ T : Subgroup G)).map (L ⊔ T).subtype = L := by
    have hh := localNormalizer_residual_eq L T (⊥ : Subgroup G) hL.2.1 hT
    unfold normalizerResidual at hh
    rw [hb, inf_top_eq, inf_top_eq] at hh
    rw [solvableResidual_eq_top (G := L), ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  have he : solvableResidual (L ⊔ T : Subgroup G) = L.subgroupOf (L ⊔ T) := by
    apply map_injective (L ⊔ T).subtype_injective
    rw [hm, map_subgroupOf_eq_of_le le_sup_left]
  exact he ▸ hL.1

private theorem residual_cComponent_of_supplement
    {G : Type*} [Group G] [Finite G] (H C N : Subgroup G)
    (hCH : C ≤ H) (hNH : N ≤ H) (hn : H ≤ normalizer (C : Set G))
    [Group.IsSolvable C] (hCN : C ⊔ N = H)
    (hH : (solvableResidual H).IsCComponent) :
    (solvableResidual N).IsCComponent := by
  let C' := C.subgroupOf H
  let : C'.Normal := normal_subgroupOf_of_le_normalizer hn
  let : Group.IsSolvable C' := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hCH).toMonoidHom) (subgroupOfEquivOfLe hCH).injective
  let q := QuotientGroup.mk' C'
  let f := q.comp (inclusion hNH)
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective C' z
    have hh : (h : G) ∈ C ⊔ N := hCN.symm ▸ h.property
    change (h : G) ∈ ((C ⊔ N : Subgroup G) : Set G) at hh
    rw [coe_mul_of_right_le_normalizer_left C N (hNH.trans hn)] at hh
    obtain ⟨c, hc, n, hn, he⟩ := hh
    refine ⟨⟨n, hn⟩, ?_⟩
    have heH : (⟨c, hCH hc⟩ : H) * ⟨n, hNH hn⟩ = h := Subtype.ext he
    change q ⟨n, hNH hn⟩ = q h
    rw [← heH, map_mul]
    have hcq : q ⟨c, hCH hc⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hc
    rw [hcq, one_mul]
  let k : f.ker →* C := (N.subtype.comp f.ker.subtype).codRestrict C (by
    intro x
    exact (QuotientGroup.eq_one_iff ((inclusion hNH) x.val)).mp x.property)
  have hk : Function.Injective k := by
    intro a b hab
    have hv : ((a.val : N) : G) = ((b.val : N) : G) := congrArg (fun z : C => (z : G)) hab
    exact Subtype.ext (Subtype.ext hv)
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hk
  have hq := hH.map_quotient C'
  rw [map_solvableResidual_eq q (QuotientGroup.mk'_surjective C')] at hq
  exact residual_cComponent_of_surjective f hf hq

variable {G : Type*} [Group G] [Finite G]

/-- Every intermediate normalizer residual is a C-component once the section
centralizer in the Frattini factorization is known to be solvable. -/
theorem normalizerResidual_cComponent_of_solvable_sectionCentralizer
    (p : ℕ) (L T D : Subgroup G)
    (hL : L ∈ CFSG.Quasithin.Chapter1.L G T)
    (hT : T ≤ normalizer (L : Set G))
    (hD : normalizer (radicalCore p L T : Set G) ≤ normalizer (D : Set G))
    (hsol : Group.IsSolvable (twoSectionCentralizer (XiP p L) (L ⊔ T))) :
    ((normalizerResidual L D).subgroupOf ((L ⊔ T) ⊓ normalizer (D : Set G))).IsCComponent := by
  let H := L ⊔ T
  let C := twoSectionCentralizer (XiP p L) H
  let N := H ⊓ normalizer (D : Set G)
  let := hsol
  have hCN : C ⊔ N = H := le_antisymm (sup_le (twoSectionCentralizer_le _ _) inf_le_left)
    ((radical_frattini p L T hL.2.1 hT).ge.trans (sup_le_sup_left (inf_le_inf_left H hD) C))
  have hres := residual_cComponent_of_supplement H C N (twoSectionCentralizer_le _ _)
    inf_le_left (twoSectionCentralizer_normalized _ _
      ((sup_le L.le_normalizer hT).trans (normalizer_le_normalizer_XiP p L)))
    hCN (join_residual_cComponent L T hL hT)
  have he : (normalizerResidual L D).subgroupOf N = solvableResidual N := by
    rw [← localNormalizer_residual_eq L T D hL.2.1 hT]
    exact comap_map_eq_self_of_injective N.subtype_injective _
  exact he ▸ hres

/-- The actual C-component property of Y in N_LT(R), conditional only on
solvability of the section centralizer. -/
theorem Y_cComponent_of_solvable_sectionCentralizer
    (p : ℕ) (L T : Subgroup G)
    (hL : L ∈ CFSG.Quasithin.Chapter1.L G T)
    (hT : T ≤ normalizer (L : Set G))
    (hsol : Group.IsSolvable (twoSectionCentralizer (XiP p L) (L ⊔ T))) :
    ((normalizerResidual L (radicalCore p L T)).subgroupOf
      ((L ⊔ T) ⊓ normalizer (radicalCore p L T : Set G))).IsCComponent :=
  normalizerResidual_cComponent_of_solvable_sectionCentralizer p L T _ hL hT le_rfl hsol

/-- The residual Y is nontrivial under the same solvability input. -/
theorem Y_ne_bot_of_solvable_sectionCentralizer
    (p : ℕ) (L T : Subgroup G)
    (hL : L ∈ CFSG.Quasithin.Chapter1.L G T)
    (hT : T ≤ normalizer (L : Set G))
    (hsol : Group.IsSolvable (twoSectionCentralizer (XiP p L) (L ⊔ T))) :
    normalizerResidual L (radicalCore p L T) ≠ ⊥ := by
  intro he
  have hne := (Y_cComponent_of_solvable_sectionCentralizer p L T hL hT hsol).ne_bot
  exact hne (by rw [he, bot_subgroupOf])


omit [Finite G] in
/-- A nontrivial subgroup C of R supplies the nontrivial two-core of N_LT(C). -/
theorem characteristicLocalNormalizer_mem_H (p : ℕ) (L T : Subgroup G)
    (C : Subgroup (radicalCore p L T)) (hC : C ≠ ⊥) :
    (L ⊔ T) ⊓ normalizer (C.map (radicalCore p L T).subtype : Set G) ∈ H G := by
  let R := radicalCore p L T
  let D := C.map R.subtype
  have hDH : D ≤ L ⊔ T := (map_subtype_le C).trans
    ((radicalCore_le_join p L T).trans (sup_le_sup_right (XiP_le p L) T))
  have hcore : D ≤ ((L ⊔ T) ⊓ normalizer (D : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (((radicalCore_isTwoGroup p L T).to_subgroup C).map _)
      (le_inf hDH D.le_normalizer) inf_le_right
  intro he
  have hD : D = ⊥ := bot_unique (he ▸ hcore)
  exact hC ((C.map_eq_bot_iff_of_injective R.subtype_injective).mp hD)

/-- The characteristic-subgroup residual L_C belongs to the genuine local family. -/
theorem characteristicResidual_mem_L_of_solvable_sectionCentralizer
    (p : ℕ) (L T : Subgroup G)
    (hL : L ∈ CFSG.Quasithin.Chapter1.L G T)
    (hT : T ≤ normalizer (L : Set G))
    (hsol : Group.IsSolvable (twoSectionCentralizer (XiP p L) (L ⊔ T)))
    (C : Subgroup (radicalCore p L T)) [C.Characteristic] (hC : C ≠ ⊥) :
    normalizerResidual L (C.map (radicalCore p L T).subtype) ∈ CFSG.Quasithin.Chapter1.L G T := by
  have hD := normalizer_le_normalizer_characteristic_image (radicalCore p L T) C
  apply mem_L_of_cComponent (characteristicLocalNormalizer_mem_H p L T C hC)
    (hL.2.1.restrict (le_inf le_sup_right ((t_le_normalizer_radicalCore p L T).trans hD))
      inf_le_left)
    (le_inf ((normalizerResidual_le L _).trans le_sup_left) (normalizerResidual_le_normalizer _ _))
  exact normalizerResidual_cComponent_of_solvable_sectionCentralizer p L T _ hL hT hD hsol

/-- Local-family membership and a nontrivial Y suffice for [L_C,Y] = L_C. -/
theorem characteristicResidual_commutator_of_mem_L
    (L R T : Subgroup G) (C : Subgroup R) [C.Characteristic]
    (hLC : normalizerResidual L (C.map R.subtype) ∈ CFSG.Quasithin.Chapter1.L G T)
    (hY : normalizerResidual L R ≠ ⊥) :
    ⁅normalizerResidual L (C.map R.subtype), normalizerResidual L R⁆ =
      normalizerResidual L (C.map R.subtype) := by
  let K := normalizerResidual L (C.map R.subtype)
  let Y := normalizerResidual L R
  let W := K ⊔ T
  have hYK : Y ≤ K := normalizerResidual_le_of_characteristic L R C
  have hYW : Y ≤ W := hYK.trans le_sup_left
  have hKW : K ≤ W := le_sup_left
  let : Group.IsPerfect Y := normalizerResidual_perfect L R
  let : Group.IsPerfect (Y.subgroupOf W) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hYW).symm.toMonoidHom)
    (subgroupOfEquivOfLe hYW).symm.surjective
  have hY' : Y.subgroupOf W ≠ ⊥ := by
    intro he
    have hm := congrArg (map W.subtype) he
    rw [map_subgroupOf_eq_of_le hYW, Subgroup.map_bot] at hm
    exact hY hm
  have hK : (K.subgroupOf W).IsCComponent := hLC.1
  have hc := cComponent_commutator (Y := Y.subgroupOf W) hK (comap_mono hYK) hY'
  have hm := congrArg (map W.subtype) hc
  simpa only [map_commutator, map_subgroupOf_eq_of_le hYW,
    map_subgroupOf_eq_of_le hKW] using hm

/-- The p.513 commutator equality follows from the solvable section centralizer. -/
theorem characteristicResidual_commutator_of_solvable_sectionCentralizer
    (p : ℕ) (L T : Subgroup G)
    (hL : L ∈ CFSG.Quasithin.Chapter1.L G T)
    (hT : T ≤ normalizer (L : Set G))
    (hsol : Group.IsSolvable (twoSectionCentralizer (XiP p L) (L ⊔ T)))
    (C : Subgroup (radicalCore p L T)) [C.Characteristic] (hC : C ≠ ⊥) :
    ⁅normalizerResidual L (C.map (radicalCore p L T).subtype),
      normalizerResidual L (radicalCore p L T)⁆ =
      normalizerResidual L (C.map (radicalCore p L T).subtype) :=
  characteristicResidual_commutator_of_mem_L L _ T C
    (characteristicResidual_mem_L_of_solvable_sectionCentralizer p L T hL hT hsol C hC)
    (Y_ne_bot_of_solvable_sectionCentralizer p L T hL hT hsol)

end CFSG.Quasithin.Chapter1.RadicalNormalizers
