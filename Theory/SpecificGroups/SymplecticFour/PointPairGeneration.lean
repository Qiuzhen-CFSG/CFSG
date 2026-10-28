module
public import Theory.SpecificGroups.SymplecticFour.MoverNormalizer
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement.OvergroupGeometry
public import Theory.GroupTheory.MarkedConjugateGeneration
public import Theory.SpecificGroups.SL2.SylowConsequences

/-!
# One shear for the marked exceptional paired generation

The endpoint and the actual normalized plane intersection generate the
full point-local rank-one quotient. Otherwise the latter intersection
would equal the endpoint, and normalization would make the upper root
normal in SL₂. A fixed shear in the original plane radical then gives a
noncentral radical commutator; the point-radical lattice forces the whole
point local into the generated group.

The index-two unequal mover moves that point. The orthogonal point-orbit
criterion shows that any proper overgroup of the full point local still
fixes the point, proving generation of Sp₄ by the same mover pair.
No arbitrary square-order subgroup is identified with a full root pair.

Source: MS93 (5.5)(c), printed pp.915--917. The literal quotient and
full-kernel consumer is CriticalReduction.ContainedPairGeneration.
-/

public noncomputable section
open Subgroup Matrix
open scoped Pointwise
namespace Theory.SpecificGroups.SymplecticFour.PointPairGeneration
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The actual normalized plane intersection and endpoint generate the rank-one image. -/
theorem normalized_pair_rankOne (A E T : Subgroup (Sp F))
    (hAL : A ≤ pointLocal) (hTL : T ≤ pointLocal)
    (hTJ : T ≤ A ⊔ E) (hET : E ≤ normalizer (T : Set (Sp F)))
    (hTtwo : IsPGroup 2 T) (hsize : Nat.card T = Nat.card A)
    (hA : (A.subgroupOf pointLocal).map pointQuotient = SpecialLinearGroup.upperUnipotent F)
    (hJ : ((A ⊔ E).subgroupOf pointLocal).map pointQuotient = ⊤)
    (hupper : (A ⊔ E).subgroupOf pointLocal ⊓
      (SpecialLinearGroup.upperUnipotent F).comap pointQuotient = A.subgroupOf pointLocal) :
    ((A ⊔ T).subgroupOf pointLocal).map pointQuotient = ⊤ := by
  let A₀ := A.subgroupOf pointLocal
  let T₀ := T.subgroupOf pointLocal
  let I := ((A ⊔ T).subgroupOf pointLocal).map pointQuotient
  have hAI : SpecialLinearGroup.upperUnipotent F ≤ I := by
    rw [←hA]
    exact map_mono (comap_mono le_sup_left)
  by_contra hI
  have hTB : T₀.map pointQuotient ≤ SpecialLinearGroup.rankOneBorel F :=
    (map_mono (comap_mono le_sup_right)).trans
      (SpecialLinearGroup.overgroup_le_rankOneBorel hAI hI)
  have hTU : T₀.map pointQuotient ≤ SpecialLinearGroup.upperUnipotent F := by
    calc
      T₀.map pointQuotient = T₀.map pointQuotient ⊓ SpecialLinearGroup.rankOneBorel F :=
        (inf_eq_left.mpr hTB).symm
      _ = T₀.map pointQuotient ⊓ (SpecialLinearGroup.upperUnipotentSylow F 2 : Subgroup _) :=
        (hTtwo.comap_subtype.map pointQuotient).inf_normalizer_sylow (SpecialLinearGroup.upperUnipotentSylow F 2)
      _ ≤ _ := inf_le_right
  have hTA : T ≤ A := by
    have h : T₀ ≤ A₀ := by
      change T₀ ≤ A.subgroupOf pointLocal
      rw [←hupper]
      exact le_inf (comap_mono hTJ) (map_le_iff_le_comap.mp hTU)
    have hm := map_mono h (f := pointLocal.subtype)
    rwa [map_subgroupOf_eq_of_le hAL,map_subgroupOf_eq_of_le hTL] at hm
  have hTeq : T=A := eq_of_le_of_card_ge hTA hsize.ge
  have hJA : A ⊔ E ≤ normalizer (A : Set (Sp F)) :=
    sup_le A.le_normalizer (hTeq ▸ hET)
  have hnormal : (A ⊔ E).subgroupOf pointLocal ≤ normalizer (A₀ : Set (pointLocal (F := F))) :=
    (comap_mono hJA).trans (A.le_normalizer_comap pointLocal.subtype)
  have hN := (map_mono hnormal (f := pointQuotient)).trans (le_normalizer_map pointQuotient)
  rw [hJ,hA] at hN
  exact SpecialLinearGroup.upperUnipotent_not_normal F (normalizer_eq_top_iff.mp (top_le_iff.mp hN))

/-- One fixed shear in the original plane radical supplies paired generation. -/
theorem shear_pair_generate {n : ℕ} (hcard : Nat.card F=2^n) (hn : 1<n)
    (A T : Subgroup (pointLocal (F := F)))
    (hA : A.map pointQuotient = SpecialLinearGroup.upperUnipotent F)
    (hgen : (A ⊔ T).map pointQuotient = ⊤) :
    (A ⊔ T) ⊔ T.map (MulAut.conj (pointRadicalElement (1:F) 0 0)).toMonoidHom = ⊤ := by
  let x := pointRadicalElement (1:F) 0 0
  let D := (A ⊔ T) ⊔ T.map (MulAut.conj x).toMonoidHom
  have hDgen : D.map pointQuotient = ⊤ := top_le_iff.mp
    (hgen ▸ map_mono (show A ⊔ T ≤ D from le_sup_left))
  have hsupp : D ⊔ pointRadical = ⊤ := by
    rw [←pointQuotient_ker,←comap_map_eq,hDgen,comap_top]
  rcases PointSupplement.supplement_dichotomy hcard hn D hsupp with he | hc
  · exact he
  exfalso
  have hout : ¬ T.map pointQuotient ≤ SpecialLinearGroup.rankOneBorel F := by
    intro ht
    have ha : A.map pointQuotient ≤ SpecialLinearGroup.rankOneBorel F := by
      rw [hA]
      exact (SpecialLinearGroup.upperUnipotent F).le_normalizer
    have hall := sup_le ha ht
    rw [←Subgroup.map_sup,hgen] at hall
    exact SpecialLinearGroup.upperUnipotent_not_normal F
      (normalizer_eq_top_iff.mp (top_le_iff.mp hall))
  obtain ⟨y,⟨t,ht,rfl⟩,hy⟩ := SetLike.not_le_iff_exists.mp hout
  have htc : (pointQuotient t).val 1 0 ≠ 0 := by
    simpa only [SpecialLinearGroup.mem_rankOneBorel_iff] using hy
  let q : pointRadical (F := F) := ⟨x,pointRadicalElement_mem 1 0 0⟩
  let r := pointRadicalConjugate t q * q⁻¹
  have hrD : r.val ∈ D := by
    change (t*x*t⁻¹)*x⁻¹ ∈ D
    have htD : t∈D := (show T ≤ D from le_sup_right.trans le_sup_left) ht
    have hxT : x*t⁻¹*x⁻¹ ∈ D :=
      (show T.map (MulAut.conj x).toMonoidHom ≤ D from le_sup_right)
        (mem_map_of_mem (MulAut.conj x).toMonoidHom (T.inv_mem ht))
    simpa only [mul_assoc] using D.mul_mem htD hxT
  have hrZ : r.val ∈ center (pointLocal (F := F)) := hc ⟨hrD,r.property⟩
  have hzero : pointRadicalVector r = 1 := by
    obtain ⟨z,hz⟩ := (pointRadical_mem_center_iff r).mp hrZ
    have he : r=⟨pointRadicalElement 0 0 z,pointRadicalElement_mem 0 0 z⟩ := Subtype.ext hz
    rw [he,pointRadicalVector_element]
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl
  have hv := congrArg (fun z : Multiplicative (Fin 2 → F) => z.toAdd 1) hzero
  dsimp only [r] at hv
  rw [map_mul,map_inv,pointRadicalVector_conjugate] at hv
  change ((pointQuotient t).val *ᵥ ![(1:F),0]) 1 + (-![(1:F),0]) 1 = 0 at hv
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_one,
    Matrix.cons_val_zero, mul_one, mul_zero, add_zero, Pi.neg_apply, neg_zero] at hv
  exact htc hv

omit [Finite F] in
/-- A proper overgroup of the whole point local still fixes the same point. -/
theorem overgroup_pointLocal (N : Subgroup (Sp F)) (hLN : pointLocal ≤ N) (hN : N ≠ ⊤) :
    N ≤ pointParabolic := by
  have ho := ThreeResidualPlacement.orthogonal_point_orbit_of_proper_unipotent_overgroup
    N (inf_le_left.trans hLN) hN
  intro g hg
  have hc : g.val (.inr 0) (.inl 0) = 0 := by
    simpa [form_apply,e,smul_eq_mulVec,Matrix.mulVec_single,Fin.sum_univ_two] using ho g hg
  have horbit (k : pointLocal (F := F)) :
      form F (g • e 0) (k.val • (g • e 0)) = 0 := by
    have hmem : g⁻¹*k.val*g∈N := N.mul_mem (N.mul_mem (N.inv_mem hg) (hLN k.property)) hg
    have he := preserves_form g (e 0) ((g⁻¹*k.val*g) • e 0)
    have heq : g • ((g⁻¹*k.val*g) • e (F := F) 0) = k.val • (g • e (F := F) 0) := by
      rw [←mul_smul,show g*(g⁻¹*k.val*g)=k.val*g by group,mul_smul]
    rw [heq] at he
    exact he.trans (ho _ hmem)
  have hb : g.val (.inl 1) (.inl 0) = 0 := by
    have hh := horbit (pointLevi (SpecialLinearGroup.transvection (i := 1) (j := 0) one_ne_zero (1:F)))
    simp [form_apply,smul_eq_mulVec,e,Matrix.mulVec_single,Fin.sum_univ_two,
      pointLevi,pointLeviMatrix,SpecialLinearGroup.transvection_coe,Matrix.mulVec,
      dotProduct,Fintype.sum_sum_type,hc,CharTwo.sub_eq_add] at hh
    have hs : g.val (.inl 1) (.inl 0)^2=0 := by linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hh
    exact (sq_eq_zero_iff).mp hs
  have hd : g.val (.inr 1) (.inl 0) = 0 := by
    have hh := horbit (pointLevi (SpecialLinearGroup.transvection (i := 0) (j := 1) zero_ne_one (1:F)))
    simp [form_apply,smul_eq_mulVec,e,Matrix.mulVec_single,Fin.sum_univ_two,
      pointLevi,pointLeviMatrix,SpecialLinearGroup.transvection_coe,Matrix.mulVec,
      dotProduct,Fintype.sum_sum_type,hc,CharTwo.sub_eq_add] at hh
    have hs : g.val (.inr 1) (.inl 0)^2=0 := by linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hh
    exact (sq_eq_zero_iff).mp hs
  exact (mem_pointParabolic_iff g).mpr ⟨hb,fun i => by fin_cases i <;> assumption⟩

omit [CharP F 2] in
private theorem pgroup_le_pointLocal {n : ℕ} (hcard : Nat.card F=2^n) (hn : 1<n)
    (T : Subgroup (Sp F)) (hTP : T ≤ pointParabolic) (hT : IsPGroup 2 T) :
    T ≤ pointLocal := by
  let S : Sylow 2 (pointParabolic (F := F)) := (unipotentSylow hcard (by omega)).subtype
    (unipotent_le_borel.trans inf_le_left)
  have hSN : (S : Subgroup (pointParabolic (F := F))) ≤ pointLocal.subgroupOf pointParabolic :=
    comap_mono (show unipotent ≤ pointLocal (F := F) from inf_le_left)
  have hle := hT.comap_subtype.le_normalClosure_sylow S
  have hle' : T.subgroupOf pointParabolic ≤ pointLocal.subgroupOf pointParabolic :=
    hle.trans (normalClosure_le_normal hSN)
  intro x hx
  exact hle' (show (⟨x,hTP hx⟩ : pointParabolic) ∈ T.subgroupOf pointParabolic from hx)

/-- An index-two normalizing mover in the central branch moves the point. -/
theorem mover_not_pointParabolic {n : ℕ} (hcard : Nat.card F=2^n) (hn : 1<n)
    (A E T : Subgroup (Sp F)) (_hAL : A ≤ pointLocal) (hTL : T ≤ pointLocal)
    (hTJ : T ≤ A ⊔ E) (hET : E ≤ normalizer (T : Set (Sp F)))
    (hE2 : IsPGroup 2 E) (hT2 : IsPGroup 2 T) (hsize : Nat.card T=Nat.card F^2)
    (hc : (A ⊔ E).subgroupOf pointLocal ⊓ pointRadical ≤ center (pointLocal (F := F)))
    (hi : T.relIndex E=2) : ¬ E ≤ pointParabolic := by
  intro hEP
  have hEL := pgroup_le_pointLocal hcard hn E hEP hE2
  have hsupL : E ⊔ T ≤ pointLocal := sup_le hEL hTL
  have hb := PointSupplement.central_kernel_pgroup_card_bound hcard hn
    ((A ⊔ E).subgroupOf pointLocal) ((E ⊔ T).subgroupOf pointLocal)
    hc (comap_mono (sup_le le_sup_right hTJ))
    (hE2.to_sup_of_normal_right' hT2 hET).comap_subtype
  rw [←card_map_of_injective pointLocal.subtype_injective,map_subgroupOf_eq_of_le hsupL,←hsize] at hb
  have he : T = E ⊔ T := eq_of_le_of_card_ge le_sup_right hb
  have hle : E ≤ T := he.symm ▸ le_sup_left
  have h1 : T.relIndex E=1 := relIndex_eq_one.mpr hle
  omega

/-- The selected shear belongs to the original plane radical. -/
theorem shear_mem_plane : (pointRadicalElement (1:F) 0 0).val ∈
    (CentralRootGeometry.wing true).map unipotent.subtype := by
  have he : (pointRadicalElement (1:F) 0 0).val = (CentralRootGeometry.element 0 0 1 0).val := by
    apply Subtype.ext
    rw [CentralRootGeometry.element_matrix]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [pointRadicalElement,pointRadicalMatrix,Matrix.fromBlocks]
  rw [he]
  exact mem_map_of_mem unipotent.subtype
    ((CentralRootGeometry.element_mem_wing true _ _ _ _).mpr rfl)

/-- The actual central-intersection branch has paired generation by the
individual mover with one shear in the original plane radical. -/
theorem marked_pair_generate {n : ℕ} (hcard : Nat.card F=2^n) (hn : 1<n)
    (A E T : Subgroup (Sp F))
    (hAP : A ≤ (CentralRootGeometry.wing true).map unipotent.subtype)
    (hTL : T ≤ pointLocal) (hTJ : T ≤ A ⊔ E)
    (hET : E ≤ normalizer (T : Set (Sp F)))
    (hE2 : IsPGroup 2 E) (hT2 : IsPGroup 2 T)
    (hsize : Nat.card T=Nat.card F^2) (hAsize : Nat.card A=Nat.card F^2)
    (hA : (A.subgroupOf pointLocal).map pointQuotient = SpecialLinearGroup.upperUnipotent F)
    (hJ : ((A ⊔ E).subgroupOf pointLocal).map pointQuotient = ⊤)
    (hupper : (A ⊔ E).subgroupOf pointLocal ⊓
      (SpecialLinearGroup.upperUnipotent F).comap pointQuotient = A.subgroupOf pointLocal)
    (hc : (A ⊔ E).subgroupOf pointLocal ⊓ pointRadical ≤ center (pointLocal (F := F)))
    (hi : T.relIndex E=2) :
    let x := (pointRadicalElement (1:F) 0 0).val
    (A ⊔ T) ⊔ T.map (MulAut.conj x).toMonoidHom = pointLocal ∧
      (A ⊔ E) ⊔ E.map (MulAut.conj x).toMonoidHom = ⊤ := by
  let x := pointRadicalElement (1:F) 0 0
  have hAL : A ≤ pointLocal := hAP.trans ((map_subtype_le _).trans inf_le_left)
  have hproj := normalized_pair_rankOne A E T hAL hTL hTJ hET hT2
    (hsize.trans hAsize.symm) hA hJ hupper
  rw [subgroupOf_sup hAL hTL] at hproj
  have hlocal := shear_pair_generate hcard hn (A.subgroupOf pointLocal) (T.subgroupOf pointLocal) hA hproj
  have hl := congrArg (Subgroup.map pointLocal.subtype) hlocal
  rw [Subgroup.map_sup,Subgroup.map_sup,Subgroup.image_conjugate,
    map_subgroupOf_eq_of_le hAL,map_subgroupOf_eq_of_le hTL,
    ←MonoidHom.range_eq_map,range_subtype] at hl
  refine ⟨hl,?_⟩
  let N := (A ⊔ E) ⊔ E.map (MulAut.conj x.val).toMonoidHom
  have hAc : A.map (MulAut.conj x.val).toMonoidHom=A := by
    let P := (CentralRootGeometry.wing (F := F) true).map unipotent.subtype
    let := CentralRootGeometry.wing_elementary (F := F) true
    let : IsElementaryAbelian 2 P := IsElementaryAbelian.map unipotent.subtype
    apply mem_normalizer_iff_map_conj_eq.mp
    exact centralizer_le_normalizer (A : Set (Sp F))
      ((centralizer_le hAP) (P.le_centralizer shear_mem_plane))
  have hLN : pointLocal ≤ N := by
    rw [←hl]
    refine sup_le (sup_le (le_sup_left.trans le_sup_left) (hTJ.trans le_sup_left)) ?_
    have hm := map_mono hTJ (f := (MulAut.conj x.val).toMonoidHom)
    rw [Subgroup.map_sup,hAc] at hm
    exact hm.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  by_contra hN
  exact mover_not_pointParabolic hcard hn A E T hAL hTL hTJ hET hE2 hT2 hsize hc hi
    ((le_sup_right.trans le_sup_left).trans (overgroup_pointLocal N hLN hN))

end Theory.SpecificGroups.SymplecticFour.PointPairGeneration
