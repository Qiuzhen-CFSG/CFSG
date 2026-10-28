module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.Seed
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Theory.SpecificGroups.PSL3Two.Automorphisms.SylowStabilizer
public import Theory.SpecificGroups.PSL3Two.Parabolics.PointNormalizer

/-!
# The original paired parabolic and its residual

The Hall-faithful source puts H∩M inside L₀T. Its two-residual and the
original T∩L₀ therefore generate exactly H∩L₀. In SL₃(2), every overgroup
of a Sylow two-subgroup is self-normalizing; hence an overgroup of the
product Sylow splits into its coordinate intersections. Mark the second
component by the original exchange element. The two intersections are
then equal, and the Hall torus excludes the two-group case. A single
quotient isomorphism marks both the orbit Sylow and the paired parabolic.
Functoriality retains the literal image of O²(H∩M) under that same map.

These are the parabolic-placement clauses of 10.2.3(3) used in 10.3.1.
Recognition of H/C_H(U) as S₅ wr C₂ remains a separate step in this task.
Hall faithfulness remains the authorized earlier-source input; its final
discharge belongs to qt-d-10-fixed-hstar-parameter. Neither fixed-space
vanishing, TI nor later CentralizerData is used.
Source: Aschbacher--Smith, 10.2.3(3) and 10.3.1, printed pp.744--745,755.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
open Chapter3.Section02 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan

private theorem linear_three_sylow_overgroup_normalizer
    (S : Sylow 2 Matrix.PSL3Two.SL) (P : Subgroup Matrix.PSL3Two.SL)
    (hSP : (S : Subgroup Matrix.PSL3Two.SL) ≤ P) :
    normalizer (P : Set Matrix.PSL3Two.SL) = P := by
  by_cases ht : P = ⊤
  · subst P
    exact normalizer_eq_top_iff.mpr inferInstance
  by_cases hp : IsPGroup 2 P
  · have he := S.is_maximal' hp hSP
    rw [he]
    exact Matrix.PSL3Two.self_normalizing_sylow S
  obtain ⟨e,_,he⟩ := Matrix.PSL3Two.exists_sylow_line_marking
    Matrix.PSL3Two.equiv S P hSP ht hp
  have hn : normalizer (Matrix.PSL3Two.lineParabolicSL : Set Matrix.PSL3Two.SL) =
      Matrix.PSL3Two.lineParabolicSL := by
    rw [← Matrix.PSL3Two.flagDuality_map_point, ← map_equiv_normalizer_eq,
      Matrix.PSL3Two.pointParabolicSL_normalizer]
  apply e.mapSubgroup.injective
  change (normalizer (P : Set Matrix.PSL3Two.SL)).map e.toMonoidHom = P.map e.toMonoidHom
  rw [map_equiv_normalizer_eq,he,hn]

private theorem product_isTwo {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (P : Subgroup A) (Q : Subgroup B) (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q) :
    IsPGroup 2 (P.prod Q) := by
  obtain ⟨m,hm⟩ := hP.exists_card_eq
  obtain ⟨n,hn⟩ := hQ.exists_card_eq
  exact IsPGroup.of_card (n := m+n) (by
    rw [Nat.card_congr (P.prodEquiv Q).toEquiv,Nat.card_prod,hm,hn,pow_add])

private theorem product_sylow_eq (S : Sylow 2 (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL)) :
    (S : Subgroup (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL)) =
      ((S.mapSurjective (f := MonoidHom.fst _ _) (fun x => ⟨(x,1),rfl⟩) :
        Sylow 2 Matrix.PSL3Two.SL) : Subgroup Matrix.PSL3Two.SL).prod
      ((S.mapSurjective (f := MonoidHom.snd _ _) (fun x => ⟨(1,x),rfl⟩) :
        Sylow 2 Matrix.PSL3Two.SL) : Subgroup Matrix.PSL3Two.SL) := by
  symm
  apply S.is_maximal'
  · exact product_isTwo _ _ (S.isPGroup'.map _) (S.isPGroup'.map _)
  · intro x hx
    exact ⟨mem_map_of_mem _ hx,mem_map_of_mem _ hx⟩

private theorem product_overgroup_splits
    (S : Sylow 2 (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL))
    (V : Subgroup (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL)) (hSV : (S : Subgroup _) ≤ V) :
    V = (V.comap (MonoidHom.inl _ _)).prod (V.comap (MonoidHom.inr _ _)) := by
  let P := V.comap (MonoidHom.inl _ _)
  let Q := V.comap (MonoidHom.inr _ _)
  let S₁ := S.mapSurjective (f := MonoidHom.fst _ _) (fun x => ⟨(x,1),rfl⟩)
  let S₂ := S.mapSurjective (f := MonoidHom.snd _ _) (fun x => ⟨(1,x),rfl⟩)
  have h₁ : (S₁ : Subgroup _) ≤ P := by
    intro x hx
    apply hSV
    rw [product_sylow_eq]
    exact ⟨hx,one_mem _⟩
  have h₂ : (S₂ : Subgroup _) ≤ Q := by
    intro x hx
    apply hSV
    rw [product_sylow_eq]
    exact ⟨one_mem _,hx⟩
  apply le_antisymm
  · intro x hx
    have hn₁ : x.1 ∈ normalizer (P : Set Matrix.PSL3Two.SL) := by
      apply mem_normalizer_iff.mpr
      intro y
      change (y,1) ∈ V ↔ (x.1*y*x.1⁻¹,1) ∈ V
      have he : (x.1*y*x.1⁻¹,1) = x*(y,1)*x⁻¹ := by ext <;> simp
      rw [he]
      exact V.le_normalizer hx (y,1)
    have hn₂ : x.2 ∈ normalizer (Q : Set Matrix.PSL3Two.SL) := by
      apply mem_normalizer_iff.mpr
      intro y
      change (1,y) ∈ V ↔ (1,x.2*y*x.2⁻¹) ∈ V
      have he : (1,x.2*y*x.2⁻¹) = x*(1,y)*x⁻¹ := by ext <;> simp
      rw [he]
      exact V.le_normalizer hx (1,y)
    rw [linear_three_sylow_overgroup_normalizer S₁ P h₁] at hn₁
    rw [linear_three_sylow_overgroup_normalizer S₂ Q h₂] at hn₂
    exact ⟨hn₁,hn₂⟩
  · rintro ⟨x,y⟩ ⟨hx,hy⟩
    simpa using V.mul_mem hx hy

private theorem six_overgroup_marking
    (S : Sylow 2 Matrix.PSL3Two.SL) (P : Subgroup Matrix.PSL3Two.SL)
    (hSP : (S : Subgroup Matrix.PSL3Two.SL) ≤ P) (hP : IsPGroup 6 P) :
    ∃ e : Matrix.PSL3Two.SL ≃* Matrix.PSL3Two.SL,
      (S : Subgroup Matrix.PSL3Two.SL).map e.toMonoidHom = Matrix.PSL3Two.borelSL ∧
      (P.map e.toMonoidHom = Matrix.PSL3Two.borelSL ∨
        P.map e.toMonoidHom = Matrix.PSL3Two.lineParabolicSL) := by
  by_cases hp : IsPGroup 2 P
  · obtain ⟨e,he⟩ := Matrix.PSL3Two.exists_sylow_marking Matrix.PSL3Two.equiv S
    exact ⟨e,he,Or.inl ((congrArg (map e.toMonoidHom) (S.is_maximal' hp hSP)).trans he)⟩
  have ht : P ≠ ⊤ := by
    intro he
    have h6 : IsPGroup 6 Matrix.PSL3Two.SL := (he ▸ hP).of_equiv topEquiv
    obtain ⟨n,hn⟩ := h6.exists_card_dvd_pow
    rw [Matrix.PSL3Two.card_SL] at hn
    have h7 : 7 ∣ 6 := Nat.Prime.dvd_of_dvd_pow (by decide) ((by decide : 7 ∣ 168).trans hn)
    norm_num at h7
  obtain ⟨e,hS,he⟩ := Matrix.PSL3Two.exists_sylow_line_marking
    Matrix.PSL3Two.equiv S P hSP ht hp
  exact ⟨e,hS,Or.inr he⟩

/-- The same equivalence marks the actual product Sylow and its six-group overgroup. -/
private theorem product_six_overgroup_marking
    (S : Sylow 2 (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL))
    (V : Subgroup (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL)) (hSV : (S : Subgroup _) ≤ V)
    (hV : IsPGroup 6 V) (hn : ¬ IsPGroup 2 V) :
    ∃ e : (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL) ≃*
        (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL),
      (S : Subgroup _).map e.toMonoidHom = Matrix.PSL3Two.borelSL.prod Matrix.PSL3Two.borelSL ∧
      (V.map e.toMonoidHom = Matrix.PSL3Two.lineParabolicSL.prod Matrix.PSL3Two.borelSL ∨
       V.map e.toMonoidHom = Matrix.PSL3Two.borelSL.prod Matrix.PSL3Two.lineParabolicSL ∨
       V.map e.toMonoidHom = Matrix.PSL3Two.lineParabolicSL.prod Matrix.PSL3Two.lineParabolicSL) := by
  let P := V.comap (MonoidHom.inl _ _)
  let Q := V.comap (MonoidHom.inr _ _)
  let S₁ := S.mapSurjective (f := MonoidHom.fst _ _) (fun x => ⟨(x,1),rfl⟩)
  let S₂ := S.mapSurjective (f := MonoidHom.snd _ _) (fun x => ⟨(1,x),rfl⟩)
  have h₁ : (S₁ : Subgroup _) ≤ P := by
    intro x hx
    apply hSV
    rw [product_sylow_eq]
    exact ⟨hx,one_mem _⟩
  have h₂ : (S₂ : Subgroup _) ≤ Q := by
    intro x hx
    apply hSV
    rw [product_sylow_eq]
    exact ⟨one_mem _,hx⟩
  obtain ⟨a,ha,hP⟩ := six_overgroup_marking S₁ P h₁
    (hV.comap_of_injective _ (by intro x y h; exact congrArg Prod.fst h))
  obtain ⟨b,hb,hQ⟩ := six_overgroup_marking S₂ Q h₂
    (hV.comap_of_injective _ (by intro x y h; exact congrArg Prod.snd h))
  let e := a.prodCongr b
  have hmap (P Q : Subgroup Matrix.PSL3Two.SL) :
      (P.prod Q).map e.toMonoidHom = (P.map a.toMonoidHom).prod (Q.map b.toMonoidHom) := by
    ext z
    constructor
    · rintro ⟨x,⟨hx,hy⟩,rfl⟩
      exact ⟨⟨x.1,hx,rfl⟩,⟨x.2,hy,rfl⟩⟩
    · rintro ⟨⟨x,hx,hxa⟩,⟨y,hy,hyb⟩⟩
      exact ⟨(x,y),⟨hx,hy⟩,Prod.ext hxa hyb⟩
  have hs : (S : Subgroup _).map e.toMonoidHom =
      Matrix.PSL3Two.borelSL.prod Matrix.PSL3Two.borelSL := by
    rw [product_sylow_eq,hmap]
    exact congrArg₂ Subgroup.prod ha hb
  have hv : V.map e.toMonoidHom = (P.map a.toMonoidHom).prod (Q.map b.toMonoidHom) := by
    rw [product_overgroup_splits S V hSV]
    exact hmap P Q
  refine ⟨e,hs,?_⟩
  rcases hP with hP | hP <;> rcases hQ with hQ | hQ
  · have he : V.map e.toMonoidHom = (S : Subgroup _).map e.toMonoidHom := by
      rw [hv,hP,hQ,hs]
    exact (hn ((map_injective e.injective he).symm ▸ S.isPGroup')).elim
  · exact Or.inr (Or.inl (by rw [hv,hP,hQ]))
  · exact Or.inl (by rw [hv,hP,hQ])
  · exact Or.inr (Or.inr (by rw [hv,hP,hQ]))

private theorem product_equal_overgroup_marking
    (S : Sylow 2 (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL))
    (V : Subgroup (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL)) (hSV : (S : Subgroup _) ≤ V)
    (hV : IsPGroup 6 V) (hn : ¬ IsPGroup 2 V)
    (hequal : V.comap (MonoidHom.inl _ _) = V.comap (MonoidHom.inr _ _)) :
    ∃ e : (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL) ≃*
        (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL),
      (S : Subgroup _).map e.toMonoidHom = Matrix.PSL3Two.borelSL.prod Matrix.PSL3Two.borelSL ∧
      V.map e.toMonoidHom = Matrix.PSL3Two.lineParabolicSL.prod Matrix.PSL3Two.lineParabolicSL := by
  obtain ⟨e,hs,hv⟩ := product_six_overgroup_marking S V hSV hV hn
  let P := V.comap (MonoidHom.inl _ _)
  have hsplit : V = P.prod P := (product_overgroup_splits S V hSV).trans
    (congrArg (Subgroup.prod P) hequal.symm)
  have hcard : Nat.card V = Nat.card P * Nat.card P := by
    rw [hsplit,Nat.card_congr (P.prodEquiv P).toEquiv,Nat.card_prod]
  have hne : Nat.card V ≠ 192 := by
    intro hc
    rw [hcard] at hc
    have hb : Nat.card P ≤ 13 ∨ 14 ≤ Nat.card P := by omega
    rcases hb with hb | hb
    · have hh := Nat.mul_le_mul hb hb
      norm_num [hc] at hh
    · have hh := Nat.mul_le_mul hb hb
      norm_num [hc] at hh
  refine ⟨e,hs,?_⟩
  rcases hv with hv | hv | hv
  · apply (hne ?_).elim
    have hc := Nat.card_congr (V.equivMapOfInjective e.toMonoidHom e.injective).toEquiv
    rw [hv,Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,
      Matrix.PSL3Two.card_lineParabolicSL,Matrix.PSL3Two.card_borelSL] at hc
    exact hc
  · apply (hne ?_).elim
    have hc := Nat.card_congr (V.equivMapOfInjective e.toMonoidHom e.injective).toEquiv
    rw [hv,Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,
      Matrix.PSL3Two.card_lineParabolicSL,Matrix.PSL3Two.card_borelSL] at hc
    exact hc
  · exact hv

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The two-residual and the prescribed Sylow supplement the literal overlap. -/
theorem overlap_residual_sup_sylow
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    (pResidual 2 (H ⊓ D.maximalLocal : Subgroup G)).map (H ⊓ D.maximalLocal).subtype ⊔
      (T : Subgroup G) = H ⊓ D.maximalLocal := by
  have hTP : (T : Subgroup G) ≤ H ⊓ D.maximalLocal :=
    le_inf hH.1.1.2 (le_normalizer_componentOrbit L T)
  have hg := congrArg (map (H ⊓ D.maximalLocal).subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTP))
  simpa only [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTP,
    ← MonoidHom.range_eq_map, range_subtype] using hg

/-- The source subgroup O²(H∩M)T₀ is exactly H∩L₀. -/
theorem overlap_residual_sup_orbit_sylow
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    (pResidual 2 (H ⊓ D.maximalLocal : Subgroup G)).map (H ⊓ D.maximalLocal).subtype ⊔
      ((T : Subgroup G) ⊓ localOrbit T L) = H ⊓ localOrbit T L := by
  let P := H ⊓ D.maximalLocal
  let N := (pResidual 2 P).map P.subtype
  have hNP : N ≤ P := map_subtype_le _
  have hNR : N ≤ localOrbit T L := overlap_residual_le_orbit D hfaith hmany s hH
  have hPN : P ≤ normalizer (N : Set G) := P.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image P (pResidual 2 P))
  have hTP : (T : Subgroup G) ≤ P :=
    le_inf hH.1.1.2 (le_normalizer_componentOrbit L T)
  apply le_antisymm
  · exact sup_le (le_inf (hNP.trans inf_le_left) hNR)
      (inf_le_inf_right _ hH.1.1.2)
  · intro x hx
    have hxP : x ∈ P := ⟨hx.1,(localOrbit T L).le_normalizer hx.2⟩
    have hxprod : x ∈ (N : Set G) * (T : Set G) := by
      change x ∈ (N : Set G) * ((T : Subgroup G) : Set G)
      rw [← coe_mul_of_right_le_normalizer_left N (T : Subgroup G) (hTP.trans hPN)]
      exact (overlap_residual_sup_sylow D hH).symm ▸ hxP
    obtain ⟨n,hn,t,ht,rfl⟩ := hxprod
    have htR : t ∈ localOrbit T L := by
      simpa only [inv_mul_cancel_left] using
        (localOrbit T L).mul_mem ((localOrbit T L).inv_mem (hNR hn)) hx.2
    exact mul_mem_sup hn ⟨ht,htR⟩

private theorem overlap_not_two (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    ¬ IsPGroup 2 (H ⊓ D.maximalLocal : Subgroup G) := by
  intro hp
  obtain ⟨hP,f,_,hf,d,he,_,_⟩ := source_hstar_cartan_data_of_generation_gt_one D hH
    (by rw [s.generation H hH]; decide)
  have hBM := he ▸ d.hall_le
  have hBP : d.witness.abelianGroup.map H.subtype ≤ H ⊓ D.maximalLocal :=
    le_inf (map_subtype_le _) (map_le_iff_le_comap.mpr hBM)
  have hB := (hp.to_le hBP).of_equiv
    (d.witness.abelianGroup.equivMapOfInjective H.subtype H.subtype_injective).symm
  obtain ⟨n,hn⟩ := hB.exists_card_eq
  have hcard : Nat.card d.witness.abelianGroup = 1 :=
    Nat.eq_one_of_dvd_coprimes (d.witness.odd.coprime_two_right.pow_right n)
      (dvd_refl _) (hn ▸ dvd_refl _)
  have hcyc : Nat.card d.witness.cyclicGroup = 1 := Nat.eq_one_of_dvd_one (by
    simpa only [hcard] using card_dvd_of_le d.witness.cyclic_le)
  rw [d.witness.card] at hcyc
  rw [s.generation H hH] at hf
  have hpow : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hf
  omega

private theorem orbit_overlap_not_two
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    ¬ IsPGroup 2 (H ⊓ localOrbit T L : Subgroup G) := by
  intro hp
  have hnorm : (T : Subgroup G) ≤ normalizer (H ⊓ localOrbit T L : Set G) :=
    (le_inf (hH.1.1.2.trans H.le_normalizer) (le_normalizer_componentOrbit L T)).trans
      inf_normalizer_le_normalizer_inf
  have h2 := hp.to_sup_of_normal_left' T.isPGroup' hnorm
  apply overlap_not_two D s hH
  apply h2.to_le
  rw [← overlap_residual_sup_sylow D hH]
  exact sup_le_sup (le_inf ((map_subtype_le _).trans inf_le_left)
    (overlap_residual_le_orbit D hfaith hmany s hH)) le_rfl

private theorem orbit_sylow : ∃ S : Sylow 2 (localOrbit T L),
    (S : Subgroup (localOrbit T L)) = (T : Subgroup G).subgroupOf (localOrbit T L) := by
  let R := localOrbit T L
  let J := localJoin T L
  have hRJ : R ≤ J := le_sup_left
  let : (R.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le R.le_normalizer (le_normalizer_componentOrbit L T))
  obtain ⟨P,hP⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal
    (R.subgroupOf J)
  let e := subgroupOfEquivOfLe hRJ
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change (P : Subgroup (R.subgroupOf J)).map e.toMonoidHom = _
  rw [hP]
  ext k
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ha
  · intro hk
    exact ⟨⟨⟨k,hRJ k.prop⟩,k.prop⟩,hk,rfl⟩

private theorem exchanged_orbit_quotient
    (s : SourceLinearThreeSurvivor T D) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hker : pCore 2 (localOrbit T L) ≤ H.subgroupOf (localOrbit T L)) :
    ∃ q : localOrbit T L →* (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL),
      Function.Surjective q ∧ q.ker = pCore 2 (localOrbit T L) ∧
      ((H.subgroupOf (localOrbit T L)).map q).comap (MonoidHom.inl _ _) =
        ((H.subgroupOf (localOrbit T L)).map q).comap (MonoidHom.inr _ _) := by
  let R := localOrbit T L
  have hLR : L ≤ R := le_componentOrbit L T
  have hRt : R.map (MulAut.conj s.exchange).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T s.exchange_mem)
  let τ : MulAut R := ((MulAut.conj s.exchange).subgroupMap R).trans (MulEquiv.subgroupCongr hRt)
  let A := L.subgroupOf R
  let B := A.map τ.toMonoidHom
  have hA : A.IsCComponent :=
    D.maximal.1.1.subgroupOf_of_le hLR (componentOrbit_le_sup L T)
  have hB : B.IsCComponent := hA.map_equiv τ
  have hmapA : A.map R.subtype = L := map_subgroupOf_eq_of_le hLR
  have hmapB : B.map R.subtype = L.map (MulAut.conj s.exchange).toMonoidHom := by
    rw [show B = A.map τ.toMonoidHom from rfl,map_map,
      show R.subtype.comp τ.toMonoidHom =
        (MulAut.conj s.exchange).toMonoidHom.comp R.subtype from rfl,←map_map,hmapA]
  have hne : A ≠ B := by
    intro he
    apply s.exchange_moves
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map R.subtype) he).symm.trans hmapA)
  have hp : L ⊔ L.map (MulAut.conj s.exchange).toMonoidHom = R :=
    (componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 (Bender.survivor_nonnormal s))
      inf_le_right s.exchange_mem s.exchange_moves).symm
  have hgen : A ⊔ B = ⊤ := by
    apply map_injective R.subtype_injective
    rw [Subgroup.map_sup,hmapA,hmapB,←MonoidHom.range_eq_map,range_subtype,hp]
  let a : A ≃* L := subgroupOfEquivOfLe hLR
  let eA := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans s.quotient
  let b : A ≃* B := τ.subgroupMap A
  let eB := (QuotientGroup.congr _ _ b.symm (pCore_map_iso 2 b.symm)).trans eA
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup Matrix.PSL3Two.SL := Matrix.PSL3Two.equiv.isSimpleGroup
  obtain ⟨q,hq,hk,hqa,hqb⟩ :=
    exists_twoCore_product_of_simple_pair A B hA hB hne hgen eA eB
  refine ⟨q,hq,hk,?_⟩
  have hτH (x : R) : (τ x : G) ∈ H ↔ (x : G) ∈ H := by
    exact (H.le_normalizer (hTH s.exchange_mem) x).symm
  have hqb' (x : A) : q (τ x) = (1,eA (QuotientGroup.mk' (pCore 2 A) x)) := by
    have hh := hqb (b x)
    change q (τ x) = (1,eA ((QuotientGroup.congr _ _ b.symm (pCore_map_iso 2 b.symm))
      (QuotientGroup.mk' (pCore 2 B) (b x)))) at hh
    have hc := (QuotientGroup.congr_mk' (pCore 2 B) (pCore 2 A) b.symm
      (pCore_map_iso 2 b.symm) (b x)).trans
      (congrArg (QuotientGroup.mk' (pCore 2 A)) (b.symm_apply_apply x))
    exact hh.trans (congrArg (fun z => (1,eA z)) hc)
  have hpre (x : R) : q x ∈ (H.subgroupOf R).map q ↔ x ∈ H.subgroupOf R := by
    change x ∈ ((H.subgroupOf R).map q).comap q ↔ _
    rw [comap_map_eq_self (hk ▸ hker)]
  ext c
  obtain ⟨x,hx⟩ := eA.surjective c
  obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective (pCore 2 A) x
  have ha' : eA (QuotientGroup.mk' (pCore 2 A) a) = c := by rw [ha,hx]
  change (c,1) ∈ (H.subgroupOf R).map q ↔ (1,c) ∈ (H.subgroupOf R).map q
  rw [←ha',←hqa a,←hqb' a,hpre,hpre]
  exact (hτH a).symm

/-- Both actual component intersections are maximal parabolics, under a single
marking which also retains the original orbit Sylow subgroup. -/
theorem orbit_overlap_parabolic
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    ∃ e : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃*
        (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL),
      let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))
      ((T : Subgroup G).subgroupOf (localOrbit T L)).map q =
        Matrix.PSL3Two.borelSL.prod Matrix.PSL3Two.borelSL ∧
      ((H.subgroupOf (localOrbit T L)).map q =
        Matrix.PSL3Two.lineParabolicSL.prod Matrix.PSL3Two.lineParabolicSL) := by
  let R := localOrbit T L
  let V := H.subgroupOf R
  obtain ⟨S,hS⟩ := orbit_sylow (T := T) (L := L)
  have hSV : (S : Subgroup R) ≤ V := by
    rw [hS]
    exact subgroupOf_mono R hH.1.1.2
  obtain ⟨q,hq,hk,hequal⟩ := exchanged_orbit_quotient D s H hH.1.1.2
    ((pCore_isPGroup.le_sylow_of_normal S).trans hSV)
  let S' := S.mapSurjective (f := q) hq
  have hV6 : IsPGroup 6 V := by
    have he : H.subgroupOf R = (H ⊓ R).subgroupOf R := by
      ext x
      exact ⟨fun hx => ⟨hx,x.property⟩,fun hx => hx.1⟩
    rw [show V = H.subgroupOf R from rfl,he]
    exact ((overlap_isSixGroup D hfaith hmany s hH).to_le
      (inf_le_inf_left H R.le_normalizer)).comap_subtype
  have hnot : ¬ IsPGroup 2 (V.map q) := by
    intro hp
    have hV2 := hp.comap_of_ker_isPGroup q (hk ▸ pCore_isPGroup)
    rw [comap_map_eq_self ((hk ▸ pCore_isPGroup.le_sylow_of_normal S).trans hSV)] at hV2
    have he : V = (H ⊓ R).subgroupOf R := by
      ext x
      exact ⟨fun hx => ⟨hx,x.property⟩,fun hx => hx.1⟩
    rw [he] at hV2
    exact orbit_overlap_not_two D hfaith hmany s hH
      (hV2.of_equiv (subgroupOfEquivOfLe inf_le_right))
  obtain ⟨a,ha,hV⟩ := product_equal_overgroup_marking S' (V.map q)
    (map_mono hSV) (hV6.map q) hnot hequal
  let e₀ : (R ⧸ pCore 2 R) ≃* (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have he₀ : e₀.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R)) = q := by
    apply MonoidHom.ext
    intro x
    have he : (QuotientGroup.quotientMulEquivOfEq hk.symm) (QuotientGroup.mk' (pCore 2 R) x) =
        QuotientGroup.mk' q.ker x := QuotientGroup.quotientMulEquivOfEq_mk hk.symm x
    exact (congrArg (QuotientGroup.quotientKerEquivOfSurjective q hq) he).trans rfl
  refine ⟨e₀.trans a,?_,?_⟩
  · change ((T : Subgroup G).subgroupOf R).map
      (a.toMonoidHom.comp (e₀.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R)))) = _
    rw [he₀,←map_map,←hS]
    exact ha
  · change V.map (a.toMonoidHom.comp (e₀.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R)))) = _
    rw [he₀,←map_map]
    exact hV

/-- The source's literal O²(H∩M)T₀ is the paired maximal parabolic in L₀.
The quotient map and Sylow mark are shared by both equations. -/
theorem overlap_residual_parabolic_placement
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    ∃ e : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃*
        (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL),
      let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))
      ((T : Subgroup G).subgroupOf (localOrbit T L)).map q =
        Matrix.PSL3Two.borelSL.prod Matrix.PSL3Two.borelSL ∧
      ((((pResidual 2 (H ⊓ D.maximalLocal : Subgroup G)).map (H ⊓ D.maximalLocal).subtype ⊔
        ((T : Subgroup G) ⊓ localOrbit T L)).subgroupOf (localOrbit T L)).map q =
        Matrix.PSL3Two.lineParabolicSL.prod Matrix.PSL3Two.lineParabolicSL) := by
  obtain ⟨e,hs,hp⟩ := orbit_overlap_parabolic D hfaith hmany s hH
  refine ⟨e,hs,?_⟩
  rw [overlap_residual_sup_orbit_sylow D hfaith hmany s hH]
  have he : (H ⊓ localOrbit T L).subgroupOf (localOrbit T L) = H.subgroupOf (localOrbit T L) := by
    ext x
    exact ⟨fun hx => hx.1,fun hx => ⟨hx,x.property⟩⟩
  rw [he]
  exact hp

/-- Restriction to L₀ preserves the embedded two-residual of the overlap. -/
theorem overlap_residual_eq_orbit_residual
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    (pResidual 2 (H ⊓ D.maximalLocal : Subgroup G)).map (H ⊓ D.maximalLocal).subtype =
      (pResidual 2 (H ⊓ localOrbit T L : Subgroup G)).map (H ⊓ localOrbit T L).subtype := by
  let P := H ⊓ D.maximalLocal
  let N := (pResidual 2 P).map P.subtype
  let S := (T : Subgroup G) ⊓ localOrbit T L
  have hN : IsPPerfect 2 N := (isPPerfect_pResidual (G := P) 2).of_surjective
    (P.subtype.subgroupMap (pResidual 2 P)) (P.subtype.subgroupMap_surjective _)
  have hn : S ≤ normalizer (N : Set G) :=
    (inf_le_left.trans (le_inf hH.1.1.2 (le_normalizer_componentOrbit L T))).trans
      (P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pResidual 2 P)))
  have hh := embedded_pResidual_join_pGroup N S hN (T.isPGroup'.to_le inf_le_left) hn
  rw [show N ⊔ S = H ⊓ localOrbit T L from overlap_residual_sup_orbit_sylow D hfaith hmany s hH] at hh
  exact hh.symm

/-- The original residual maps to the residual of the actual marked paired parabolic.
This uses the same map as the Sylow and whole-overlap marking. -/
theorem overlap_residual_marked
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    ∃ e : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃*
        (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL),
      let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))
      ((T : Subgroup G).subgroupOf (localOrbit T L)).map q =
        Matrix.PSL3Two.borelSL.prod Matrix.PSL3Two.borelSL ∧
      ((H.subgroupOf (localOrbit T L)).map q =
        Matrix.PSL3Two.lineParabolicSL.prod Matrix.PSL3Two.lineParabolicSL) ∧
      (((pResidual 2 (H ⊓ D.maximalLocal : Subgroup G)).map (H ⊓ D.maximalLocal).subtype).subgroupOf
        (localOrbit T L)).map q =
        (pResidual 2 (Matrix.PSL3Two.lineParabolicSL.prod Matrix.PSL3Two.lineParabolicSL)).map
          (Matrix.PSL3Two.lineParabolicSL.prod Matrix.PSL3Two.lineParabolicSL).subtype := by
  obtain ⟨e,hs,hp⟩ := orbit_overlap_parabolic D hfaith hmany s hH
  let R := localOrbit T L
  let V := H.subgroupOf R
  let N := (pResidual 2 (H ⊓ D.maximalLocal : Subgroup G)).map (H ⊓ D.maximalLocal).subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hN : N.subgroupOf R = (pResidual 2 V).map V.subtype := by
    apply map_injective R.subtype_injective
    rw [map_subgroupOf_eq_of_le (overlap_residual_le_orbit D hfaith hmany s hH),
      map_embedded_pResidual]
    change N = (pResidual 2 ((H.subgroupOf R).map R.subtype)).map _
    rw [subgroupOf_map_subtype]
    exact overlap_residual_eq_orbit_residual D hfaith hmany s hH
  refine ⟨e,hs,hp,?_⟩
  change (N.subgroupOf R).map q = _
  rw [hN,map_embedded_pResidual]
  exact congrArg (fun P : Subgroup (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL) =>
    (pResidual 2 P).map P.subtype) hp


end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
