module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.RadicalSeparation
public import Theory.GroupTheory.InvertingComplementNormalizer
public import Theory.SpecificGroups.SL2.OddCoreAndRank
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction

/-!
# The radical point row of the ambient normalizer containments

The actual Ξ₇(K₁) image in G₁/O₂(G₁) is its component's full seven-core.
A.3.6 supplies the natural SL₂(7) action on that plane, with the original
binary-three section excluding the nilpotent alternative. The original L₁
image complements the plane: its solvable kernel is both a two-group and
a seven-group, and the already proved product covers the quotient.

The unique involution in this complement inverts the plane. It lies in
the original Sylow and therefore in each local intersection. The proved
radical separation makes those intersections fix the involution, hence
normalize its centralizer, which is precisely the original complement.
Lifting through the whole point-core kernel proves G₃,G₆ ≤ N_G(L),
independently of the generation-one exclusion. The strict-enlargement
consumer now retains only Structural1222At from qt-d-1222-source.

The J₄ normalizer row and local assembly remain with qt-d-1251-local;
final exterior assembly remains with qt-d-1251-source.
Source: Aschbacher--Smith, 12.5.3--4 and 12.5.11(2), pp.818--819,821.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Chapter1.Section02.LocalModels

private theorem sl2_involution_unique {F : Type*} [Field F] (hF : (2 : F) ≠ 0) :
    ∃! z : SL(2,F), orderOf z = 2 := by
  refine ⟨-1,Matrix.SpecialLinearGroup.orderOf_neg_one_eq_two hF,?_⟩
  intro z hz
  have hz2 : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
  have hd : (Matrix.SpecialLinearGroup.toGL z).det = 1 := Units.ext z.property
  rcases Matrix.GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one hF
    (Matrix.SpecialLinearGroup.toGL z) (by rw [←map_pow,hz2,map_one]) hd with he | he
  · have h1 : z = 1 := Matrix.SpecialLinearGroup.toGL_injective (by simpa using he)
    simp [h1] at hz
  · exact Subtype.ext (congrArg Units.val he)

private theorem normalizes_natural_seven_complement
    {E : Type*} [Group E] [Finite E]
    (C X B A : Subgroup E) [C.Normal]
    (hXC : X ≤ C) (hBC : B ≤ C) (hgen : X ⊔ B = C)
    (hcore : X.subgroupOf C = pCore 7 C)
    (hact : NaturalSL2Action C (pCore 7 C) 7)
    [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hXA : Disjoint X A)
    (R : Sylow 2 E) (hRB : (R : Subgroup E) ≤ normalizer (B : Set E))
    (hRA : (R : Subgroup E) ≤ A) : A ≤ normalizer (B : Set E) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let N := pCore 7 C
  obtain ⟨F,_,_,hF,v,ρ,hρ⟩ := hact
  let q : C →* SL(2,F) := ρ.toMonoidHom.comp (QuotientGroup.mk' N)
  have hq : q.ker = X.subgroupOf C := by
    rw [MonoidHom.ker_comp_of_injective _ _ ρ.injective,QuotientGroup.ker_mk',hcore]
  let f := q.comp (inclusion hBC)
  have hker7 : IsPGroup 7 f.ker := by
    rw [←MonoidHom.comap_ker,hq,hcore]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hBC)
  let : Group.IsNilpotent f.ker := hker7.isNilpotent
  have hker2 := PerfectCoreTwoExtension.ker_isTwoGroup f
  have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp
    (disjoint_self.mp (hker2.disjoint_of_coprime hker7 (by decide)))
  have hqsurj := ρ.surjective.comp (QuotientGroup.mk'_surjective N)
  have hftop : f.range = ⊤ := by
    have htop : N ⊔ B.subgroupOf C = ⊤ := by
      rw [show N = pCore 7 C from rfl,←hcore,←subgroupOf_sup hXC hBC,hgen,subgroupOf_self]
    have hh := congrArg (map q) htop
    have hnq : N.map q = ⊥ := by
      rw [Subgroup.map_eq_bot_iff,hq,hcore]
    rw [Subgroup.map_sup,hnq,bot_sup_eq,map_top_of_surjective q hqsurj] at hh
    have hr : f.range = (B.subgroupOf C).map q := by
      rw [MonoidHom.range_comp]
      congr 1
      ext c
      constructor
      · rintro ⟨b,rfl⟩; exact b.property
      · intro hc; exact ⟨⟨c,hc⟩,rfl⟩
    exact hr.trans hh
  let e : B ≃* SL(2,F) := MulEquiv.ofBijective f ⟨hf,MonoidHom.range_eq_top.mp hftop⟩
  have hX7 : IsPGroup 7 X := by
    have hp : IsPGroup 7 (X.subgroupOf C) := hcore.symm ▸ pCore_isPGroup
    exact hp.of_equiv (subgroupOfEquivOfLe hXC)
  have hodd : Odd (Nat.card X) := by
    obtain ⟨n,hn⟩ := hX7.exists_card_eq
    rw [hn]
    exact Odd.pow (by decide : Odd 7)
  have htwo : (2 : F) ≠ 0 := GorensteinWalter.two_ne_zero_of_odd_card F (hF ▸ (by decide : Odd 7))
  apply normalizes_complement_of_unique_quotient_involution C X B A hXC hBC hgen hXA hodd q hq e
    (sl2_involution_unique htwo) ?_ R hRB hRA
  intro z hz x hx
  have hez : f z = -1 := (sl2_involution_unique htwo).unique
    ((e.orderOf_eq z).trans hz) (Matrix.SpecialLinearGroup.orderOf_neg_one_eq_two htwo)
  let xN : N := ⟨⟨x,hXC hx⟩,by
    change (⟨x,hXC hx⟩ : C) ∈ pCore 7 C
    rw [←hcore]
    exact hx⟩
  have hi := hρ (inclusion hBC z) xN
  change v _ = Multiplicative.ofAdd (Matrix.mulVec (f z).val (Multiplicative.toAdd (v xN))) at hi
  rw [hez] at hi
  have heq : (⟨_,(inferInstance : N.Normal).conj_mem xN xN.property (inclusion hBC z)⟩ : N) = xN⁻¹ := by
    apply v.injective
    rw [hi,map_inv]
    change Multiplicative.ofAdd (Matrix.mulVec (-1 : Matrix (Fin 2) (Fin 2) F) _) = _
    rw [Matrix.neg_mulVec,Matrix.one_mulVec]
    rfl
  exact congrArg (fun a : N => ((a : C) : E)) heq

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The literal radical image is the full seven-core of the point-component
image. The original quotient map is retained. -/
theorem point_radical_image_eq_seven_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    (s.pointCoreImage (Chapter1.XiP 7 K)).subgroupOf (s.pointCoreImage K) =
      pCore 7 (s.pointCoreImage K) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let C := s.pointCoreImage K
  let X := s.pointCoreImage (Chapter1.XiP 7 K)
  let f := s.pointCoreImageHom K hK.1
  let e := s.pointComponentCoreEquivImage hK.1 hN
  have hf : f = e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)) := by
    ext k
    exact (s.pointCoreImageHom_apply K hK.1 k).trans
      (s.pointComponentCoreEquivImage_mk hK.1 hN k).symm
  have himage : (Chapter1.xiPIn 7 K).map f = X.subgroupOf C := by
    ext x
    constructor
    · rintro ⟨k,hk,rfl⟩
      change (s.pointCoreImageHom K hK.1 k : s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1)) ∈ X
      rw [s.pointCoreImageHom_apply]
      exact mem_map_of_mem _ (show (⟨k,hK.1 k.property⟩ : s.marking.Gi 1) ∈
        (Chapter1.XiP 7 K).subgroupOf (s.marking.Gi 1) from mem_map_of_mem K.subtype hk)
    · rintro ⟨k,hk,hkx⟩
      obtain ⟨b,hb,hbk⟩ := hk
      refine ⟨b,hb,?_⟩
      apply Subtype.ext
      change (s.pointCoreImageHom K hK.1 b : s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1)) = x
      rw [s.pointCoreImageHom_apply]
      have hkk : (⟨b,hK.1 b.property⟩ : s.marking.Gi 1) = k := Subtype.ext hbk
      exact (congrArg (QuotientGroup.mk' (pCore 2 (s.marking.Gi 1))) hkk).trans hkx
  rw [←himage,hf,←map_map,Chapter1.xiPIn_map_quotient (by decide : Odd 7)]
  obtain ⟨hm,_⟩ := s.local_component_nonquasisimple_seven_core h 1 (.inl rfl) hK hLK hn
  have hω : omega (pCore 7 (K ⧸ pCore 2 K)) (p := 7) 1 = ⊤ := by
    apply Chapter1.RadicalStructure.omega_top
    intro x
    apply hm.some.injective
    rw [map_pow,map_one]
    apply congrArg Multiplicative.ofAdd
    funext j
    change (7 : ℕ) • (hm.some x).toAdd j = 0
    have hz : Nat.card (ZMod 7) • (hm.some x).toAdd j = 0 := card_nsmul_eq_zero'
    simpa only [Nat.card_zmod] using hz
  change ((omega (pCore 7 (K ⧸ pCore 2 K)) (p := 7) 1).map _).map _ = _
  rw [hω,←MonoidHom.range_eq_map,range_subtype,pCore_map_iso]

/-- A.3.6 supplies the natural SL₂(7) action on the actual seven-core;
the original binary-three section excludes the nilpotent alternative. -/
theorem point_radical_natural_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    NaturalSL2Action (s.pointCoreImage K) (pCore 7 (s.pointCoreImage K)) 7 := by
  let C := s.pointCoreImage K
  let e := s.pointComponentCoreEquivImage hK.1 hN
  have hnC : ¬ IsQuasisimple C := fun hq => hn (by
    let := hq
    exact IsQuasisimple.of_mulEquiv e.symm)
  have hc := Chapter1.Section02.proposition_1_2_1_four_earlier_conclusion
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    (ChapterE.Structure.sqtk_two_quotient
      (h.simpleQTKE.twoLocal_sqtk (s.marking.Gi_twoLocal 1 (.inl rfl)))
      (pCore 2 (s.marking.Gi 1)) pCore_isPGroup) hK.2
  change Chapter1.Section02.A36Conclusion C at hc
  have ha := Chapter1.RadicalStructure.nonsimple_radical hc hnC
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨hm,_⟩ := s.local_component_nonquasisimple_seven_core h 1 (.inl rfl) hK hLK hn
  let e7 := (e.subgroupMap (pCore 7 (K ⧸ pCore 2 K))).trans (MulEquiv.subgroupCongr (pCore_map_iso 7 e))
  have h7 : Nat.card (pCore 7 C) = 49 := by
    rw [←Nat.card_congr e7.toEquiv,Nat.card_congr hm.some.toEquiv]
    simp
  have hd : 7 ∣ Nat.card (fittingSubgroup C) :=
    (show 7 ∣ Nat.card (pCore 7 C) by rw [h7]; decide).trans
      (card_dvd_of_le (pCore_le_fitting C 7))
  rcases ha with ha | ha
  · obtain ⟨p,hp,hp3,hact⟩ := ha.2
    have hc := (Chapter1.RadicalStructure.natural_elementary hact).2
    have h7p : 7 = p := (Nat.prime_dvd_prime_iff_eq (by decide) hp).mp
      ((by decide : Nat.Prime 7).dvd_of_dvd_pow (by simpa only [←ha.1,hc] using hd))
    subst p
    have hcore : generalizedFitting C = pCore 7 C := ha.1.trans
      (Chapter1.RadicalStructure.fitting_eq_core (by
        rw [←ha.1]
        exact IsPGroup.of_card hc))
    simpa only [hcore] using hact
  · let B := s.marking.Li 1
    let : Group.IsPerfect B := s.marking.Li_perfect 1
    let : IsSimpleGroup SL(3,ZMod 2) := Atlas.Comparisons.Exceptional.sl3Two_simple
    let b : (B ⧸ pCore 2 B) ≃* SL(3,ZMod 2) := s.marking.LiCoreEquiv 1 (.inl rfl)
    let : IsSimpleGroup (B ⧸ pCore 2 B) := b.isSimpleGroup
    have hb : Nat.card (B ⧸ pCore 2 B) = 168 :=
      (Nat.card_congr (s.marking.LiCoreEquiv 1 (.inl rfl)).toEquiv).trans Atlas.Comparisons.Exceptional.sl3Two_card
    let f : B →* C := (s.pointCoreImageHom K hK.1).comp (inclusion hLK)
    have hk : IsPGroup 2 f.ker := by
      rw [←MonoidHom.comap_ker]
      exact (s.pointCoreImageHom_ker_isPGroup K hK.1).comap_of_injective _ (inclusion_injective hLK)
    let : Group.IsNilpotent f.ker := hk.isNilpotent
    let := ha.2.1
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := ha.2.2.1
    let g := a.toMonoidHom.comp ((QuotientGroup.mk' (generalizedFitting C)).comp f)
    let : Group.IsSolvable g.ker := by
      change Group.IsSolvable (a.toMonoidHom.comp ((QuotientGroup.mk' (generalizedFitting C)).comp f)).ker
      rw [MonoidHom.ker_comp_of_injective _ _ a.injective,←MonoidHom.comap_ker,QuotientGroup.ker_mk']
      exact isSolvable_comap_of_solvable_ker f _
    have he := Theory.SL2.prime_eq_seven_of_solvable_kernel hb (by decide : Nat.Prime 5) (by decide) hF g
    norm_num at he

/-- In the radical point row the original local intersection normalizes the
original point residual after projection through the full point-core kernel. -/
theorem point_radical_intersection_image_normalizes_point
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K))
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    s.pointCoreImage (s.marking.Gi i ⊓ s.marking.Gi 1) ≤
      normalizer (s.pointCoreImage (s.marking.Li 1) : Set _) := by
  let H := s.marking.Gi 1
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := s.pointCoreImage K
  let X := s.pointCoreImage (Chapter1.XiP 7 K)
  let B := s.pointCoreImage (s.marking.Li 1)
  let A := s.pointCoreImage (s.marking.Gi i ⊓ H)
  let R := (T.subtype s.sylow_le_G₁).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  let := hN
  let : C.Normal := Subgroup.Normal.map hN q (QuotientGroup.mk'_surjective _)
  have hXC : X ≤ C := s.pointCoreImage_mono (Chapter1.XiP_le 7 K)
  have hBC : B ≤ C := s.pointCoreImage_mono hLK
  have hgen : X ⊔ B = C := by
    have he := congrArg s.pointCoreImage (s.local_component_nonquasisimple_product h 1 (.inl rfl) hK hLK hn)
    simp only [pointCoreImage,subgroupOf_sup ((Chapter1.XiP_le 7 K).trans hK.1)
      (s.marking.Li_le_Gi 1),Subgroup.map_sup] at he
    exact he.symm
  let fb := s.pointCoreImageHom (s.marking.Li 1) (s.marking.Li_le_Gi 1)
  let : Group.IsPerfect (s.marking.Li 1) := s.marking.Li_perfect 1
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := fb) (s.pointCoreImageHom_surjective _ _)
  let ebq : (B ⧸ pCore 2 B) ≃* SL(3,ZMod 2) := (fb.pCoreQuotientEquiv (s.pointCoreImageHom_surjective _ _)
    (s.pointCoreImageHom_ker_isPGroup _ _)).symm.trans (s.marking.LiCoreEquiv 1 (.inl rfl))
  let : IsSimpleGroup SL(3,ZMod 2) := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup (B ⧸ pCore 2 B) := ebq.isSimpleGroup
  have hRB : (R : Subgroup (H ⧸ pCore 2 H)) ≤ normalizer (B : Set _) :=
    (s.pointCoreImage_normalizes_point_iff (T : Subgroup G) s.sylow_le_G₁).mpr
      (s.sylow_normalizes_Li 1 (.inl rfl))
  have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
  exact normalizes_natural_seven_complement C X B A hXC hBC hgen
    (s.point_radical_image_eq_seven_core h hK hLK hN hn)
    (s.point_radical_natural_action h hK hLK hN hn)
    (s.point_radical_image_disjoint_local_intersection h hK hLK hN hn i hi)
    R hRB (s.pointCoreImage_mono (le_inf (s.sylow_le_Gi i hidx) s.sylow_le_G₁))

/-- Both source normalizer containments in the radical point row,
independent of the generation-one exclusion. -/
theorem local_normalizers_le_M_of_radical_point_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    s.marking.Gi 3 ≤ s.marking.M ∧ s.marking.Gi 6 ≤ s.marking.M := by
  have step (i : ℕ) (hi : i = 3 ∨ i = 6) : s.marking.Gi i ≤ s.marking.M := by
    apply (s.local_intersection_normalizes_point_iff h i hi).mpr
    apply (s.pointCoreImage_normalizes_point_iff _ inf_le_right).mp
    exact s.point_radical_intersection_image_normalizes_point h hK hLK hN hn i hi
  exact ⟨step 3 (.inl rfl),step 6 (.inr rfl)⟩

/-- The radical point row supplies every local containment on the original V. -/
theorem local_containments_of_radical_point_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    s.marking.Gi 3 ≤ s.marking.M ∧ s.marking.Gi 6 ≤ s.marking.M ∧
      V ≤ (s.marking.Gi 1).pCoreIn 2 := by
  obtain ⟨h3,h6⟩ := s.local_normalizers_le_M_of_radical_point_component h hK hLK hN hn
  exact ⟨h3,h6,s.seed_le_point_core_of_nonquasisimple_component h hK hLK hN hn⟩

/-- The radical row of 12.5.11(2), with both normalizer containments
discharged independently. The earlier structural input retains its source owner. -/
theorem point_component_eq_of_radical_from_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) : s.marking.Li 1 = K := by
  obtain ⟨h3,h6⟩ := s.local_normalizers_le_M_of_radical_point_component h hK hLK hN hn
  exact s.point_component_eq_of_nonquasisimple_of_source_parameters h structural h3 h6 hK hLK hN hn

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
