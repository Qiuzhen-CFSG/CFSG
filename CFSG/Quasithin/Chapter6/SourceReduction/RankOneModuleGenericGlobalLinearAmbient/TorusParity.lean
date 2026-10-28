module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeEven.TorusParity
public import Theory.GroupTheory.Involution.Dihedral
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.AmbientGeneration

/-!
# Odd Weyl products and the disjoint-Sylow branch in the prepared linear row

Ambient involution fusion transports the established centralizer core to an
ambient Sylow at every involution. This rules out even-order products of the
two exact native reflections: their cubic torus action would otherwise make
a reflection centralize the marked odd torus. Both comparison orientations
and field four are included, with escape from the whole full-normalizer overlap.

For central involutions in two distinct Sylows, the same core theorem identifies
odd-order products with disjointness. In that case a dihedral reflection swaps
the actual Sylows and normalizes the intersection of their full normalizers.
These discharge the parity and disjoint-Sylow steps in the source Hall-coset
argument. The nontrivial-intersection cases and Hall-normalizer coset bound
still have to give cube membership in the whole overlap before recognition.

Source: Aschbacher–Smith, F.4.46(2), F.4.48 and F.4.49, printed pp.297–299
of `refs/quasithin.pdf`. The original §5.3.7 and ambient-generation inputs are
proved in the imported prepared-row modules, not new hypotheses here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include d h hH hp hm hF he hmax

/-- Every involution has an ambient Sylow as the literal two-core of its
centralizer, and that full centralizer normalizes this same Sylow. -/
theorem Preparation.linear_involution_centralizer_sylow
    (x : G) (hx : orderOf x=2) :
    ∃ P : Sylow 2 G, (centralizer ({x} : Set G)).pCoreIn 2=(P : Subgroup G) ∧
      centralizer ({x} : Set G) ≤ normalizer (P : Set G) := by
  obtain ⟨z,hz,hz2,_⟩ := d.linear_exists_sylow_central_involution h hH hp F hm hF he hmax
  obtain ⟨g,hg⟩ := isConj_iff.mp (d.linear_involutions_isConj h hH hp F hm hF he hmax z x hz2 hx)
  have hcore := (d.linear_centralizer_core_eq_sourceS h hH hp F hm hF he hmax z hz2 hz).trans
    (d.linear_sourceS_eq_sylow h hH hp F hm hF he hmax)
  have hmap : (centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({x} : Set G) := by
    rw [Theory.GroupTheory.map_centralizer_equiv,Set.image_singleton]
    exact congrArg (fun a : G => centralizer ({a} : Set G)) hg
  have hP : (centralizer ({x} : Set G)).pCoreIn 2 = ((g • T : Sylow 2 G) : Subgroup G) := by
    change _ = (T : Subgroup G).map (MulAut.conj g).toMonoidHom
    rw [←hcore,map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,hmap]
  refine ⟨g • T,hP,?_⟩
  change centralizer ({x} : Set G) ≤ normalizer (((g • T : Sylow 2 G) : Subgroup G) : Set G)
  rw [←hP]
  exact (centralizer ({x} : Set G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))



/-- A native completion in original G with both original parabolic images
and the whole common Borel. The Boolean records the comparison orientation. -/
theorem Preparation.linear_native_ambient_completion :
    ∃ c : ChapterF.SourceCompletion.LinearThreeEven.NativeCompletion F G,
      ∃ i : Bool,
      c.family i=ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ∧
      c.family (!i)=ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ∧
      c.middle.range=ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) := by
  let P₀ := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let P₁ := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  have hgen : P₀ ⊔ P₁=⊤ := by
    rw [ChapterF.Source.parabolics_generate]
    change L ⊔ residual H ⊔ sourceS L H=⊤
    rw [(d.linear_ambient_generation h hH hp F hm hF he hmax).2,top_sup_eq]
  let c₀ : RankTwoAmalgam.FaithfulCompletion
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (G := G) :=
    .ofSubgroups P₀ (P₀ ⊓ P₁) P₁ inf_le_left inf_le_right hgen
  have hmid : c₀.middle.range=ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) :=
    (range_subtype _).trans (ChapterF.Source.lemma_F_1_3_6 (d.hypothesisF11 h hH.1.1.2))
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · refine ⟨c₀.comapIso e.symm,false,?_,?_,?_⟩
    · change (c₀.comapIso e.symm).left.range=_
      rw [RankTwoAmalgam.FaithfulCompletion.comapIso_left_range]
      exact range_subtype _
    · change (c₀.comapIso e.symm).right.range=_
      rw [RankTwoAmalgam.FaithfulCompletion.comapIso_right_range]
      exact range_subtype _
    · simpa only [RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using hmid
  · let c := c₀.comapIso e.symm
    refine ⟨ChapterF.SourceCompletion.UnitaryNonbinary.Generated.reverseCompletion c,true,?_,?_,?_⟩
    · change c.left.range=_
      rw [RankTwoAmalgam.FaithfulCompletion.comapIso_left_range]
      exact range_subtype _
    · change c.right.range=_
      rw [RankTwoAmalgam.FaithfulCompletion.comapIso_right_range]
      exact range_subtype _
    · change (c.right.comp (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).left).range=_
      calc
        _ = c.middle.range := congrArg MonoidHom.range c.compatible.symm
        _ = _ := by simpa only [c,RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using hmid

/-- Both original endpoint involutions normalize one marked odd split torus;
their product has odd order, and its cube centralizes that same torus.
Escape is from the WHOLE full-normalizer overlap, not just its Sylow subgroup.
Cube membership in that overlap is the remaining source obligation. -/
theorem Preparation.linear_odd_weyl_witness :
    ∃ D : Subgroup G, D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) ∧
      Odd (Nat.card D) ∧ ∃ s t : G,
      s ∈ normalizer (L : Set G) ∧ t ∈ normalizer (residual H : Set G) ∧
      s ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
      t ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
      s^2=1 ∧ t^2=1 ∧ s ∈ normalizer (D : Set G) ∧ t ∈ normalizer (D : Set G) ∧
      (s*t)^3 ∈ centralizer (D : Set G) ∧ Odd (orderOf (s*t)) := by
  obtain ⟨c,i,hleft,hright,hmid⟩ := d.linear_native_ambient_completion h hH hp F hm hF he hmax
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let N := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
  have hf := d.hypothesisF11 h hH.1.1.2
  have hs := d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he
  have hPN (j : Fin 2) : P j ⊓ N = C := by
    dsimp only [N]
    rw [←d.linear_common_normalizer_eq h hH hp F hm hF he hmax]
    simpa only [inf_eq_left.mpr (hs j)] using (hf.commonBorel_eq_normalizer j).symm
  have hP₀ : P 0 ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show L ≤ P 0 from le_sup_left.trans le_sup_left)).mp
      (hf.local_normal_in_parabolic 0)
  have hP₁ : P 1 ≤ normalizer (residual H : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show residual H ≤ P 1 from le_sup_left.trans le_sup_left)).mp
      (hf.local_normal_in_parabolic 1)
  have hsm : c.weyl i ∈ P 0 := hleft.le (c.weyl_mem i)
  have htm : c.weyl (!i) ∈ P 1 := hright.le (c.weyl_mem (!i))
  have hout (j : Bool) (k : Fin 2) (hj : c.weyl j ∈ P k) : c.weyl j ∉ N := by
    intro hh
    apply c.weyl_not_mem_middle j
    exact hmid.symm ▸ ((hPN k).le ⟨hj,hh⟩)
  have hm' : 1<m := (d.linear_core_structure h hH hp F hm hF he).1 ▸ h.exponent
  refine ⟨c.torusHom.range,?_,c.torusHom_odd hF,c.weyl i,c.weyl (!i),
    hP₀ hsm,hP₁ htm,hout i 0 hsm,hout (!i) 1 htm,c.weyl_sq i,c.weyl_sq (!i),
    c.weyl_normalizes_torus i,c.weyl_normalizes_torus (!i),c.weyl_product_cube_centralizes i,?_⟩
  · rintro x ⟨a,rfl⟩
    apply hmid.le
    exact ⟨_,rfl⟩
  · exact c.weyl_product_odd hF hm'
      (fun z hz => by
        obtain ⟨P,_,hP⟩ := d.linear_involution_centralizer_sylow h hH hp F hm hF he hmax z hz
        exact ⟨P,hP⟩) i



/-- A commuting involution belongs to the literal centralizer two-core. -/
theorem Preparation.linear_commuting_involution_mem_core
    (x y : G) (hx : orderOf x=2) (hy : orderOf y=2) (hxy : Commute x y) :
    x ∈ (centralizer ({y} : Set G)).pCoreIn 2 := by
  obtain ⟨P,hcore,hN⟩ := d.linear_involution_centralizer_sylow h hH hp F hm hF he hmax y hy
  rw [hcore]
  have hpX : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hx,pow_one])
  exact ((hpX.inf_normalizer_sylow P).le
    ⟨mem_zpowers x,hN (mem_centralizer_singleton_iff.mpr hxy)⟩).2

/-- The odd-product clause of source F.4.48: outside the actual Sylow
normalizer, the two Sylows are disjoint exactly when the central involutions
have odd-order product. No Hall-coset or intersection bound is assumed. -/
theorem Preparation.linear_odd_product_iff_disjoint_sylows
    (z : G) (hz : orderOf z=2) (hzZ : z ∈ centerIn (sourceS L H))
    (g : G) (hg : g ∉ normalizer (T : Set G)) :
    Odd (orderOf (z*(g*z*g⁻¹))) ↔
      Disjoint (T : Subgroup G) ((T : Subgroup G).conjBy g) := by
  let y := g*z*g⁻¹
  have hy : orderOf y=2 := (MulAut.conj g).orderOf_eq z |>.trans hz
  have hz2 : z^2=1 := hz ▸ pow_orderOf_eq_one z
  have hy2 : y^2=1 := hy ▸ pow_orderOf_eq_one y
  have hz1 : z≠1 := by intro hh; simp [hh] at hz
  have hy1 : y≠1 := by intro hh; simp [hh] at hy
  have hST := d.linear_sourceS_eq_sylow h hH hp F hm hF he hmax
  have hzT : z ∈ centerIn (T : Subgroup G) := hST ▸ hzZ
  have hzy : z≠y := by
    intro hh
    apply hg
    rw [d.linear_sylow_normalizer_eq_inter h hH hp F hm hF he hmax]
    apply d.linear_centralizer_le_inter h hH hp F hm hF he hmax z hz hzZ
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh.symm)
  have hprod : z*y≠1 := by
    intro hh
    apply hzy
    calc
      z = z*(z*y) := by rw [hh,mul_one]
      _ = y := by rw [←mul_assoc,←pow_two,hz2,one_mul]
  have hcore : (centralizer ({z} : Set G)).pCoreIn 2=(T : Subgroup G) :=
    (d.linear_centralizer_core_eq_sourceS h hH hp F hm hF he hmax z hz hzZ).trans hST
  have hcoreY : (centralizer ({y} : Set G)).pCoreIn 2=(T : Subgroup G).conjBy g := by
    change _ = (T : Subgroup G).map (MulAut.conj g).toMonoidHom
    rw [←hcore,map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
      Theory.GroupTheory.map_centralizer_equiv,Set.image_singleton]
    rfl
  constructor
  · intro hodd
    apply disjoint_iff.mpr
    by_contra hne
    obtain ⟨v,hv1⟩ := ne_bot_iff_exists_ne_one.mp hne
    have htwo : 2 ∣ orderOf (v:G) := by
      have hpV := T.isPGroup'.to_le
        (show (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g ≤ (T : Subgroup G) from inf_le_left)
      have hh := hpV.dvd_orderOf hv1
      rwa [←orderOf_coe] at hh
    let j : G := (v:G)^(orderOf (v:G)/2)
    have hj : orderOf j=2 := orderOf_pow_orderOf_div (orderOf_pos _).ne' htwo
    have hjT : j ∈ (T : Subgroup G) := (T : Subgroup G).pow_mem v.property.1 _
    have hjTg : j ∈ (T : Subgroup G).conjBy g :=
      ((T : Subgroup G).conjBy g).pow_mem v.property.2 _
    have hzj : Commute z j := (hzT.2 j hjT).symm
    have hyZ : y ∈ centerIn ((T : Subgroup G).conjBy g) := by
      change y ∈ centerIn ((T : Subgroup G).map (MulAut.conj g).toMonoidHom)
      rw [←centerIn_map_equiv]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom hzT
    have hyj : Commute y j := (hyZ.2 j hjTg).symm
    obtain ⟨P,hP,_⟩ := d.linear_involution_centralizer_sylow h hH hp F hm hF he hmax j hj
    have hzP : z ∈ (P : Subgroup G) := hP ▸
      d.linear_commuting_involution_mem_core h hH hp F hm hF he hmax z j hz hj hzj
    have hyP : y ∈ (P : Subgroup G) := hP ▸
      d.linear_commuting_involution_mem_core h hH hp F hm hF he hmax y j hy hj hyj
    have hd := P.isPGroup'.dvd_orderOf
      (g := (⟨z*y,(P : Subgroup G).mul_mem hzP hyP⟩ : P))
      (fun hh => hprod (congrArg Subtype.val hh))
    have hd' : 2 ∣ orderOf (z*y) := by simpa only [←orderOf_coe] using hd
    exact hodd.not_two_dvd_nat hd'
  · intro hdis
    by_contra hodd
    have hd := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    have ho : orderOf (z*y)=2*(orderOf (z*y)/2) := (Nat.mul_div_cancel' hd).symm
    obtain ⟨hj,hjz,hjy⟩ := BenderSuzuki.External.Suzuki.V.suzuki_ch5_proposition_1_2_iii
      ⟨hz1,hz2⟩ ⟨hy1,hy2⟩ hzy ho
    have hj2 : orderOf ((z*y)^(orderOf (z*y)/2))=2 := orderOf_eq_prime hj.2 hj.1
    have hzmem := d.linear_commuting_involution_mem_core h hH hp F hm hF he hmax _ z hj2 hz hjz
    have hymem := d.linear_commuting_involution_mem_core h hH hp F hm hF he hmax _ y hj2 hy hjy
    rw [hcore] at hzmem
    rw [hcoreY] at hymem
    exact hj.1 (disjoint_def.mp hdis hzmem hymem)



/-- The disjoint-Sylow case of Suzuki's F.4.49 argument. An actual involution
swaps the two Sylows and normalizes the intersection of their FULL normalizers. -/
theorem Preparation.linear_disjoint_sylow_swap
    (z : G) (hz : orderOf z=2) (hzZ : z ∈ centerIn (sourceS L H))
    (g : G) (hg : g ∉ normalizer (T : Set G))
    (hdis : Disjoint (T : Subgroup G) ((T : Subgroup G).conjBy g)) :
    ∃ w : G, orderOf w=2 ∧
      (T : Subgroup G).conjBy w=(T : Subgroup G).conjBy g ∧
      ((T : Subgroup G).conjBy g).conjBy w=(T : Subgroup G) ∧
      w ∈ normalizer ((normalizer (T : Set G) ⊓
        normalizer ((T : Subgroup G).conjBy g : Set G) : Subgroup G) : Set G) := by
  have hodd := (d.linear_odd_product_iff_disjoint_sylows h hH hp F hm hF he hmax z hz hzZ g hg).mpr hdis
  have hST := d.linear_sourceS_eq_sylow h hH hp F hm hF he hmax
  have hzT : z ∈ (T : Subgroup G) := hST ▸ hzZ.1
  have hz1 : z≠1 := by intro hh; simp [hh] at hz
  have hne : z≠g*z*g⁻¹ := by
    intro hh
    apply hz1
    exact disjoint_def.mp hdis hzT (hh.symm ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hzT)
  have hz2 : z^2=1 := hz ▸ pow_orderOf_eq_one z
  have hy2 : (g*z*g⁻¹)^2=1 := by
    change (MulAut.conj g z)^2=1
    rw [←map_pow,hz2,map_one]
  obtain ⟨w,hw,hwz⟩ := Matrix.PSL3.LinearAmbientGeometry.swapping_involution_of_odd_product
    z (g*z*g⁻¹) hz2 hy2 hne hodd
  have hcore := (d.linear_centralizer_core_eq_sourceS h hH hp F hm hF he hmax z hz hzZ).trans hST
  have hf (a : G) : (T : Subgroup G).conjBy a =
      (centralizer ({a*z*a⁻¹} : Set G)).pCoreIn 2 := by
    change (T : Subgroup G).map (MulAut.conj a).toMonoidHom=_
    rw [←hcore,map_pCoreIn_of_injective 2 _ _ (MulAut.conj a).injective,
      Theory.GroupTheory.map_centralizer_equiv,Set.image_singleton]
    rfl
  have hwT : (T : Subgroup G).conjBy w=(T : Subgroup G).conjBy g := by
    rw [hf w,hf g,hwz]
  have hw2 : w^2=1 := hw ▸ pow_orderOf_eq_one w
  have hwTg : ((T : Subgroup G).conjBy g).conjBy w=(T : Subgroup G) := by
    rw [←hwT,conjBy_conjBy,←pow_two,hw2,conjBy_one]
  refine ⟨w,hw,hwT,hwTg,?_⟩
  have hnT : (normalizer (T : Set G)).map (MulAut.conj w).toMonoidHom =
      normalizer ((T : Subgroup G).conjBy w : Set G) :=
    map_normalizer_eq_of_bijective (T : Subgroup G) (MulAut.conj w).bijective
  have hnTg : (normalizer ((T : Subgroup G).conjBy g : Set G)).map (MulAut.conj w).toMonoidHom =
      normalizer (((T : Subgroup G).conjBy g).conjBy w : Set G) :=
    map_normalizer_eq_of_bijective ((T : Subgroup G).conjBy g) (MulAut.conj w).bijective
  apply mem_normalizer_iff_map_conj_eq.mpr
  calc
    _ = (normalizer (T : Set G)).map (MulAut.conj w).toMonoidHom ⊓
        (normalizer ((T : Subgroup G).conjBy g : Set G)).map (MulAut.conj w).toMonoidHom :=
      map_inf _ _ _ (MulAut.conj w).injective
    _ = normalizer ((T : Subgroup G).conjBy w : Set G) ⊓
        normalizer (((T : Subgroup G).conjBy g).conjBy w : Set G) :=
      congrArg₂ (fun U V : Subgroup G => U ⊓ V) hnT hnTg
    _ = _ := by rw [hwT,hwTg]; exact inf_comm _ _

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
