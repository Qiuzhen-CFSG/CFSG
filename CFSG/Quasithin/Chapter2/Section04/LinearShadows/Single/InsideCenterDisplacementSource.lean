module

public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterFieldKernelSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterDisplacementSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterPairSource
public import Theory.GroupTheory.CoboundaryDirectProduct

/-!
# Center coboundaries for an inside field involution

For the original single linear block with nontrivial center, an involution in
S outside R has fixed elements equal to coboundaries on both the distinguished
center and Z(R). The actual odd torus acts regularly on the distinguished
center, so its normalizer gives the fixed-space count. The two conjugate
central factors then give the result on Z(R).

This supplies the fixed-point lifting step in Aschbacher–Smith, 2.4.12(2),
used for the involution-generation argument of 2.4.21 on printed p.536.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- Fixed distinguished-center elements are actual conjugation coboundaries. -/
theorem source_noncenterless_distinguished_involution_coboundary
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (a : G) (haS : a∈(d.S : Subgroup d.H).map d.H.subtype) (ha2 : a^2=1)
    (haR : a∉Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    ∀ z∈distinguishedZ d, Commute a z →
      ∃ w∈distinguishedZ d, z=w*(a*w*a⁻¹)⁻¹ := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let L := d.block.map d.H.subtype
  let Z := (center L).map L.subtype
  let A := S ⊓ normalizer (c.hall : Set G)
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have hAD : A ≤ normalizer (c.torus : Set G) := torusNormalizer_preserves_borel_complement
    S R c.torus c.hall (T.isPGroup'.to_le (hRS.trans hST.le)) c.hall_odd
    c.torus_le_hall (c.torus_le_hall.trans c.hall_normalizes) c.sylow_normalizes_borel
  obtain ⟨x,hxT,hxS,hxB⟩ := c.outside
  let E := c.torus.map (MulAut.conj x⁻¹).toMonoidHom
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hindex := (d.lemma_2_4_8_1 hG T hST hsingle hK).1
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST.le).mp (normal_of_index_eq_two hindex)
  have hxA : x ∈ normalizer (A : Set G) := inf_normalizer_le_normalizer_inf
    ⟨hTS hxT, (normalizer (c.hall : Set G)).le_normalizer hxB⟩
  have hxinvA : x⁻¹ ∈ normalizer (A : Set G) := (normalizer (A : Set G)).inv_mem hxA
  have hAE : A ≤ normalizer (E : Set G) := by
    rw [← mem_normalizer_iff_map_conj_eq.mp hxinvA]
    exact (map_mono hAD).trans (c.torus.le_normalizer_map (MulAut.conj x⁻¹).toMonoidHom)
  have hEL := (source_conjugate_torus_normalizes_block d hG T hST hsingle hL hM hTM hunique
    c.torus (c.hall_odd.of_dvd_nat (card_dvd_of_le c.torus_le_hall))
    (c.torus_le_hall.trans c.hall_normalizes) x hxT hxS).2.2
  have hr := (source_center_torus_of_choice d hG T hST hsingle hL hM hTM hunique
    c.torus c.hall x hxT (c.torus_le.trans inf_le_right)
    (c.hall_odd.of_dvd_nat (card_dvd_of_le c.torus_le_hall)) c.torus_card
    (c.conjugate_pair x hxT hxS hxB) c.hall_fixed hEL).resolve_left hz
  have hzdata := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  rw [distinguishedZ_of_center_ne_bot d hz] at hzdata
  let : IsElementaryAbelian 2 Z := hzdata.1
  let : IsCyclic c.torus := c.torus_cyclic
  let : IsCyclic E := isCyclic_of_surjective
    ((MulAut.conj x⁻¹).toMonoidHom.subgroupMap c.torus)
    ((MulAut.conj x⁻¹).toMonoidHom.subgroupMap_surjective c.torus)
  let hEZ : E≤normalizer (Z:Set G) := hr.2.1
  let hSZ : S≤normalizer (Z:Set G) := hzdata.2.2.2
  let ρ := Z.normalizerMonoidHom
  let β := ρ.comp (inclusion hEZ)
  let α := ρ.comp (inclusion hSZ)
  let C := β.range
  let : IsCyclic C := isCyclic_of_surjective β.rangeRestrict β.rangeRestrict_surjective
  have hreg : ∀ v w : Z, v≠1 → w≠1 → ∃! b:C,b.val v=w := by
    intro v w hv hw
    obtain ⟨b,hb,hu⟩ := hr.2.2 v hv w hw
    refine ⟨⟨β b,⟨b,rfl⟩⟩,Subtype.ext hb,?_⟩
    intro d hd
    obtain ⟨e,he⟩ := d.property
    have he' : e=b := hu e (by
      have hh := congrArg Subtype.val hd
      rw [←he] at hh
      exact hh)
    exact Subtype.ext (he.symm.trans (congrArg β he'))
  have hC : C=(E.subgroupOf (normalizer (Z:Set G))).map ρ := by
    change (ρ.comp (inclusion hEZ)).range=_
    rw [MonoidHom.range_comp,inclusion_range]
  have hn : α.range≤normalizer (C:Set (MulAut Z)) := by
    rintro b ⟨s,rfl⟩
    obtain ⟨⟨r,f⟩,he⟩ := c.split_sylow.2 s
    have hr : α (r:S)=1 := by
      ext z
      exact mul_inv_eq_iff_eq_mul.mpr
        ((hzdata.2.2.1 z.property).2 _ r.property)
    have hf : (⟨((f:S):G),hSZ (f:S).property⟩ : normalizer (Z:Set G))∈
        normalizer (E.subgroupOf (normalizer (Z:Set G)):Set _) := by
      rw [←subgroupOf_normalizer_eq hEZ]
      exact hAE f.property
    have hf' : α (f:S)∈normalizer (C:Set (MulAut Z)) := by
      rw [hC]
      exact (E.subgroupOf (normalizer (Z:Set G))).le_normalizer_map ρ
        (mem_map_of_mem ρ hf)
    rw [←he,map_mul,hr,one_mul]
    exact hf'
  let t := α ⟨a,haS⟩
  have ht : t≠1 := by
    intro he
    apply haR
    apply (source_distinguished_sylow_centralizer_eq d hG T hST hsingle hL hM hTM hunique).le
    refine ⟨haS,?_⟩
    rw [distinguishedZ_of_center_ne_bot d hz]
    intro z hzZ
    have hh := congrArg (fun f:MulAut Z=>(f ⟨z,hzZ⟩:G)) he
    change a*z*a⁻¹=z at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have ht2 : t^2=1 := by
    change (α ⟨a,haS⟩)^2=1
    rw [←map_pow,show (⟨a,haS⟩:S)^2=1 from Subtype.ext ha2,map_one]
  have hc := regular_cyclic_automorphism_normalizer_involution_fixed_card C hreg t ht ht2
    (hn ⟨⟨a,haS⟩,rfl⟩)
  have hi (w:Z) : t (t w)=w := by
    simpa only [pow_two,MulAut.mul_apply,MulAut.one_apply] using
      congrArg (fun f:MulAut Z=>f w) ht2
  rw [distinguishedZ_of_center_ne_bot d hz]
  intro z hzZ hza
  obtain ⟨w,hw⟩ := elementary_fixed_is_coboundary t.toMonoidHom hi hc ⟨z,hzZ⟩
    (Subtype.ext (mul_inv_eq_iff_eq_mul.mpr hza.eq))
  refine ⟨w,w.property,?_⟩
  rw [map_inv] at hw
  exact congrArg Subtype.val hw


/-- The actual fixed points on Z(R) lift through the displacement map. -/
theorem source_noncenterless_inside_center_coboundary
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (a : G) (haS : a∈(d.S : Subgroup d.H).map d.H.subtype) (ha2 : a^2=1)
    (haR : a∉Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R⊓centralizer (R:Set G)
    ∀z∈Z,Commute a z→∃w∈Z,z=w*(a*w*a⁻¹)⁻¹ := by
  intro R Z
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let A := distinguishedZ d
  obtain ⟨x,hxT,hxS,_⟩ := c.outside
  let e := MulAut.conj x⁻¹
  let B := A.map e.toMonoidHom
  obtain ⟨hd,hgen⟩ := source_distinguished_center_pair d hG T hST hsingle hL
    hM hTM hunique hz x hxT hxS
  have hzdata := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hTS : (T:Subgroup G)≤normalizer (S:Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST.le).mp
      (normal_of_index_eq_two (d.lemma_2_4_8_1 hG T hST hsingle hK).1)
  have hTR : (T:Subgroup G)≤normalizer (R:Set G) :=
    (d.lemma_2_4_8_1 hG T hST hsingle hK).2.2
  let b := e.symm a
  have hbdef : b=x*a*x⁻¹ := by
    apply e.injective
    rw [e.apply_symm_apply]
    change a=x⁻¹*(x*a*x⁻¹)*(x⁻¹)⁻¹
    group
  have hbS : b∈S := hbdef ▸ (mem_normalizer_iff.mp (hTS hxT) a).mp haS
  have hb2 : b^2=1 := by change (e.symm a)^2=1;rw [←map_pow,ha2,map_one]
  have hbR : b∉R := by
    intro hb
    have hh := (mem_normalizer_iff.mp ((normalizer (R:Set G)).inv_mem (hTR hxT)) b).mp hb
    change e b∈R at hh
    apply haR
    simpa only [b,MulEquiv.apply_symm_apply] using hh
  have hAB {z:G} (hzB:z∈B) : e.symm z∈A := by
    obtain ⟨w,hw,he⟩ := hzB
    change e w=z at he
    rw [←he,e.symm_apply_apply]
    exact hw
  have hbtrace := source_noncenterless_distinguished_involution_coboundary d hG T hST hsingle hL
    hM hTM hunique c hz b hbS hb2 hbR
  have haA (z:G) (hzA:z∈A) : (MulAut.conj a) z∈A :=
    (mem_normalizer_iff.mp (hzdata.2.2.2 haS) z).mp hzA
  have haB (z:G) (hzB:z∈B) : (MulAut.conj a) z∈B := by
    have hh := (mem_normalizer_iff.mp (hzdata.2.2.2 hbS) (e.symm z)).mp (hAB hzB)
    have he := mem_map_of_mem e.toMonoidHom hh
    change e (b*e.symm z*b⁻¹)∈B at he
    change a*z*a⁻¹∈B
    simpa only [map_mul,map_inv,b,MulEquiv.apply_symm_apply] using he
  have htraceA (z:G) (hzA:z∈A) (hzfix:(MulAut.conj a) z=z) :
      ∃w∈A,z=w*((MulAut.conj a) w)⁻¹ :=
    source_noncenterless_distinguished_involution_coboundary d hG T hST hsingle hL
      hM hTM hunique c hz a haS ha2 haR z hzA (mul_inv_eq_iff_eq_mul.mp hzfix)
  have htraceB (z:G) (hzB:z∈B) (hzfix:(MulAut.conj a) z=z) :
      ∃w∈B,z=w*((MulAut.conj a) w)⁻¹ := by
    have hh : b*e.symm z*b⁻¹=e.symm z := by
      have he := congrArg e.symm hzfix
      change e.symm (a*z*a⁻¹)=e.symm z at he
      simpa only [map_mul,map_inv,b] using he
    obtain ⟨w,hw,hew⟩ := hbtrace (e.symm z) (hAB hzB) (mul_inv_eq_iff_eq_mul.mp hh)
    refine ⟨e w,mem_map_of_mem e.toMonoidHom hw,?_⟩
    have he := congrArg e hew
    change z=e w*(a*e w*a⁻¹)⁻¹
    simpa only [map_mul,map_inv,b,MulEquiv.apply_symm_apply] using he
  have hBR : B≤R := le_sup_right.trans hgen.le |>.trans inf_le_left
  have hc : A≤centralizer (B:Set G) :=
    hzdata.2.2.1.trans inf_le_right |>.trans (centralizer_le hBR)
  have hh := coboundaries_sup_of_disjoint_commuting A B hd hc (MulAut.conj a)
    haA haB htraceA htraceB
  rw [hgen] at hh
  intro z hzZ hza
  exact hh z hzZ (mul_inv_eq_iff_eq_mul.mpr hza.eq)
end CFSG.Quasithin.Chapter2.LinearShadows.Single
