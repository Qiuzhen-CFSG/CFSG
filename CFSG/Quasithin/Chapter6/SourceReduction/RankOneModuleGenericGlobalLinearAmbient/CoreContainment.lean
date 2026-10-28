module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.CoreDisplacement
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.TorusControl

/-!
# Centralizer core containment outside field four

The original common-Borel comparison marks the actual S and Z(S). Its
diagonal torus centralizes Z(S) and acts on the two simple roots by cubes.
Every element of R = O₂(C_G(z)), for z central in T, has unipotent
displacements on this torus. The intrinsic UT₃ calculation therefore makes
R centralize Z(S) when q>4, giving R ≤ C_T(Z(S)) = S.

The proved core alternatives now give C_G(z) ≤ N_G(L) ∩ N_G(O²(H)).
Central-line fusion extends this to every involution on Z(S), whose core
is exactly S. Equality of these cores proves that distinct ambient
conjugates of Z(S) are disjoint. The original exponent, field, whole Borel,
and both comparison orientations are retained. Field four, compatible
full-normalizer realization and ambient recognition remain separate.
Source: Aschbacher–Smith §5.3.7 and F.4.34, printed pp.660 and 290
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
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
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3Even.UnipotentGeometry Matrix.PSL3.LinearAmbientGeometry


omit hmax in
/-- The original whole Borel marks the same unipotent subgroup and central line. -/
theorem Preparation.linear_exists_borel_coordinates :
    ∃ f : borel F →* G, Function.Injective f ∧
      f.range = ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) ∧
      (f.comp (borelUnipotent F)).range = sourceS L H ∧
      (Z F).map (f.comp (borelUnipotent F)) = centerIn (sourceS L H) := by
  let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
  let S := sourceS L H
  have hs := d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he
  have hf := d.hypothesisF11 h hH.1.1.2
  have hCS : C ≤ normalizer (S : Set G) := by
    have hh := hf.commonBorel_normalizes_localSylow 0
    change C ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) at hh
    rwa [inf_eq_left.mpr (show S ≤ L from hs 0)] at hh
  have hcore : C.pCoreIn 2 = S := by
    obtain ⟨P,hP⟩ := hf.sylow_commonBorel
    apply le_antisymm ((pCoreIn_le_sylow C P).trans_eq hP)
    exact le_pCoreIn_of_normalizes hf.S_isP le_sup_right hCS
  have hab : Nonempty (C ≃* borel F) := by
    have hh := ChapterF.Source.lemma_F_1_3_6 hf
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · exact ⟨(MulEquiv.subgroupCongr hh.symm).trans e.middle⟩
    · exact ⟨(MulEquiv.subgroupCongr hh.symm).trans e.middle⟩
  obtain ⟨b⟩ := hab
  let f : borel F →* G := C.subtype.comp b.symm.toMonoidHom
  have hfi : Function.Injective f := C.subtype_injective.comp b.symm.injective
  have hfr : f.range = C := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr b.symm.surjective,←MonoidHom.range_eq_map,range_subtype]
  have hjr : (f.comp (borelUnipotent F)).range = S := by
    rw [MonoidHom.range_comp,borelUnipotent_range,←BorelQuotient.twoCore_eq F hF]
    change (pCore 2 (borel F)).map (C.subtype.comp b.symm.toMonoidHom) = S
    rw [←map_map,pCore_map_iso]
    exact hcore
  let j := f.comp (borelUnipotent F)
  have hji : Function.Injective j := hfi.comp (borelUnipotent_injective F)
  let e : U F ≃* S := (MonoidHom.ofInjective hji).trans
    (MulEquiv.subgroupCongr hjr)
  have hj : markedHom F S e = j := by ext u; rfl
  refine ⟨f,hfi,hfr,hjr,?_⟩
  change (Z F).map j = centerIn S
  rw [←hj,←marked_center,←centerIn_eq_map_center]

/-- For q>4 the actual centralizer core lies in S, including even degrees. -/
theorem Preparation.linear_centralizer_core_le_of_large
    (hn : 2 < n) (z : G) (hz : z ∈ centerIn (sourceS L H))
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    (centralizer ({z} : Set G)).pCoreIn 2 ≤ sourceS L H := by
  have hq : 4 < Nat.card F := by
    rw [hF,(d.linear_core_structure h hH hp F hm hF he).1]
    exact Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) hn
  obtain ⟨f,hfi,_,hjr,hjZ⟩ := d.linear_exists_borel_coordinates h hH hp F hm hF he
  let j := f.comp (borelUnipotent F)
  have hji : Function.Injective j := hfi.comp (borelUnipotent_injective F)
  have hTS : (T : Subgroup G) ≤ normalizer (sourceS L H : Set G) := by
    have hs := d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he
    have hS : sourceS L H = (T : Subgroup G) ⊓ L := by
      rw [←d.left_intersection,inf_eq_left.mpr (show sourceS L H ≤ L from hs 0)]
    rw [hS]
    exact (le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans
      inf_normalizer_le_normalizer_inf
  have hN := d.linear_root_normalizers h hH hp F hm hF he hmax
  have hnplane (E : Subgroup (U F)) (hE : IsElementaryAbelian 2 E)
      (hc : Nat.card E = Nat.card F^2) :
      (T : Subgroup G) ≤ normalizer (E.map j : Set G) := by
    have hES : E.map j ≤ sourceS L H := (map_le_range j E).trans_eq hjr
    have hcard : Nat.card F^2 ≤ Nat.card (E.map j) := by
      rw [card_map_of_injective hji,hc]
    rcases d.linear_large_elementary_in_sourceS h hH hp F hm hF he hmax
      (E.map j) (hE.map j) hES hcard with hE | hE
    · rw [hE,hN.1]
      exact h.sylow_normalizes
    · rw [hE,hN.2.1]
      exact hH.1.1.2.trans (le_normalizer_residual H)
  have hn₁ := hnplane (V₁ F) inferInstance (card_V₁ F)
  have hn₂ := hnplane (V₂ F) inferInstance (card_V₂ F)
  obtain ⟨hRT,hd⟩ := d.linear_centralizer_core_displacement h hH hp F hm hF he hmax z hz hzT
  intro r hr
  have hrT := hRT hr
  have hrc : r ∈ centralizer (centerIn (sourceS L H) : Set G) := by
    rw [←hjZ]
    apply centralizes_center_of_torus_displacement F hq f hfi r
    · rw [hjr]
      exact hTS hrT
    · exact hn₁ hrT
    · exact hn₂ hrT
    · obtain ⟨k,hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp T.isPGroup') ⟨r,hrT⟩
      exact ⟨k,congrArg Subtype.val hk⟩
    · intro t
      rw [hjr]
      apply hd
      apply commutator_mem_commutator hr
      rw [←hjZ]
      exact centralTorus_centralizes F f t
  have hh : r ∈ (T : Subgroup G) ⊓ centralizer (centerIn (sourceS L H) : Set G) := ⟨hrT,hrc⟩
  rwa [d.linear_sylow_center_centralizer h hH hp F hm hF he hmax] at hh

/-- Source §5.3.7 for a Sylow-central involution, with no core premise, at q>4. -/
theorem Preparation.linear_centralizer_le_inter_of_large_central
    (hn : 2 < n) (z : G) (hz2 : orderOf z = 2)
    (hz : z ∈ centerIn (sourceS L H))
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    centralizer ({z} : Set G) ≤
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
  d.linear_centralizer_le_inter_of_core_le h hH hp F hm hF he hmax z hz2 hz hzT
    (d.linear_centralizer_core_le_of_large h hH hp F hm hF he hmax hn z hz hzT)

/-- Every central-line involution satisfies the source intersection bound at q>4. -/
theorem Preparation.linear_centralizer_le_inter_of_large
    (hn : 2 < n) (z : G) (hz2 : orderOf z = 2)
    (hz : z ∈ centerIn (sourceS L H)) :
    centralizer ({z} : Set G) ≤
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  obtain ⟨w,hw,hw2,hwT⟩ := d.linear_exists_sylow_central_involution h hH hp F hm hF he hmax
  have hw1 : w ≠ 1 := by intro hh; simp [hh] at hw2
  have hz1 : z ≠ 1 := by intro hh; simp [hh] at hz2
  obtain ⟨g,hg,hgw⟩ := d.linear_center_transitive h hH hp F hm hF he hmax w z hw hz hw1 hz1
  have hcw := d.linear_centralizer_le_inter_of_large_central h hH hp F hm hF he hmax hn w hw2 hw hwT
  let M := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  intro x hx
  have hc : g⁻¹*x*g ∈ centralizer ({w} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hh := mem_centralizer_singleton_iff.mp hx
    rw [←hgw] at hh
    calc
      (g⁻¹*x*g)*w = g⁻¹*(x*(g*w*g⁻¹))*g := by group
      _ = g⁻¹*((g*w*g⁻¹)*x)*g := by rw [hh]
      _ = w*(g⁻¹*x*g) := by group
  have hm : g*(g⁻¹*x*g)*g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg (hcw hc)) (M.inv_mem hg)
  rwa [show g*(g⁻¹*x*g)*g⁻¹ = x from by group] at hm


/-- Every involution on the original central line has precisely the original S
as its centralizer two-core, for q>4. -/
theorem Preparation.linear_centralizer_core_eq_of_large
    (hn : 2 < n) (z : G) (hz2 : orderOf z = 2)
    (hz : z ∈ centerIn (sourceS L H)) :
    (centralizer ({z} : Set G)).pCoreIn 2 = sourceS L H := by
  obtain ⟨w,hw,hw2,hwT⟩ := d.linear_exists_sylow_central_involution h hH hp F hm hF he hmax
  have hw1 : w ≠ 1 := by intro hh; simp [hh] at hw2
  have hz1 : z ≠ 1 := by intro hh; simp [hh] at hz2
  obtain ⟨g,hg,hgw⟩ := d.linear_center_transitive h hH hp F hm hF he hmax w z hw hz hw1 hz1
  have hcw := d.linear_centralizer_le_inter_of_large_central h hH hp F hm hF he hmax hn w hw2 hw hwT
  have hCwS : centralizer ({w} : Set G) ≤ normalizer (sourceS L H : Set G) := by
    rw [←d.linear_factor_centralizer h hH hp F hm hF he hmax 0 w hw hw1]
    exact (le_inf (hcw.trans inf_le_left) (centralizer ({w} : Set G)).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hcore : (centralizer ({w} : Set G)).pCoreIn 2 = sourceS L H := by
    apply le_antisymm (d.linear_centralizer_core_le_of_large h hH hp F hm hF he hmax hn w hw hwT)
    apply le_pCoreIn_of_normalizes
    · exact T.isPGroup'.to_le (sourceS_le_sylow h.sylow_normalizes hH.1.1.2)
    · exact fun x hx => mem_centralizer_singleton_iff.mpr (hw.2 x hx)
    · exact hCwS
  have hcmap : (centralizer ({w} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({z} : Set G) := by
    rw [Theory.GroupTheory.map_centralizer_equiv,Set.image_singleton]
    exact congrArg (fun t : G => centralizer ({t} : Set G)) hgw
  have hSmap : (sourceS L H).map (MulAut.conj g).toMonoidHom = sourceS L H := by
    apply mem_normalizer_iff_map_conj_eq.mp
    have hh : g ∈ normalizer (centerIn (sourceS L H) : Set G) := by
      rwa [d.linear_center_normalizer h hH hp F hm hF he hmax]
    rw [←d.linear_center_centralizer_core h hH hp F hm hF he hmax]
    exact normalizer_le_normalizer_characteristic_image _ (pCore 2 _)
      (normalizer_le_normalizer_centralizer _ hh)
  calc
    (centralizer ({z} : Set G)).pCoreIn 2 =
        ((centralizer ({w} : Set G)).pCoreIn 2).map (MulAut.conj g).toMonoidHom := by
      rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,hcmap]
    _ = sourceS L H := by rw [hcore,hSmap]

/-- Distinct ambient conjugates of the central line are disjoint at q>4. -/
theorem Preparation.linear_center_TI_of_large (hn : 2 < n) (g : G) :
    (centerIn (sourceS L H)).map (MulAut.conj g).toMonoidHom = centerIn (sourceS L H) ∨
      Disjoint (centerIn (sourceS L H)) ((centerIn (sourceS L H)).map (MulAut.conj g).toMonoidHom) := by
  let Z := centerIn (sourceS L H)
  by_cases hd : Disjoint Z (Z.map (MulAut.conj g).toMonoidHom)
  · exact Or.inr hd
  left
  have hne : Z ⊓ Z.map (MulAut.conj g).toMonoidHom ≠ ⊥ := fun hh => hd (disjoint_iff.mpr hh)
  obtain ⟨x,hx1⟩ := ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨y,hy,hgy⟩ := x.property.2
  have hxne : (x:G) ≠ 1 := fun hh => hx1 (Subtype.ext hh)
  have hyne : y ≠ 1 := by intro hh; simp [hh] at hgy; exact hxne hgy.symm
  have hexp := (d.linear_involution_geometry h hH hp F hm hF he hmax).2.2.2.1
  have hx2 : orderOf (x:G) = 2 := orderOf_eq_prime
    (hexp x (by rw [←centerIn_eq_map_center]; exact x.property.1)) hxne
  have hy2 : orderOf y = 2 := orderOf_eq_prime
    (hexp y (by rw [←centerIn_eq_map_center]; exact hy)) hyne
  have hcx := d.linear_centralizer_core_eq_of_large h hH hp F hm hF he hmax hn x hx2 x.property.1
  have hcy := d.linear_centralizer_core_eq_of_large h hH hp F hm hF he hmax hn y hy2 hy
  have hcmap : (centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({(x:G)} : Set G) := by
    rw [Theory.GroupTheory.map_centralizer_equiv,Set.image_singleton]
    exact congrArg (fun t : G => centralizer ({t} : Set G)) hgy
  have hs : (sourceS L H).map (MulAut.conj g).toMonoidHom = sourceS L H := by
    calc
      _ = ((centralizer ({y} : Set G)).pCoreIn 2).map (MulAut.conj g).toMonoidHom :=
        congrArg (fun P : Subgroup G => P.map (MulAut.conj g).toMonoidHom) hcy.symm
      _ = (centralizer ({(x:G)} : Set G)).pCoreIn 2 := by
        rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,hcmap]
      _ = sourceS L H := hcx
  rw [centerIn_map_equiv,hs]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
