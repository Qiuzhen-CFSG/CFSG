module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentSevenCubic
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentNormalizer
public import Theory.SpecificGroups.AlternatingSeven.CubicFour
public import Theory.GroupTheory.CentralFactorPointCore

/-!
# Excluding the original cubic A₇ component

The simultaneous cubic/involution marking identifies the original R₁ action
image with the Klein four on the first four letters. Its containment follows
from the even cubic centralizer calculation. For the reverse containment,
lift the Klein four in K-star through the central quotient; the original
Sylow normalizes this lift, so it lies in the original point two-core.

The two disjoint cubics then give an order-nine subgroup normalizing this
same four-group. Its full preimage in K-star has order 27. The recovered
normalizer acts on the unchanged R₁-star, contradicting the previously proved
divisibility by nine in that exact normalizer. This removes A₇ from the
original selected-component catalogue while retaining every earlier input.
The M₂₂ exclusion, remaining simple-component cases, abelian point span and
universal natural reduction remain separate obligations.

Source: Aschbacher–Smith, proof of 12.6.26, printed p.832.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- Simultaneously mark the original L₁, V and R₁ images. The four-group
is proved using the original Sylow and the literal star quotient. -/
theorem SourceHypothesis.original_alternatingSevenCover_marked_four
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hm : Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 7)
    (e : (Nonabelian.Setup.star H c.K ⧸ center (Nonabelian.Setup.star H c.K)) ≃*
      alternatingGroup (Fin 7)) :
    ∃ f : H →* Equiv.Perm (Fin 7),
      f.ker = (centralizer (Nonabelian.Setup.star H c.K : Set (Nonabelian.Setup.Hstar H))).comap
        (QuotientGroup.mk' (pCore 2 H)) ∧
      (c.K.subgroupOf H).map f = alternatingGroup (Fin 7) ∧
      ((D.fullSetup hZ T z).R₁.subgroupOf H).map f ≤ alternatingGroup (Fin 7) ∧
      (∀ x : c.localActor, MulAut.centralQuotientAction e (a.action x) =
        MulAut.conjNormal (f (inclusion a.local_le x))) ∧
      (∃ P : Sylow 2 f.range,
        (P : Subgroup f.range).map f.range.subtype = ((T : Subgroup G).subgroupOf H).map f) ∧
      ∃ g : Equiv.Perm (Fin 7),
        (((D.fullSetup hZ T z).L₁.subgroupOf H).map f).map (MulAut.conj g).toMonoidHom =
          zpowers (Equiv.swap 4 5 * Equiv.swap 5 6) ∧
        ((V.subgroupOf H).map f).map (MulAut.conj g).toMonoidHom =
          zpowers (Equiv.swap 0 1 * Equiv.swap 2 3) ∧
        (((D.fullSetup hZ T z).R₁.subgroupOf H).map f).map (MulAut.conj g).toMonoidHom =
          AlternatingSeven.CubicFour.four := by
  classical
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  let A := Nonabelian.Setup.star H E.L₁
  let U := Nonabelian.Setup.star H (T : Subgroup G)
  let R := Nonabelian.Setup.star H E.R₁
  let q := QuotientGroup.mk' (pCore 2 H)
  obtain ⟨f,hker,hK,hR,hmark,hP,g,hgA,hgV⟩ :=
    S.original_alternatingSevenCover_marked_cubic D hZ z hz hTV hTz hbound hH hn c a hm e
  refine ⟨f,hker,hK,hR,hmark,hP,g,hgA,hgV,?_⟩
  have hcore : pCore 2 H ≤ f.ker := by
    rw [hker]
    intro x hx
    change q x ∈ centralizer (B : Set (Nonabelian.Setup.Hstar H))
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  let f₀ : Nonabelian.Setup.Hstar H →* Equiv.Perm (Fin 7) :=
    QuotientGroup.lift (pCore 2 H) f hcore
  let d : Nonabelian.Setup.Hstar H →* Equiv.Perm (Fin 7) :=
    (MulAut.conj g).toMonoidHom.comp f₀
  have hdker : d.ker = centralizer (B : Set (Nonabelian.Setup.Hstar H)) := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective]
    ext x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
    change y ∈ f.ker ↔ _
    rw [hker]
    rfl
  have hmap (J : Subgroup G) :
      (Nonabelian.Setup.star H J).map d = ((J.subgroupOf H).map f).map (MulAut.conj g).toMonoidHom := by
    change (((J.subgroupOf H).map q).map d) = _
    rw [map_map,map_map]
    rfl
  have hAB : A.map d = zpowers AlternatingSeven.CubicFour.cubic := (hmap E.L₁).trans hgA
  have hB : B.map d = alternatingGroup (Fin 7) := by
    rw [hmap c.K,hK]
    exact mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (alternatingGroup (Fin 7) : Set _) from
      le_normalizer_of_normal (mem_top g))
  have hnormB : B.Normal :=
    (S.original_cubicCover_component_normal D hZ z hz hH c (Or.inl hm)).1
  let := hnormB
  have hTn : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) := by
    intro x hx
    exact S.original_module_normalizer_normalizes_residual D hZ z hTV hH
      ⟨hH.1.2 (Or.inr hx),hTV hx⟩
  have hUn : U ≤ normalizer (A : Set (Nonabelian.Setup.Hstar H)) :=
    (map_mono ((comap_mono hTn).trans (E.L₁.le_normalizer_comap H.subtype))).trans
      ((E.L₁.subgroupOf H).le_normalizer_map q)
  have hUm : U.map d ≤ normalizer (zpowers AlternatingSeven.CubicFour.cubic : Set _) := by
    rw [←hAB]
    exact (map_mono hUn).trans (A.le_normalizer_map d)
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  let T₀ : Sylow 2 (Nonabelian.Setup.Hstar H) :=
    (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hT₀ : (T₀ : Subgroup (Nonabelian.Setup.Hstar H)) = U := by
    rw [Sylow.coe_mapSurjective,Sylow.coe_subtype]
    rfl
  have hlow : AlternatingSeven.CubicFour.four ≤ R.map d := by
    rw [show R = (A ⊔ U).pCoreIn 2 from S.original_point_core_star D hZ z hH]
    rw [←hT₀]
    apply central_factor_le_point_core_image d B A (by rw [hdker]; exact inf_le_right) T₀
      AlternatingSeven.CubicFour.four AlternatingSeven.CubicFour.four_two
    · rw [hB]
      exact AlternatingSeven.CubicFour.four_even
    · rw [hAB]
      exact le_normalizer.trans AlternatingSeven.CubicFour.normalizer_cubic_le_normalizer_four
    · rw [hT₀]
      exact hUm.trans AlternatingSeven.CubicFour.normalizer_cubic_le_normalizer_four
  have hupp : R.map d ≤ AlternatingSeven.CubicFour.four := by
    apply AlternatingSeven.CubicFour.two_subgroup_le_four
    · exact ((isPGroup_pCoreIn 2 (E.L₁ ⊔ (T : Subgroup G))).comap_subtype.map q).map d
    · rw [hmap E.R₁]
      exact (map_mono hR).trans_eq (mem_normalizer_iff_map_conj_eq.mp
        (show g ∈ normalizer (alternatingGroup (Fin 7) : Set _) from
          le_normalizer_of_normal (mem_top g)))
    · rw [←hAB]
      exact (map_mono (S.original_alternatingSevenCover_point_core_centralizes
        D hZ z hz hTV hTz hbound hH hn c a hm)).trans
          (map_centralizer_le_centralizer_image _ d)
  exact (hmap E.R₁).symm.trans (le_antisymm hupp hlow)
/-- The original cubic A₇ component is impossible: its marked four-group
normalizer contains an order-27 subgroup, contradicting the original bound. -/
theorem SourceHypothesis.original_not_alternatingSevenCover
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hm : Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 7)
    : False := by
  classical
  have hmcopy := hm
  obtain ⟨_,⟨ec⟩,⟨e⟩⟩ := hmcopy
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  let A := Nonabelian.Setup.star H E.L₁
  let U := Nonabelian.Setup.star H (T : Subgroup G)
  let R := Nonabelian.Setup.star H E.R₁
  let q := QuotientGroup.mk' (pCore 2 H)
  obtain ⟨f,hker,hK,_,_,_,g,hgA,_,hgR⟩ :=
    S.original_alternatingSevenCover_marked_four D hZ z hz hTV hTz hbound hH hn c a hm e
  have hcore : pCore 2 H ≤ f.ker := by
    rw [hker]
    intro x hx
    change q x ∈ centralizer (B : Set (Nonabelian.Setup.Hstar H))
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  let f₀ : Nonabelian.Setup.Hstar H →* Equiv.Perm (Fin 7) :=
    QuotientGroup.lift (pCore 2 H) f hcore
  let d : Nonabelian.Setup.Hstar H →* Equiv.Perm (Fin 7) :=
    (MulAut.conj g).toMonoidHom.comp f₀
  have hdker : d.ker = centralizer (B : Set (Nonabelian.Setup.Hstar H)) := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective]
    ext x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
    change y ∈ f.ker ↔ _
    rw [hker]
    rfl
  have hmap (J : Subgroup G) :
      (Nonabelian.Setup.star H J).map d = ((J.subgroupOf H).map f).map (MulAut.conj g).toMonoidHom := by
    change (((J.subgroupOf H).map q).map d) = _
    rw [map_map,map_map]
    rfl
  have hAB : A.map d = zpowers AlternatingSeven.CubicFour.cubic := (hmap E.L₁).trans hgA
  have hB : B.map d = alternatingGroup (Fin 7) := by
    rw [hmap c.K,hK]
    exact mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (alternatingGroup (Fin 7) : Set _) from
      le_normalizer_of_normal (mem_top g))
  have hnormB : B.Normal :=
    (S.original_cubicCover_component_normal D hZ z hz hH c (Or.inl hm)).1
  let := hnormB
  have hTn : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) := by
    intro x hx
    exact S.original_module_normalizer_normalizes_residual D hZ z hTV hH
      ⟨hH.1.2 (Or.inr hx),hTV hx⟩
  have hUn : U ≤ normalizer (A : Set (Nonabelian.Setup.Hstar H)) :=
    (map_mono ((comap_mono hTn).trans (E.L₁.le_normalizer_comap H.subtype))).trans
      ((E.L₁.subgroupOf H).le_normalizer_map q)
  have hUm : U.map d ≤ normalizer (zpowers AlternatingSeven.CubicFour.cubic : Set _) := by
    rw [←hAB]
    exact (map_mono hUn).trans (A.le_normalizer_map d)
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  let T₀ : Sylow 2 (Nonabelian.Setup.Hstar H) :=
    (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hT₀ : (T₀ : Subgroup (Nonabelian.Setup.Hstar H)) = U := by
    rw [Sylow.coe_mapSurjective,Sylow.coe_subtype]
    rfl
  have hRW : R.map d = AlternatingSeven.CubicFour.four := (hmap E.R₁).trans hgR
  obtain ⟨X,hXB,hXR,hX,hXN⟩ := central_factor_point_core_lift d B A
    (by rw [hdker]; exact inf_le_right) T₀ AlternatingSeven.CubicFour.four
    AlternatingSeven.CubicFour.four_two
    (by rw [hB]; exact AlternatingSeven.CubicFour.four_even)
    (by rw [hAB]; exact le_normalizer.trans AlternatingSeven.CubicFour.normalizer_cubic_le_normalizer_four)
    (by rw [hT₀]; exact hUm.trans AlternatingSeven.CubicFour.normalizer_cubic_le_normalizer_four)
  have hXR' : X ≤ R := by
    rw [show R = (A ⊔ U).pCoreIn 2 from S.original_point_core_star D hZ z hH,←hT₀]
    exact hXR
  have hN := normalizer_le_of_centralizer_kernel_lift d B R X
    AlternatingSeven.CubicFour.four hdker.le hXR' hX hRW hXN
  let P := B ⊓ AlternatingSeven.CubicFour.nine.comap d
  have hPN : P ≤ B ⊓ normalizer (R : Set (Nonabelian.Setup.Hstar H)) :=
    le_inf inf_le_left ((inf_le_inf_left B (comap_mono
      AlternatingSeven.CubicFour.nine_normalizes_four)).trans hN)
  have hcard : Nat.card P = 27 := by
    rw [centralizer_kernel_preimage_card d B AlternatingSeven.CubicFour.nine hdker
      (by rw [hB]; exact AlternatingSeven.CubicFour.nine_even),
      AlternatingSeven.CubicFour.nine_card]
    have hc : Nat.card (center B) = 3 := by rw [Nat.card_congr ec.toEquiv]; simp
    rw [hc]
  let N := B ⊓ normalizer (R : Set (Nonabelian.Setup.Hstar H))
  have hp : IsPGroup 3 P := IsPGroup.of_card (n := 3) hcard
  obtain ⟨Q,hQ⟩ := (hp.comap_subtype (K := N)).exists_le_sylow
  have hd := card_dvd_of_le hQ
  change Nat.card (P.subgroupOf N) ∣ Nat.card Q at hd
  rw [Nat.card_congr (subgroupOfEquivOfLe hPN).toEquiv,hcard] at hd
  have hbound := S.original_component_pointNormalizer_star_sylow_card D hZ z hz hTV hTz hH c Q
  have hh := hd.trans hbound
  norm_num at hh

/-- After excluding the cubic A₇ row, the only nonsimple selected
component still possible is the cubic M₂₂ cover. Earlier geometry remains explicit. -/
theorem SourceHypothesis.original_selectedComponent_simple_or_mathieu_cover
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking) :
    let B := Nonabelian.Setup.star H c.K
    IsSimpleGroup B ∨
      (Nonempty (center B ≃* Multiplicative (ZMod 3)) ∧
        Chapter1.Section02.LocalModels.IsM22Cover B ∧
        Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁ ≤ B ∧
        a.action.range = MulAut.innerSubgroup B ∧
        B.Normal ∧ H ≤ normalizer (c.K : Set G)) := by
  rcases S.original_selectedComponent_simple_or_normal_internal_cover D hZ z hz hTV hTz
    hbound hns hH hn c a with hs|⟨hc,hm,hA,ha,hBn,hKn⟩
  · exact Or.inl hs
  · rcases hm with hm|hm
    · exact (S.original_not_alternatingSevenCover D hZ z hz hTV hTz hbound hH hn c a hm).elim
    · exact Or.inr ⟨hc,hm,hA,ha,hBn,hKn⟩

end CFSG.Quasithin.Chapter12.Section06
