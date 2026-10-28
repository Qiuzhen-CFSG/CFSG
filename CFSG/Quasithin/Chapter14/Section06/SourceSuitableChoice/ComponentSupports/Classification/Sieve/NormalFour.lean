module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.LinearTwo
public import CFSG.Quasithin.Chapter14.Section02.NormalF11
public import Theory.SpecificGroups.SL2.BorelJoin
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.Alternating.FiveComponentExtension

/-!
# The minimal parabolic and marked five-point action at field four

The component Borel lifts from K/O₂(K) into M because its omitted kernel
lies in the original Sylow T. For a relatively normal PSL₂(4) component,
every proper overgroup of T in KT lies in this Borel times T. Thus KT is
an actual member of HStar. Perfectness identifies its two-residual with
the original K, and the earlier normal-Bender construction supplies all
six F.1.1 clauses and both literal Borel identities. The prescribed A₅
component marking extends to a five-point action of KT with kernel O₂(KT),
giving actual A₅/S₅ isomorphisms for its full two-core quotient. The unique
maximal Sylow overgroup identifies the original M intersection KT with a
point stabilizer in that same action; its relative index is five.

These results construct inputs to the printed minimal-parabolic argument;
they do not assert its missing ambient recognition or exclude PSL₂(4).
That exclusion, the A₆ support marking and suitable-vector assembly remain
with qt-e-suitable-component-supports. Original 14.6.18 remains the explicit
input supplied by qt-e-14625-source.
Source: Aschbacher--Smith 14.3.6(1), 14.6.20 and F.1.1,
printed pp.991,1037,259.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Lift the Borel placement to the original component, retaining its two-core. -/
theorem source_component_sylow_normalizer_le
    (T : Sylow 2 G) (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOver G (T : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤ M := by
  obtain ⟨P,hP⟩ := source_component_sylow T H K hH.2 hKH hK
  let q := QuotientGroup.mk' (pCore 2 K)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : q.ker ≤ M.subgroupOf K := by
    rw [QuotientGroup.ker_mk']
    exact (pCore_isPGroup.le_sylow_of_normal P).trans
      (hP ▸ subgroupOf_mono K hTM)
  have hb := source_component_sylow_normalizer_le_image T M hsolv H hH K hKH hK
    (MulEquiv.refl (K ⧸ pCore 2 K)) P hP
  change normalizer (((P : Subgroup K).map q) : Set (K ⧸ pCore 2 K)) ≤
    (M.subgroupOf K).map q at hb
  rw [←P.normalizer_map_surjective q hq] at hb
  have hh := map_le_iff_le_comap.mp hb
  rw [comap_map_eq_self hk] at hh
  apply map_le_iff_le_comap.mpr
  change normalizer ((T : Subgroup G).subgroupOf K : Set K) ≤ M.subgroupOf K
  change normalizer ((P : Subgroup K) : Set K) ≤ M.subgroupOf K at hh
  rwa [hP] at hh

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv

/-- The remaining normal field-four component gives an actual minimal outside subgroup. -/
theorem source_normal_four_join_minimal
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    K ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) M := by
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hH.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn)
  have hspan : conjugateSpanBy K (T : Subgroup G) = K :=
    le_antisymm (conjugateSpanBy_le le_rfl hTK) (le_conjugateSpanBy _ _)
  have hout := source_component_orbit_outside hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK
  rw [hspan] at hout
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
    (show Nat.card F = 2 ^ 2 by simpa using hF)
  let a := eF.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hb := source_component_sylow_normalizer_le T M hM.1.2 hsolv H hH.1 K hKH hK
  refine ⟨hout,?_⟩
  intro Y hY hYH
  by_contra hHY
  exact hY.2 ((Matrix.SpecialLinearGroup.proper_overgroup_join_le_borel_sup
    T K hTK q hq hk Y hY.1.2 (lt_of_le_not_ge hYH hHY)).trans (sup_le hb hM.1.2))

/-- The same original component supplies every clause of the normal F.1.1 amalgam. -/
theorem source_normal_four_amalgam
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    let J := K ⊔ (T : Subgroup G)
    let Y := sourceResidual M Mc
    let S₂ := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K)
    J ∈ Chapter3.HStar (T : Subgroup G) M ∧
      (pResidual 2 J).map J.subtype = K ∧
      ChapterF.Source.HypothesisF11 ![K,Y ⊔ S₂] (T : Subgroup G) ∧
      Y = ⁅Y,S₂⁆ ∧ ChapterF.Source.borel K (T : Subgroup G) = M ⊓ K ∧
      ChapterF.Source.borel (Y ⊔ S₂) (T : Subgroup G) = S₂ := by
  dsimp only
  let J := K ⊔ (T : Subgroup G)
  have hKJ : K ≤ J := le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hJH : J ≤ H := sup_le hKH hH.1.2
  have hc : (K.subgroupOf J).IsCComponent := hK.subgroupOf_of_le hKJ hJH
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hH.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn)
  have hnc : (K.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hKJ).mpr
    (sup_le K.le_normalizer hTK)
  let := hnc
  have hgen : K.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup hKJ hTJ]
    exact subgroupOf_self J
  have hres := source_twoResidual_eq_normal_cComponent T J hTJ (K.subgroupOf J) hc hnc hgen
  have hmap : (K.subgroupOf J).map J.subtype = K := map_subgroupOf_eq_of_le hKJ
  have hstar := source_normal_four_join_minimal hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hn hm
  let a := subgroupOfEquivOfLe hKJ
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hq : ChapterF.Source.IsRankOneModel ((K.subgroupOf J) ⧸ pCore 2 (K.subgroupOf J)) :=
    .linear 2 (by decide) (by simpa using hm.of_mulEquiv aq)
  have hF := Section02.source_normal_bender_hypothesis_F_1_1
    hG T hempty hM hunique hmany hcard e J hstar (K.subgroupOf J) hgen hres hq
  refine ⟨hstar,?_,?_⟩
  · rw [hres,hmap]
  · simpa only [hmap,inf_eq_left.mpr hTK] using And.intro hF.1 hF.2.2

/-- At the remaining endpoint the full two-core quotient acts faithfully on
five points, compatibly with the original component and the genuine F.1.1 pair. -/
theorem source_normal_four_marked_amalgam
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    let J := K ⊔ (T : Subgroup G)
    let Y := sourceResidual M Mc
    let S₂ := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K)
    ∃ (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
      (f : J →* Equiv.Perm (Fin 5)),
      f.ker = pCore 2 J ∧
      (f.range = alternatingGroup (Fin 5) ∨ f.range = ⊤) ∧
      (∀ k : K, f ⟨k,(show K ≤ J from le_sup_left) k.property⟩ =
        eK (QuotientGroup.mk' (pCore 2 K) k)) ∧
      J ∈ Chapter3.HStar (T : Subgroup G) M ∧
      (pResidual 2 J).map J.subtype = K ∧
      ChapterF.Source.HypothesisF11 ![K,Y ⊔ S₂] (T : Subgroup G) ∧
      Y = ⁅Y,S₂⁆ ∧ ChapterF.Source.borel K (T : Subgroup G) = M ⊓ K ∧
      ChapterF.Source.borel (Y ⊔ S₂) (T : Subgroup G) = S₂ := by
  dsimp only
  let J := K ⊔ (T : Subgroup G)
  have hKJ : K ≤ J := le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hJH : J ≤ H := sup_le hKH hH.1.2
  have hc : (K.subgroupOf J).IsCComponent := hK.subgroupOf_of_le hKJ hJH
  let : (K.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hKJ).mpr
    (hJH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn))
  have hgen : K.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup hKJ hTJ]
    exact subgroupOf_self J
  obtain ⟨F,_,_,hF,⟨aF⟩⟩ := hm
  obtain ⟨bF⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let eK := aF.trans bF
  let a := subgroupOfEquivOfLe hKJ
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  obtain ⟨f,hker,hr,hf⟩ := Theory.SpecificGroups.Alternating.FiveExtensionAction.cComponent_action
    (K.subgroupOf J) ((T : Subgroup G).subgroupOf J) hc T.isPGroup'.comap_subtype hgen (aq.trans eK)
  refine ⟨eK,f,hker,hr,?_,?_⟩
  · intro k
    exact hf ⟨⟨k,hKJ k.property⟩,k.property⟩
  · exact source_normal_four_amalgam hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK hn ⟨F,inferInstance,inferInstance,hF,⟨aF⟩⟩

/-- The original field-four endpoint has precisely A₅ or S₅ as its full
KT two-core quotient. The isomorphisms are constructed from its marked action. -/
theorem source_normal_four_join_models
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    let J := K ⊔ (T : Subgroup G)
    Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨eK,f,hker,hr,_⟩ := source_normal_four_marked_amalgam
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn hm
  let a := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange f)
  rcases hr with hr | hr
  · exact Or.inl ⟨a.trans (MulEquiv.subgroupCongr hr)⟩
  · exact Or.inr ⟨a.trans ((MulEquiv.subgroupCongr hr).trans Subgroup.topEquiv)⟩

/-- The original overlap is exactly a point stabilizer in the compatible
five-point action, with its actual relative index equal to five. -/
theorem source_normal_four_point_overlap
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    let J := K ⊔ (T : Subgroup G)
    ∃ (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
      (f : J →* Equiv.Perm (Fin 5)) (i : Fin 5),
      f.ker = pCore 2 J ∧
      (f.range = alternatingGroup (Fin 5) ∨ f.range = ⊤) ∧
      (∀ k : K, f ⟨k,(show K ≤ J from le_sup_left) k.property⟩ =
        eK (QuotientGroup.mk' (pCore 2 K) k)) ∧
      M.subgroupOf J = (MulAction.stabilizer (Equiv.Perm (Fin 5)) i).comap f ∧
      (M ⊓ J).relIndex J = 5 := by
  dsimp only
  let J := K ⊔ (T : Subgroup G)
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  obtain ⟨eK,f,hker,hr,hf,hstar,_⟩ := source_normal_four_marked_amalgam
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn hm
  have hA : alternatingGroup (Fin 5) ≤ f.range := by
    rcases hr with h | h
    · exact h ▸ le_rfl
    · exact h ▸ le_top
  have hB : M.subgroupOf J ≠ ⊤ := by
    intro he
    exact hstar.1.2 (subgroupOf_eq_top.mp he)
  have hmax (D : Subgroup J) (hD : (T : Subgroup G).subgroupOf J ≤ D)
      (hne : D ≠ ⊤) : D ≤ M.subgroupOf J := by
    apply map_le_iff_le_comap.mp
    apply Chapter3.HStar.proper_overgroup_le T hstar
    · rw [←map_subgroupOf_eq_of_le hTJ]
      exact map_mono hD
    · have hh := (map_lt_map_iff_of_injective J.subtype_injective).mpr
        (lt_top_iff_ne_top.mpr hne)
      simpa only [←MonoidHom.range_eq_map,range_subtype] using hh
  obtain ⟨i,hi,hindex⟩ := Theory.SpecificGroups.Alternating.FiveExtensionAction.point_stabilizer_of_unique_maximal
    f hA ((T : Subgroup G).subgroupOf J) (M.subgroupOf J) T.isPGroup'.comap_subtype hB hmax
  refine ⟨eK,f,i,hker,hr,hf,hi,?_⟩
  simpa only [relIndex,inf_subgroupOf_right] using hindex

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
