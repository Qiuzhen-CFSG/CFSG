module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFourEndpointEquality
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCentralizerAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalDisplacement
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.FourOuter
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.FirstPair
public import Theory.SpecificGroups.PSL3Two.NonSolvable

/-!
# The original Sylow action on the binary-four central span

Each original Sylow actor on the A8 carrier is inner and preserves the
same restricted Sylow. The full flag is self-normalizing, so its inner
representative lies in that restricted Sylow and hence in the actual B.
The centralizing remainder fixes the entire original central span W.
Consequently S fixes W intersect H, which lies in the original fixed line.
The kernel C_X(K) is retained throughout.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions BinaryLinear.SylowFlagOvergroups

private theorem sylow_le_component_join_centralizer
    {X : Type*} [Group X] [Finite X]
    (K B : Subgroup X) [K.Normal] (hBK : B ≤ K)
    (S : Sylow 2 X) (hSB : (S : Subgroup X) ≤ normalizer B)
    (T : Sylow 2 K) (hT : (T : Subgroup K)=(S : Subgroup X).subgroupOf K)
    (hTB : (T : Subgroup K) ≤ B.subgroupOf K)
    (a : K ≃* LinearGroup 4) (v : Basis 3)
    (hv : (T.mapSurjective (f := a.toMonoidHom) a.surjective : Subgroup _)=cutStabilizer v Set.univ)
    (hne : (B.subgroupOf K).map a.toMonoidHom ≠ ⊤)
    (hns : ¬ Group.IsSolvable ((B.subgroupOf K).map a.toMonoidHom)) :
    (S : Subgroup X) ≤ B ⊔ centralizer (K : Set X) := by
  let R := (B.subgroupOf K).map a.toMonoidHom
  let U := T.mapSurjective (f := a.toMonoidHom) a.surjective
  let α := componentAction K a
  have hUR : (U : Subgroup (LinearGroup 4)) ≤ normalizer R :=
    (map_mono hTB).trans R.le_normalizer
  have hI : ((S : Subgroup X) ⊓ K).subgroupOf K=(T : Subgroup K) := by
    rw [hT]
    ext x
    exact and_iff_left x.property
  have hnI : (S : Subgroup X) ≤ normalizer ((S : Subgroup X) ⊓ K : Set X) :=
    (le_inf (S : Subgroup X).le_normalizer (by rw [normalizer_eq_top]; exact le_top)).trans
      inf_normalizer_le_normalizer_inf
  have hker : α.ker=centralizer (K : Set X) := by
    change ((MulAut.congr a).toMonoidHom.comp (MulAut.conjNormal : X →* MulAut K)).ker=_
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.congr a).injective,
      MulAut.conjNormal_ker_eq_centralizer]
  intro s hs
  have hUs : (U : Subgroup _).map (α s).toMonoidHom=U := by
    have hh := componentAction_map_subgroup K a ((S : Subgroup X) ⊓ K)
      inf_le_right s (hnI hs)
    change ((T : Subgroup K).map a.toMonoidHom).map (α s).toMonoidHom=(T : Subgroup K).map a.toMonoidHom
    simpa only [hI] using hh
  have hRs : R.map (α s).toMonoidHom=R := componentAction_map_subgroup K a B hBK s (hSB hs)
  obtain ⟨g,hg⟩ := inner_of_preserves_nonsolvable_normalized_four U R hUR hne hns (α s) hUs hRs
  have hgU : g ∈ (U : Subgroup _) := by
    have hh : (U : Subgroup _).map (MulAut.conj g).toMonoidHom=U := by rw [hg]; exact hUs
    have hn : g ∈ normalizer ((U : Subgroup (LinearGroup 4)) : Set (LinearGroup 4)) :=
      mem_normalizer_iff_map_conj_eq.mpr (by simpa only [MulEquiv.toMonoidHom_eq_coe] using hh)
    rw [show (U : Subgroup _)=cutStabilizer v Set.univ from hv,
      normalizer_fullFlag_eq v] at hn
    exact hv.symm ▸ hn
  let k : K := a.symm g
  have hkT : k ∈ (T : Subgroup K) := (Subgroup.mem_map_equiv).mp hgU
  have hkB : (k : X) ∈ B := hTB hkT
  have hak : α (k : X)=MulAut.conj g := by
    change (MulAut.congr a) (MulAut.conjNormal (k : X))=MulAut.conj g
    rw [MulAut.conjNormal_val,MulAut.congr_conj]
    exact congrArg MulAut.conj (a.apply_symm_apply g)
  have hd : (k : X)⁻¹*s ∈ centralizer (K : Set X) := by
    rw [←hker]
    change α ((k : X)⁻¹*s)=1
    rw [map_mul,map_inv,hak,hg,inv_mul_cancel]
  have hh := (B ⊔ centralizer (K : Set X)).mul_mem (mem_sup_left hkB) (mem_sup_right hd)
  simpa only [mul_inv_cancel_left] using hh

variable {G : Type*} [Group G] [Finite G]

/-- The actual full Sylow lies in B times the retained centralizing factor
in the point quotient, and its literal preimage lies in L times that factor. -/
theorem binary_three_point_four_sylow_action
    (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (z : G) (hLS : L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (L.subgroupOf C).map q
    let Z := centralizer (K : Set (C ⧸ pCore 2 C))
    (P : Subgroup C).map q ≤ B ⊔ Z ∧
      d.S ≤ L ⊔ (Z.comap q).map C.subtype := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (L.subgroupOf C).map q
  let Z := centralizer (K : Set (C ⧸ pCore 2 C))
  let S := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))
  let D := B.subgroupOf K
  obtain ⟨T,hT,hTD,a,v,hv,hflags⟩ := binary_three_point_four_endpoint_equality d L b z hLS P hP K hBK hm
  obtain ⟨T₀,hT₀,⟨eJ⟩⟩ := binary_three_point_containing_join_core_quotient d L b z hLS P hP K hBK
  have hTT : T₀=T := Sylow.ext (hT₀.trans hT.symm)
  subst T₀
  have hjoin : D ⊔ (T : Subgroup K)=D := sup_eq_left.mpr hTD
  rw [hjoin] at eJ
  have hnsD : ¬ Group.IsSolvable D := by
    intro hd
    let := hd
    let : Group.IsSolvable (D ⧸ pCore 2 D) := inferInstance
    exact not_isSolvable_psl3_two
      (Group.isSolvable_of_surjective (f := eJ.toMonoidHom) eJ.surjective)
  have hns : ¬ Group.IsSolvable (D.map a.toMonoidHom) := by
    intro hd
    let := hd
    let i := D.equivMapOfInjective a.toMonoidHom a.injective
    exact hnsD (Group.isSolvable_of_isSolvable_injective (f := i.toMonoidHom) i.injective)
  have hne : D.map a.toMonoidHom ≠ ⊤ := by
    intro ht
    rcases hflags with hh | hh
    · have hle : cutStabilizer v ∅ ≤ cutStabilizer v ({0} : Set (Fin 3)) := by rw [←hh,ht]; exact le_top
      exact (cutStabilizer_le_iff v _ _).mp hle (Set.mem_singleton 0)
    · have hle : cutStabilizer v ∅ ≤ cutStabilizer v ({2} : Set (Fin 3)) := by rw [←hh,ht]; exact le_top
      exact (cutStabilizer_le_iff v _ _).mp hle (Set.mem_singleton 2)
  have hLC : L ≤ C := le_sup_left.trans hLS
  have hJL : L ⊔ d.S ≤ normalizer L :=
    (normal_subgroupOf_iff_le_normalizer (show L ≤ L ⊔ d.S from le_sup_left)).mp b.component_normal
  have hPL : (P : Subgroup C) ≤ normalizer (L.subgroupOf C) := by
    rw [←subgroupOf_normalizer_eq hLC]
    intro x hx
    exact hJL (mem_sup_right (hP ▸ mem_map_of_mem C.subtype hx))
  have hSB : (S : Subgroup (C ⧸ pCore 2 C)) ≤ normalizer B :=
    (map_mono hPL).trans ((L.subgroupOf C).le_normalizer_map q)
  have hSZ := sylow_le_component_join_centralizer K B hBK S hSB T hT hTD a v hv hne hns
  refine ⟨hSZ,?_⟩
  have hpre : (B ⊔ Z).comap q = L.subgroupOf C ⊔ Z.comap q := by
    rw [←comap_sup_eq q B Z (QuotientGroup.mk'_surjective _),comap_map_eq]
    rw [sup_assoc,sup_eq_right.mpr (MonoidHom.ker_le_comap q Z)]
  rw [←hP]
  have hp : (P : Subgroup C) ≤ (B ⊔ Z).comap q := map_le_iff_le_comap.mp hSZ
  rw [hpre] at hp
  have hm := map_mono (f := C.subtype) hp
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hLC] at hm
  exact hm


/-- Under the full original source the Sylow fixes the intersection of
its intrinsic four with the actual central span. This intersection lies
in the original fixed line, and has at most two elements. -/
theorem binary_three_source_four_sylow_fixed_intersection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (c.L.subgroupOf C).map q
    let Z := centralizer (K : Set (C ⧸ pCore 2 C))
    let W := conjugateSpanBy ⁅coreCenter c.L,c.L⁆ C
    (P : Subgroup C).map q ≤ B ⊔ Z ∧
      d.S ≤ c.L ⊔ (Z.comap q).map C.subtype ∧
      d.S ≤ centralizer (W ⊓ intrinsicFour c.L : Set G) ∧
      W ⊓ intrinsicFour c.L ≤ fixedPlane (intrinsicFour c.L) d.S ∧
      Nat.card (W ⊓ intrinsicFour c.L : Subgroup G) ≤ 2 := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let Z := centralizer (K : Set (C ⧸ pCore 2 C))
  let D := (Z.comap q).map C.subtype
  let W := conjugateSpanBy ⁅coreCenter c.L,c.L⁆ C
  let H := intrinsicFour c.L
  obtain ⟨hqP,hS⟩ := binary_three_point_four_sylow_action d c.L b z hLS P hP K hBK hm
  have hDW : D ≤ centralizer (W : Set G) := binary_three_source_component_centralizer_fixes_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK
  obtain ⟨common⟩ := t.commonFacts hc
  let earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hLH : c.L ≤ centralizer (H : Set G) := le_centralizer_iff.mp
    ((intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.2.trans inf_le_right)
  have hfix : d.S ≤ centralizer (W ⊓ H : Set G) := hS.trans
    (sup_le (hLH.trans (centralizer_le inf_le_right)) (hDW.trans (centralizer_le inf_le_left)))
  have hline : W ⊓ H ≤ fixedPlane H d.S :=
    le_inf inf_le_right (le_centralizer_iff.mp hfix)
  have hcard : Nat.card (fixedPlane H d.S)=2 := by
    obtain ⟨he,hc⟩ := binary_three_source_original_displacement_eq_fixedLine
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier
    rw [←he]
    exact hc
  exact ⟨hqP,hS,hfix,hline,(card_le_of_le hline).trans_eq hcard⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
