module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.NonnormalModels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.LinearTwo
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.LinearThree

/-!
# Orbit coordinates from the actual source component index

The two-factor quotient and Sylow marking use the index-two component
orbit, with no universal earlier-orbit interface. These are the literal
quotient coordinates needed by the source15.3.27 normality contradiction.
The group calculations specialize the existing OrbitBorel proofs.

Source: Aschbacher–Smith15.3.27(1), printed p.1130.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.ProjectiveSpecialLinearGroup OddBorel EvenBorelResidual
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open RankOneConfiguration
open RankOneConfiguration.Parabolics
open Placement Placement.OrbitBorel
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem orbit_eq_two_conjugates (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hi : (normalizer (c.L : Set G)).relIndex I = 2)
    {t : G} (ht : t ∈ d.S) (htN : t ∉ normalizer (c.L : Set G)) :
    localSpan c.L d.S = c.L ⊔ c.L.map (MulAut.conj t).toMonoidHom := by
  have hSI := (Chapter1.isSylowIn_iff.mp hS).2.1
  let N := (normalizer (c.L : Set G)).subgroupOf I
  have hconj (s : G) (hs : s ∈ d.S) :
      c.L.map (MulAut.conj s).toMonoidHom = c.L ∨
      c.L.map (MulAut.conj s).toMonoidHom = c.L.map (MulAut.conj t).toMonoidHom := by
    by_cases hsN : s ∈ normalizer (c.L : Set G)
    · exact Or.inl (mem_normalizer_iff_map_conj_eq.mp hsN)
    · have he : t⁻¹ * s ∈ normalizer (c.L : Set G) := by
        have ht' : (⟨t, hSI ht⟩ : I)⁻¹ ∉ N := by
          simpa only [inv_mem_iff] using
            (show (⟨t, hSI ht⟩ : I) ∉ N from htN)
        exact (N.mul_mem_iff_of_index_two hi).mpr (iff_of_false ht'
          (show (⟨s, hSI hs⟩ : I) ∉ N from hsN))
      have heq : c.L.map (MulAut.conj (t⁻¹ * s)).toMonoidHom = c.L :=
        mem_normalizer_iff_map_conj_eq.mp he
      right
      calc
        c.L.map (MulAut.conj s).toMonoidHom =
            (c.L.map (MulAut.conj (t⁻¹ * s)).toMonoidHom).map
              (MulAut.conj t).toMonoidHom := by
          rw [map_map]
          congr 1
          ext x
          simp [MulAut.conj_apply, mul_assoc]
        _ = _ := by rw [heq]
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x ⟨s, hs, l, hl, rfl⟩
    have hm : s * l * s⁻¹ ∈ c.L.map (MulAut.conj s).toMonoidHom :=
      mem_map.mpr ⟨l, hl, rfl⟩
    rcases hconj s hs with he | he
    · exact (show c.L ≤ c.L ⊔ c.L.map (MulAut.conj t).toMonoidHom from le_sup_left) (he ▸ hm)
    · exact (show c.L.map (MulAut.conj t).toMonoidHom ≤
          c.L ⊔ c.L.map (MulAut.conj t).toMonoidHom from le_sup_right) (he ▸ hm)
  · refine sup_le (le_conjugateSpanBy _ _) ?_
    rintro x ⟨l, hl, rfl⟩
    exact subset_closure ⟨t, ht, l, hl, rfl⟩

omit [Finite G] in
private theorem conjugate_component {I L : Subgroup G} (hLI : L ≤ I)
    (hL : (L.subgroupOf I).IsCComponent) {t : G} (ht : t ∈ I) :
    (L.map (MulAut.conj t).toMonoidHom).subgroupOf I |>.IsCComponent := by
  have hle : L.map (MulAut.conj t).toMonoidHom ≤ I := by
    rintro x ⟨l, hl, rfl⟩
    exact I.mul_mem (I.mul_mem ht (hLI hl)) (I.inv_mem ht)
  have hc := hL.map_equiv (MulAut.conj (⟨t, ht⟩ : I))
  have he : (L.subgroupOf I).map (MulAut.conj (⟨t, ht⟩ : I)).toMonoidHom =
      (L.map (MulAut.conj t).toMonoidHom).subgroupOf I := by
    apply map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le hle, map_map]
    change (L.subgroupOf I).map ((MulAut.conj t).toMonoidHom.comp I.subtype) = _
    rw [← map_map, map_subgroupOf_eq_of_le hLI]
  exact he ▸ hc

private theorem disjoint_of_simple_commuting {X : Type*} [Group X] (A B : Subgroup X)
    [IsSimpleGroup A] [Group.IsPerfect A] (hc : ⁅A, B⁆ = ⊥) : Disjoint A B := by
  have hz : center A = ⊥ := by
    rcases (inferInstance : (center A).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp hz)).elim
  apply disjoint_def.mpr
  intro x hx hy
  have hcenter : (⟨x, hx⟩ : A) ∈ center A := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (commutator_eq_bot_iff_le_centralizer.mp hc y.property x hy).symm
  rw [hz] at hcenter
  exact congrArg Subtype.val (mem_bot.mp hcenter)

/-- The nonnormal orbit has two actual commuting simple quotient factors. -/
theorem source_linearTwo_orbit_quotient (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hi : (normalizer (c.L : Set G)).relIndex I = 2)
    {F : Type*} [Field F]
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(2,F)) :
    Nonempty ((localSpan c.L d.S ⧸ pCore 2 (localSpan c.L d.S)) ≃*
      (PSL(2,F) × PSL(2,F))) := by
  let L₀ := localSpan c.L d.S
  have hL₀I : L₀ ≤ I := (orbit_normal_and_le d c hS hi).1
  have hLI : c.L ≤ I := component_le c
  have hLL₀ : c.L ≤ L₀ := le_conjugateSpanBy _ _
  have hc := LocalData.thompson_component_in c.le_thompson c.component
  have hSI := (Chapter1.isSylowIn_iff.mp hS).2.1
  obtain ⟨t, ht, htN⟩ : ∃ t ∈ d.S, t ∉ normalizer (c.L : Set G) := by
    by_contra! h
    exact (component_moved_by_sylow d c hS hi).not_ge (conjugateSpanBy_le le_rfl h)
  let C := c.L.map (MulAut.conj t).toMonoidHom
  have hCL₀ : C ≤ L₀ := by
    rintro x ⟨l, hl, rfl⟩
    exact subset_closure ⟨t, ht, l, hl, rfl⟩
  have hgen : L₀ = c.L ⊔ C := orbit_eq_two_conjugates d c hS hi ht htN
  let A := c.L.subgroupOf L₀
  let B := C.subgroupOf L₀
  have hA : A.IsCComponent := hc.subgroupOf_of_le hLL₀ hL₀I
  have hB : B.IsCComponent :=
    (conjugate_component hLI hc (hSI ht)).subgroupOf_of_le hCL₀ hL₀I
  let q := QuotientGroup.mk' (pCore 2 L₀)
  let Abar := A.map q
  let Bbar := B.map q
  let _ := pCore_isNilpotent (p := 2) (G := L₀)
  have hAbar : Abar.IsCComponent := hA.map_quotient _
  have hBbar : Bbar.IsCComponent := hB.map_quotient _
  let a₀ : A ≃* c.L := subgroupOfEquivOfLe hLL₀
  let a : Abar ≃* PSL(2,F) := (cComponentTwoCoreQuotientEquiv hA).symm.trans
    ((QuotientGroup.congr _ _ a₀ (pCore_map_iso 2 a₀)).trans e)
  let ct : c.L ≃* C := equivMapOfInjective c.L (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective
  let b₀ : B ≃* c.L := (subgroupOfEquivOfLe hCL₀).trans ct.symm
  let b : Bbar ≃* PSL(2,F) := (cComponentTwoCoreQuotientEquiv hB).symm.trans
    ((QuotientGroup.congr _ _ b₀ (pCore_map_iso 2 b₀)).trans e)
  let _ := hAbar.perfect
  let _ := hBbar.perfect
  let _ : Group.IsPerfect PSL(2,F) :=
    Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  let _ : IsSimpleGroup PSL(2,F) :=
    MulAction.IwasawaStructure.isSimpleGroup Group.IsPerfect.commutator_eq_top
      PSL2.Iwasawa inferInstance
  let _ : IsSimpleGroup Abar := a.isSimpleGroup
  let _ : IsSimpleGroup Bbar := b.isSimpleGroup
  have hne : Abar ≠ Bbar := by
    intro he
    have heq := hA.eq_of_map_quotient_eq hB (pCore 2 L₀) he
    have hh := congrArg (fun D : Subgroup L₀ => D.map L₀.subtype) heq
    rw [map_subgroupOf_eq_of_le hLL₀, map_subgroupOf_eq_of_le hCL₀] at hh
    exact htN (mem_normalizer_iff_map_conj_eq.mpr hh.symm)
  have hcomm : ⁅Abar, Bbar⁆ = ⊥ :=
    simple_subnormal_commute_of_ne Abar Bbar hAbar.subnormal hBbar.subnormal hne
  have hdisj := disjoint_of_simple_commuting Abar Bbar hcomm
  obtain ⟨m, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting Abar Bbar hdisj
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have htop : Abar ⊔ Bbar = ⊤ := by
    change A.map q ⊔ B.map q = ⊤
    rw [← Subgroup.map_sup]
    have he : A ⊔ B = ⊤ := by
      change c.L.subgroupOf L₀ ⊔ C.subgroupOf L₀ = ⊤
      rw [← subgroupOf_sup hLL₀ hCL₀, ← hgen, subgroupOf_self]
    rw [he]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  let m' := m.trans ((MulEquiv.subgroupCongr htop).trans topEquiv)
  exact ⟨m'.symm.trans (a.prodCongr b)⟩

/-- The actual two-component quotient can be marked at the supplied Sylow
subgroup, giving all four fields required by the linear-two Borel argument. -/
theorem source_linearTwo_orbit_coordinates (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hi : (normalizer (c.L : Set G)).relIndex I = 2)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(2,F)) :
    Nonempty (LinearTwo.Coordinates (localSpan c.L d.S) d.S F) := by
  let L₀ := localSpan c.L d.S
  obtain ⟨a⟩ := source_linearTwo_orbit_quotient d c hS hi e
  let q := QuotientGroup.mk' (pCore 2 L₀)
  let f := a.toMonoidHom.comp q
  obtain ⟨hle, hnormal⟩ := orbit_normal_and_le d c hS hi
  have hSL₀ : Chapter1.IsSylowIn 2 (d.S ⊓ L₀) L₀ :=
    Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hS hle hnormal.isSubnormal
  apply linearTwo_coordinates_of_quotient hSL₀ f (a.surjective.comp (QuotientGroup.mk'_surjective _))
  exact (MonoidHom.ker_comp_of_injective q a.toMonoidHom a.injective).trans
    (QuotientGroup.ker_mk' _)


private theorem pair_span {G : Type*} [Group G] (L S I : Subgroup G)
    (hSI : S ≤ I) (hi : (normalizer (L : Set G)).relIndex I = 2)
    {s : G} (hs : s ∈ S) (hsN : s ∉ normalizer (L : Set G)) :
    L ⊔ L.map (MulAut.conj s).toMonoidHom = localSpan L S ∧
      (L.map (MulAut.conj s).toMonoidHom).map (MulAut.conj s).toMonoidHom = L := by
  let N := (normalizer (L : Set G)).subgroupOf I
  have hform (t : G) (ht : t ∈ I) :
      L.map (MulAut.conj t).toMonoidHom = L ∨
        L.map (MulAut.conj t).toMonoidHom = L.map (MulAut.conj s).toMonoidHom := by
    by_cases htN : t ∈ normalizer (L : Set G)
    · exact Or.inl (mem_normalizer_iff_map_conj_eq.mp htN)
    · right
      have hn : s⁻¹ * t ∈ normalizer (L : Set G) := by
        have hs' : (⟨s, hSI hs⟩ : I)⁻¹ ∉ N := by
          simpa only [inv_mem_iff] using
            (show (⟨s, hSI hs⟩ : I) ∉ N from hsN)
        exact (N.mul_mem_iff_of_index_two hi).mpr (iff_of_false hs' (show (⟨t, ht⟩ : I) ∉ N from htN))
      have he : L.map (MulAut.conj (s⁻¹ * t)).toMonoidHom = L :=
        mem_normalizer_iff_map_conj_eq.mp hn
      have hh : (MulAut.conj s).toMonoidHom.comp
          (MulAut.conj (s⁻¹ * t)).toMonoidHom = (MulAut.conj t).toMonoidHom := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [← hh, ← map_map, he]
  constructor
  · apply le_antisymm
    · apply sup_le (le_conjugateSpanBy L S)
      rintro x ⟨l, hl, rfl⟩
      exact subset_closure ⟨s, hs, l, hl, rfl⟩
    · apply (closure_le _).mpr
      rintro x ⟨t, ht, l, hl, rfl⟩
      have hx : t * l * t⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom :=
        mem_map_of_mem _ hl
      rcases hform t (hSI ht) with he | he
      · exact (show L ≤ L ⊔ L.map (MulAut.conj s).toMonoidHom from le_sup_left) (he ▸ hx)
      · exact (show L.map (MulAut.conj s).toMonoidHom ≤ L ⊔ L.map (MulAut.conj s).toMonoidHom from le_sup_right) (he ▸ hx)
  · have hss : s * s ∈ normalizer (L : Set G) :=
      (N.mul_mem_iff_of_index_two hi).mpr
        (Iff.rfl : (⟨s, hSI hs⟩ : I) ∈ N ↔ (⟨s, hSI hs⟩ : I) ∈ N)
    have hh : (MulAut.conj s).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
        (MulAut.conj (s * s)).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [map_map, hh]
    exact mem_normalizer_iff_map_conj_eq.mp hss

/-- The coordinates are constructed on the actual S-span and the literal Y₊.
Every premise of the two-component quotient calculation is obtained from the
source orbit and Sylow hypotheses. -/
theorem source_linearThree_productCoordinates
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hS : Chapter1.IsSylowIn 2 d.S I)
    (hi : (normalizer (c.L : Set G)).relIndex I = 2)
    (hYH : d.Yplus ≤ localSpan c.L d.S)
    (hSY : d.S ≤ normalizer (d.Yplus : Set G))
    (hm : ClassicalGroup.IsPSL (c.L ⧸ pCore 2 c.L) 3 2) :
    Nonempty (LinearThree.ProductCoordinates (c.L.subgroupOf (localSpan c.L d.S))
      (d.Yplus.subgroupOf (localSpan c.L d.S))) := by
  let H := localSpan c.L d.S
  obtain ⟨hHI, hnH⟩ := orbit_normal_and_le d c hS hi
  have hLH : c.L ≤ H := le_conjugateSpanBy c.L d.S
  have hSI := (Chapter1.isSylowIn_iff.mp hS).2.1
  have hs : ∃ s ∈ d.S, s ∉ normalizer (c.L : Set G) := by
    by_contra! hsn
    exact (component_moved_by_sylow d c hS hi).not_ge (conjugateSpanBy_le le_rfl hsn)
  obtain ⟨s, hs, hsN⟩ := hs
  obtain ⟨hspan, hswap⟩ := pair_span c.L d.S I hSI hi hs hsN
  have hsH : H.map (MulAut.conj s).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy c.L d.S hs)
  let a : MulAut H := ((MulAut.conj s).subgroupMap H).trans (MulEquiv.subgroupCongr hsH)
  have ha : H.subtype.comp a.toMonoidHom = (MulAut.conj s).toMonoidHom.comp H.subtype := by
    ext x
    rfl
  have hmap (D : Subgroup H) : (D.map a.toMonoidHom).map H.subtype =
      (D.map H.subtype).map (MulAut.conj s).toMonoidHom := by
    rw [map_map, ha, ← map_map]
  let B := c.L.subgroupOf H
  have hBL : B.map H.subtype = c.L := map_subgroupOf_eq_of_le hLH
  have hB : B.IsCComponent :=
    (LocalData.thompson_component_in c.le_thompson c.component).subgroupOf_of_le hLH hHI
  have hneq : B ≠ B.map a.toMonoidHom := by
    intro he
    have he' := congrArg (Subgroup.map H.subtype) he
    rw [hmap, hBL] at he'
    exact hsN (mem_normalizer_iff_map_conj_eq.mpr he'.symm)
  have hgen : B ⊔ B.map a.toMonoidHom = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, hmap, hBL, hspan, ← MonoidHom.range_eq_map, range_subtype]
  have hswapB : (B.map a.toMonoidHom).map a.toMonoidHom = B := by
    apply map_injective H.subtype_injective
    rw [hmap, hmap, hBL, hswap]
  have hfixY : (d.Yplus.subgroupOf H).map a.toMonoidHom = d.Yplus.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hmap, map_subgroupOf_eq_of_le hYH]
    exact mem_normalizer_iff_map_conj_eq.mp (hSY hs)
  obtain ⟨T, hT⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hS hHI
    hnH.isSubnormal
  have hTY : (T : Subgroup H) ≤ normalizer (d.Yplus.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hYH]
    intro t ht
    have htS : (t : G) ∈ d.S ⊓ H := hT ▸ mem_map_of_mem H.subtype ht
    exact hSY htS.1
  let eB : B ≃* c.L := subgroupOfEquivOfLe hLH
  have hmB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 2 :=
    hm.of_mulEquiv (QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB))
  exact LinearThree.OrbitCoordinates.of_component_pair B (d.Yplus.subgroupOf H) hB hmB a hneq hgen hswapB hfixY T hTY


end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
