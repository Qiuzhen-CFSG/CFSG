module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalBlockMaximal
public import CFSG.Quasithin.Chapter5.Section03CentralizerGeneric
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Transport

/-!
# The two root planes in the prepared maximal linear row

The actual parabolic comparison identifies each source factor with its affine
plane model and identifies the original S with UT₃(F). Each core is elementary
of order q². Maximal two-locality identifies its ambient normalizer with the
full factor normalizer; escape makes the two cores distinct. The UT₃ calculation
therefore identifies them, in one coordinate system, with the two root planes.

Consequently S is their join, its center is their intersection, and every
noncentral involution has one plane as its centralizer in S. Characteristic two
makes each plane self-centralizing in the original ambient group, giving
C_G(S) = Z(S). The final theorem applies this geometry to the source's local
core alternative in §5.3.7; the containment O₂(C_G(z)) ≤ S remains explicit.

Both orientations and q=4 are retained. These theorems do not identify the
ambient group or construct the full-normalizer PSL₃ extension. In particular,
the centralizer-core containment, exceptional Sylow marking, and completion
recognition remain obligations. The companion WeakClosure module proves weak
closure of the two planes in the ambient Sylow T.
Source: Aschbacher–Smith 5.2.7 and 5.3.1,5–7, printed pp.651,658,660–661
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem affine_core_structure {K : Subgroup G}
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (e : K ≃* Matrix.SL2.Affine F) :
    IsElementaryAbelian 2 (K.pCoreIn 2) ∧ Nat.card (K.pCoreIn 2) = Nat.card F ^ 2 := by
  let a := (ChapterC.SL2Affine.coreEquiv e).trans
    ((pCore 2 K).equivMapOfInjective K.subtype K.subtype_injective)
  have ha : IsElementaryAbelian 2 (K.pCoreIn 2) :=
    IsElementaryAbelian.of_injective a.symm.toMonoidHom a.symm.injective
  refine ⟨ha,?_⟩
  exact (Nat.card_congr a.symm.toEquiv).trans (by
    change Nat.card (Fin 2 → F) = _
    simp only [Nat.card_fun,Nat.card_fin])

private theorem local_sylow_coordinates
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    {K S : Subgroup G} (P : Sylow 2 K)
    (hP : (P : Subgroup K).map K.subtype = S)
    (j : Bool) (a : K ≃* CoveredLocals.localProjective F j) :
    Nonempty (U F ≃* S) := by
  let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
  let c : P ≃* Q := (P : Subgroup K).equivMapOfInjective a.toMonoidHom a.injective
  let b : P ≃* S := ((P : Subgroup K).equivMapOfInjective K.subtype
    K.subtype_injective).trans (MulEquiv.subgroupCongr hP)
  cases j
  · let R := lineLocalSylow F hm hF
    let u : R ≃* unipotent F := subgroupOfEquivOfLe (unipotent_le_lineLocal F)
    exact ⟨(unipotentEquiv F).trans (u.symm.trans ((Q.equiv R).symm.trans (c.symm.trans b)))⟩
  · let R := pointLocalSylow F hm hF
    let u : R ≃* unipotent F := subgroupOfEquivOfLe (unipotent_le_pointLocal F)
    exact ⟨(unipotentEquiv F).trans (u.symm.trans ((Q.equiv R).symm.trans (c.symm.trans b)))⟩

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
include d h hH hp hm hF he

/-- The source cores are elementary root planes of the correct order inside
its literal S, and that same S has UT₃ coordinates. -/
theorem Preparation.linear_core_structure :
    m = n ∧ Nonempty (U F ≃* sourceS L H) ∧
    ∀ i : Fin 2, IsElementaryAbelian 2 ((![L,residual H] i).pCoreIn 2) ∧
      Nat.card ((![L,residual H] i).pCoreIn 2) = Nat.card F ^ 2 ∧
      (![L,residual H] i).pCoreIn 2 ≤ sourceS L H := by
  have hs := d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he
  have hmn := (d.linear_amalgam_blocks h hH.1.1.2 hp F hm hF he).1
  have hcore (i : Fin 2) : (![L,residual H] i).pCoreIn 2 ≤ sourceS L H := by
    obtain ⟨P,hP⟩ := d.sylow i
    rw [inf_eq_left.mpr (hs i)] at hP
    exact (pCoreIn_le_sylow _ P).trans_eq hP
  obtain ⟨P,hP⟩ := d.sylow 0
  change Sylow 2 L at P
  change (P : Subgroup L).map L.subtype = sourceS L H ⊓ L at hP
  rw [inf_eq_left.mpr (show sourceS L H ≤ L from hs 0)] at hP
  refine ⟨hmn,?_,?_⟩
  · rcases he with he | he <;> obtain ⟨e⟩ := he
    · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp F hm hF 0 true e.left).2.1
      exact local_sylow_coordinates hm hF P hP true a
    · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp F hm hF 0 false e.left).2.1
      exact local_sylow_coordinates hm hF P hP false a
  · intro i
    have ha : Nonempty (![L,residual H] i ≃* Matrix.SL2.Affine F) := by
      rcases he with he | he <;> obtain ⟨e⟩ := he <;> fin_cases i
      · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp F hm hF 0 true e.left).2.1
        exact ⟨a.trans (pointLocalEquivAffine F)⟩
      · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp F hm hF 1 false e.right).2.1
        exact ⟨a.trans (lineLocalEquivAffine F)⟩
      · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp F hm hF 0 false e.left).2.1
        exact ⟨a.trans (lineLocalEquivAffine F)⟩
      · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp F hm hF 1 true e.right).2.1
        exact ⟨a.trans (pointLocalEquivAffine F)⟩
    obtain ⟨a⟩ := ha
    exact ⟨(affine_core_structure a).1,(affine_core_structure a).2,hcore i⟩

omit [Finite G] d h hH hp hm hF he in
private theorem core_normalizer_of_maximal {K : Subgroup G}
    (hmax : IsMaximalTwoLocal (normalizer (K : Set G))) (hne : K.pCoreIn 2 ≠ ⊥) :
    normalizer (K.pCoreIn 2 : Set G) = normalizer (K : Set G) := by
  have hn := normalizer_le_normalizer_characteristic_image K (pCore 2 K)
  exact le_antisymm (hmax.2 ⟨K.pCoreIn 2,hne,isPGroup_pCoreIn 2 K,rfl⟩ hn) hn

/-- In the maximal row both root-plane normalizers are exactly the full
source normalizers. In particular the two source root planes are distinct. -/
theorem Preparation.linear_root_normalizers
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G)) :
    normalizer (L.pCoreIn 2 : Set G) = normalizer (L : Set G) ∧
    normalizer ((residual H).pCoreIn 2 : Set G) = normalizer (residual H : Set G) ∧
    L.pCoreIn 2 ≠ (residual H).pCoreIn 2 := by
  have hc := (d.linear_core_structure h hH hp F hm hF he).2.2
  have hne (i : Fin 2) : (![L,residual H] i).pCoreIn 2 ≠ ⊥ := by
    rw [← one_lt_card_iff_ne_bot,(hc i).2.1]
    exact one_lt_pow₀ Finite.one_lt_card (by decide)
  have hTK := hH.1.1.2.trans (le_normalizer_residual H)
  have horbit : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTK) (le_componentOrbit _ _)
  have hk := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hmax).normalizer_maximal
  rw [horbit] at hk
  have hl := core_normalizer_of_maximal h.maximal (hne 0)
  have hr := core_normalizer_of_maximal hk (hne 1)
  refine ⟨hl,hr,?_⟩
  intro hv
  have hh : normalizer (L : Set G) = normalizer (residual H : Set G) := by rw [← hl,← hr,hv]
  exact d.right_outside (hh ▸ (residual H).le_normalizer)

/-- The coordinate planes are the two original source cores, up to their
ordering. Both are transported through one equivalence of the same S. -/
theorem Preparation.linear_root_coordinates
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G)) :
    ∃ e : U F ≃* sourceS L H,
      ((V₁ F).map (markedHom F (sourceS L H) e) = L.pCoreIn 2 ∧
       (V₂ F).map (markedHom F (sourceS L H) e) = (residual H).pCoreIn 2) ∨
      ((V₁ F).map (markedHom F (sourceS L H) e) = (residual H).pCoreIn 2 ∧
       (V₂ F).map (markedHom F (sourceS L H) e) = L.pCoreIn 2) := by
  obtain ⟨_,⟨e⟩,hc⟩ := d.linear_core_structure h hH hp F hm hF he
  have hne := (d.linear_root_normalizers h hH hp F hm hF he hmax).2.2
  have hplanes (i : Fin 2) :
      (![L,residual H] i).pCoreIn 2 = (V₁ F).map (markedHom F (sourceS L H) e) ∨
      (![L,residual H] i).pCoreIn 2 = (V₂ F).map (markedHom F (sourceS L H) e) := by
    let := (hc i).1
    rcases marked_elementary_le_plane F (sourceS L H) e _ (hc i).2.2 with hle | hle
    · exact Or.inl (eq_of_le_of_card_ge hle (by rw [marked_card_plane₁,(hc i).2.1]))
    · exact Or.inr (eq_of_le_of_card_ge hle (by rw [marked_card_plane₂,(hc i).2.1]))
  refine ⟨e,?_⟩
  rcases hplanes 0 with hl | hl <;> rcases hplanes 1 with hr | hr
  · exact (hne (hl.trans hr.symm)).elim
  · exact Or.inl ⟨hl.symm,hr.symm⟩
  · exact Or.inr ⟨hr.symm,hl.symm⟩
  · exact (hne (hl.trans hr.symm)).elim

/-- The literal source center is the intersection of the two root planes;
every noncentral involution has one of those planes as its centralizer in S.
No ambient centralizer containment is part of this statement. -/
theorem Preparation.linear_involution_geometry
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G)) :
    (center (sourceS L H)).map (sourceS L H).subtype =
      L.pCoreIn 2 ⊓ (residual H).pCoreIn 2 ∧
    Nat.card (center (sourceS L H)) = Nat.card F ∧
    IsMulCommutative (sourceS L H ⧸ center (sourceS L H)) ∧
    (∀ x ∈ (center (sourceS L H)).map (sourceS L H).subtype, x ^ 2 = 1) ∧
    ∀ x ∈ sourceS L H, x ^ 2 = 1 →
      x ∉ (center (sourceS L H)).map (sourceS L H).subtype →
      sourceS L H ⊓ centralizer ({x} : Set G) = L.pCoreIn 2 ∨
      sourceS L H ⊓ centralizer ({x} : Set G) = (residual H).pCoreIn 2 := by
  obtain ⟨e,hplanes⟩ := d.linear_root_coordinates h hH hp F hm hF he hmax
  have hz := marked_center F (sourceS L H) e
  have hi : (center (sourceS L H)).map (sourceS L H).subtype =
      L.pCoreIn 2 ⊓ (residual H).pCoreIn 2 := by
    rw [hz,← root_planes_inter,Subgroup.map_inf _ _ _ (markedHom_injective F (sourceS L H) e)]
    rcases hplanes with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · rw [hl,hr]
    · rw [hl,hr,inf_comm]
  refine ⟨hi,?_,marked_quotient_commutative F (sourceS L H) e,?_,?_⟩
  · rw [← card_map_of_injective (f := (sourceS L H).subtype) (sourceS L H).subtype_injective,
      hz,marked_card_center]
  · intro x hx
    exact marked_center_exponent F (sourceS L H) e x (hz ▸ hx)
  · intro x hx hp hz'
    have hc := marked_involution_geometry F (sourceS L H) e x hx hp (hz ▸ hz')
    rcases hplanes with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · simpa only [hl,hr] using hc
    · simpa only [hl,hr,or_comm] using hc

/-- Each root plane is self-centralizing in the entire original group. -/
theorem Preparation.linear_root_centralizers
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G)) :
    centralizer (L.pCoreIn 2 : Set G) = L.pCoreIn 2 ∧
    centralizer ((residual H).pCoreIn 2 : Set G) = (residual H).pCoreIn 2 := by
  have hcomp : ConcreteAmalgamComparison
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) := .linear F m hm hF he
  have hl := d.normalizer_local_conditions h hH hmax rfl
    (d.common_sylow_of_comparison h hH.1.1.2 hp hcomp)
    (d.parabolic_sylow_core_eq_of_comparison h hH.1.1.2 hp hcomp)
  obtain ⟨hnl,hnr,_⟩ := d.linear_root_normalizers h hH hp F hm hF he hmax
  have hc := (d.linear_core_structure h hH hp F hm hF he).2.2
  have finish (K : Subgroup G) (hn : normalizer (K.pCoreIn 2 : Set G) = normalizer (K : Set G))
      (helem : IsElementaryAbelian 2 (K.pCoreIn 2))
      (hchar : normalizer (K : Set G) ∈ Chapter1.He G)
      (hcore : (normalizer (K : Set G)).pCoreIn 2 = K.pCoreIn 2) :
      centralizer (K.pCoreIn 2 : Set G) = K.pCoreIn 2 := by
    have hself : normalizer (K : Set G) ⊓ centralizer (K.pCoreIn 2 : Set G) ≤ K.pCoreIn 2 := by
      rw [← hcore]
      exact hchar
    apply le_antisymm
    · exact (le_inf (by rw [← hn]; exact Subgroup.centralizer_le_normalizer _) le_rfl).trans hself
    · exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  exact ⟨finish L hnl (hc 0).1
      (Chapter1.mem_He_iff.mpr (h.qtke.evenCharacteristic T _ h.maximal h.sylow_normalizes)) hl.twoCore_left,
    finish (residual H) hnr (hc 1).1 (residual_normalizer_mem_He h hH) hl.twoCore_right⟩

/-- The full ambient centralizer of S is precisely its own center. -/
theorem Preparation.linear_sourceS_centralizer
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G)) :
    centralizer (sourceS L H : Set G) = (center (sourceS L H)).map (sourceS L H).subtype := by
  have hc := (d.linear_core_structure h hH hp F hm hF he).2.2
  have hn := d.linear_root_centralizers h hH hp F hm hF he hmax
  have hz := (d.linear_involution_geometry h hH hp F hm hF he hmax).1
  apply le_antisymm
  · rw [hz]
    exact le_inf ((centralizer_le (hc 0).2.2).trans_eq hn.1)
      ((centralizer_le (hc 1).2.2).trans_eq hn.2)
  · rintro x ⟨z,hz,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hy⟩)

/-- The two source planes are exactly the elementary subgroups of S having
order at least q². This supplies the returning-conjugate calculation inside S. -/
theorem Preparation.linear_large_elementary_in_sourceS
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (E : Subgroup G) (hE : IsElementaryAbelian 2 E) (hES : E ≤ sourceS L H)
    (hcard : Nat.card F ^ 2 ≤ Nat.card E) :
    E = L.pCoreIn 2 ∨ E = (residual H).pCoreIn 2 := by
  obtain ⟨e,hplanes⟩ := d.linear_root_coordinates h hH hp F hm hF he hmax
  have hc : E = (V₁ F).map (markedHom F (sourceS L H) e) ∨
      E = (V₂ F).map (markedHom F (sourceS L H) e) := by
    rcases marked_elementary_le_plane F (sourceS L H) e E hES with hle | hle
    · exact Or.inl (eq_of_le_of_card_ge hle (by rw [marked_card_plane₁]; exact hcard))
    · exact Or.inr (eq_of_le_of_card_ge hle (by rw [marked_card_plane₂]; exact hcard))
  rcases hplanes with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · simpa only [hl,hr] using hc
  · simpa only [hl,hr,or_comm] using hc

/-- The maximal elementary planes generate the original S. -/
theorem Preparation.linear_sourceS_eq_sup_cores
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G)) :
    sourceS L H = L.pCoreIn 2 ⊔ (residual H).pCoreIn 2 := by
  obtain ⟨e,hplanes⟩ := d.linear_root_coordinates h hH hp F hm hF he hmax
  have hu : V₁ F ⊔ V₂ F = ⊤ := by
    apply top_unique
    intro a _
    have hx : (⟨a.x,0,a.c⟩ : U F) ∈ V₁ F := (mem_V₁ F _).mpr rfl
    have hy : (⟨0,a.y,0⟩ : U F) ∈ V₂ F := (mem_V₂ F _).mpr rfl
    have hh := (V₁ F ⊔ V₂ F).mul_mem (mem_sup_right hy) (mem_sup_left hx)
    have ha : (⟨0,a.y,0⟩ : U F) * ⟨a.x,0,a.c⟩ = a := by
      apply U.ext <;> simp
    exact ha ▸ hh
  have hg : (V₁ F).map (markedHom F (sourceS L H) e) ⊔
      (V₂ F).map (markedHom F (sourceS L H) e) = sourceS L H := by
    rw [← Subgroup.map_sup,hu,← MonoidHom.range_eq_map,range_markedHom]
  rcases hplanes with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · simpa only [hl,hr] using hg.symm
  · simpa only [hl,hr,sup_comm] using hg.symm

/-- The actual §5.3.7 core alternative. The local core containment R ≤ S
remains explicit; the matrix geometry and self-centralization are proved. -/
theorem Preparation.linear_centralizer_core_alternative
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (z : G) (hz : orderOf z = 2)
    (hzS : z ∈ (center (sourceS L H)).map (sourceS L H).subtype)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ sourceS L H) :
    (center (sourceS L H)).map (sourceS L H).subtype =
      ((omega₁ (center ((centralizer ({z} : Set G)).pCoreIn 2)) (p := 2)).map
        (center ((centralizer ({z} : Set G)).pCoreIn 2)).subtype).map
          ((centralizer ({z} : Set G)).pCoreIn 2).subtype ∨
    (centralizer ({z} : Set G)).pCoreIn 2 = L.pCoreIn 2 ∨
    (centralizer ({z} : Set G)).pCoreIn 2 = (residual H).pCoreIn 2 := by
  have hc := (d.linear_core_structure h hH hp F hm hF he).2.2
  have hgeo := d.linear_involution_geometry h hH hp F hm hF he hmax
  have hZS : (center (sourceS L H)).map (sourceS L H).subtype ≤ sourceS L H := map_subtype_le _
  have hZC : (center (sourceS L H)).map (sourceS L H).subtype ≤
      centralizer (sourceS L H : Set G) := by
    rintro x ⟨a,ha,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨y,hy⟩)
  have hSC : sourceS L H ≤ centralizer ({z} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (hZC hzS x hx)
  have hchar : centralizer ({z} : Set G) ∈ Chapter1.He G :=
    Chapter1.twoLocal_mem_He_of_sylow_le T (h.qtke.evenCharacteristic T)
      (isTwoLocal_involution_centralizer hz) hzT
  let : IsElementaryAbelian 2 (L.pCoreIn 2) := (hc 0).1
  let : IsElementaryAbelian 2 ((residual H).pCoreIn 2) := (hc 1).1
  exact Chapter5.Section03.core_alternative_of_involution_geometry
    (centralizer ({z} : Set G)) ((centralizer ({z} : Set G)).pCoreIn 2)
    (sourceS L H) ((center (sourceS L H)).map (sourceS L H).subtype)
    (L.pCoreIn 2) ((residual H).pCoreIn 2) hR (hZS.trans hSC) hZC
    hgeo.2.2.2.1 hchar ((hc 0).2.2.trans hSC) ((hc 1).2.2.trans hSC)
    inferInstance inferInstance hgeo.2.2.2.2

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
