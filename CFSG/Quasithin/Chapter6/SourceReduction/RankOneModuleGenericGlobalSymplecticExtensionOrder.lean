module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticMaximal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Centralizers
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRootFusion
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Lattice
public import Theory.SpecificGroups.SymplecticFour.RootTori
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.Parabolics

/-!
# Ambient local inputs for the prepared symplectic source row

The root torus is transitive on the nonidentity point-local center. The
exceptional graph automorphism carries the plane parabolic to the point
parabolic, and solvable residuals carry their whole local factors with it.
Transport through the actual source endpoint maps therefore gives both
center orbits, in either orientation of the pure amalgam comparison.

Original uniqueness over L bounds its central involution centralizers.
For K = O²(H), a central involution of the original Sylow is found in Z(K);
the transported center orbit then bounds every root-involution centralizer.
Uniqueness also determines both full parabolic core-center normalizers.
The full middle contains the original Sylow, hence has odd ambient index,
and original nonabelian simplicity gives two-perfectness.

The same compatible middle and endpoint maps split Z(S) into the two
local centers and the Sylow squares. The nonidentity squares form an odd
Cartan orbit. Its fixed point under the original T, and the corresponding
root-center fixed points, put every central involution in a conjugate Sylow
center. Original even characteristic then gives characteristic two for its
full ambient centralizer. The root orbits and centralizer bounds also give
both elementary TI centers and their exact full normalizers.

Thus all ambient clauses (a)–(e) of F.4.31 and both symplectic conclusions
of F.4.34 hold on the prepared source pair. The simultaneous native
extension, ambient involution fusion and outer transfer, third centralizer
containment and order comparison remain necessary for the extension/order
theorem. No extension, ambient generation or order conclusion is assumed.

Source: Aschbacher–Smith 5.3.1–3, printed pp.658–659; F.4.31–34, p.291
of `refs/quasithin.pdf`. The imported general orbit/centralizer transport
lemmas are independent of their original G₂ application.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Theory.SpecificGroups.SymplecticFour

private theorem point_center_orbit
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2^m) (hm : 1 < m) :
    ∀ x ∈ (center (pointLocal (F := F))).map pointLocal.subtype, x ≠ 1 →
      ∀ y ∈ (center (pointLocal (F := F))).map pointLocal.subtype, y ≠ 1 →
        ∃ g ∈ pointParabolic (F := F), y = g*x*g⁻¹ := by
  rw [PointRadicalAction.center_eq_root hF hm]
  intro x hx hx1 y hy hy1
  obtain ⟨g,hg,_⟩ := RootTori.regular 0 x y hx hy hx1 hy1
  refine ⟨g.val,?_,hg.symm⟩
  have hh := RootTori.torus_le_normalizer 0 g.property
  rwa [RootNormalizerResidual.normalizer_zero_eq] at hh

private def planePointEquiv
    (F : Type) [Field F] [Finite F] [CharP F 2] :
    planeParabolic (F := F) ≃* pointParabolic (F := F) :=
  ((DiagramAutomorphisms.ExceptionalGraph.graphAut (F := F)).subgroupMap planeParabolic).trans
    (MulEquiv.subgroupCongr (DiagramAutomorphisms.ExceptionalGraph.graphAut_map_plane (F := F)))

variable {G : Type*} [Group G] [Finite G]

/-- Each actual parabolic is transitive on the nonidentity center of its
whole local factor. The conjugator is transported through the same endpoint
map as the factor, including when the pure comparison is reversed. -/
theorem Preparation.symplectic_center_orbit
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (i : Fin 2) :
    ∀ x ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype, x ≠ 1 →
      ∀ y ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype, y ≠ 1 →
        ∃ g ∈ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i,
          y = g*x*g⁻¹ := by
  have hmn := (d.symplectic_amalgam_blocks h hTH hp F hm hF he).1
  have hm' : 1 < m := hmn.symm ▸ h.exponent
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i
  have hKP : ![L,residual H] i ≤ P := le_sup_left.trans le_sup_left
  have hres : (![L,residual H] i).subgroupOf P = solvableResidual P := by
    have hr := d.parabolic_residuals h hTH hp i
    rw [←hr]
    exact comap_map_eq_self_of_injective P.subtype_injective _
  have heP : Nonempty (P ≃* pointParabolic (F := F)) := by
    rcases he with he | he
    · obtain ⟨e⟩ := he
      fin_cases i
      · exact ⟨e.left⟩
      · exact ⟨e.right.trans (planePointEquiv F)⟩
    · obtain ⟨e⟩ := he
      fin_cases i
      · exact ⟨e.left.trans (planePointEquiv F)⟩
      · exact ⟨e.right⟩
  obtain ⟨e⟩ := heP
  apply center_orbit_transport (R := pointLocal (F := F)) hKP e
  · rw [hres,←map_map,map_solvableResidual_eq e.toMonoidHom e.surjective]
    exact pointParabolic_solvableResidual_eq hF hm'
  · exact point_center_orbit hF hm'

/-- The two root-involution centralizer bounds in 5.3.3 hold in the original
ambient group. No extra centralizer or orbit hypothesis is required. -/
theorem Preparation.symplectic_central_involution_centralizers
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) :
    ∀ i : Fin 2, ∀ z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype,
      orderOf z = 2 → centralizer ({z} : Set G) ≤ normalizer (![L,residual H] i : Set G) := by
  intro i
  fin_cases i
  · exact d.left_central_involution_centralizer
  have hTK := hH.1.1.2.trans (le_normalizer_residual H)
  have hK := d.symplectic_right_maximal h hH hp F hm hF he
  have hu := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hK).normalizer_unique
  have ho : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTK)
      (le_componentOrbit _ _)
  rw [ho] at hu
  have hc := Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
    (h.qtke.evenCharacteristic T) hK.1
  have hPN : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ≤
      normalizer (residual H : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show residual H ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 from
        le_sup_left.trans le_sup_left)).mp ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic 1)
  exact center_orbit_centralizer_bound hTK hc hPN hu
    (d.symplectic_center_orbit h hH.1.1.2 hp F hm hF he 1)

private theorem core_center_normalizer_of_unique {J K : Subgroup G}
    (hQ : pCore 2 K ≠ ⊥) (hJK : J ≤ normalizer (K : Set G))
    (hu : ∀ M : Subgroup G, IsMaximalTwoLocal M → J ≤ M → M = normalizer (K : Set G)) :
    normalizer ((center (K.pCoreIn 2)).map (K.pCoreIn 2).subtype : Set G) =
      normalizer (K : Set G) := by
  let Q := K.pCoreIn 2
  have hQ2 : IsPGroup 2 Q := isPGroup_pCoreIn 2 K
  let : Nontrivial Q := (nontrivial_iff_ne_bot Q).mpr (by
    intro he
    exact hQ ((map_eq_bot_iff_of_injective _ K.subtype_injective).mp he))
  let : Nontrivial (center Q) := hQ2.center_nontrivial
  have hZ : (center Q).map Q.subtype ≠ ⊥ := by
    intro he
    exact (nontrivial_iff_ne_bot (center Q)).mp inferInstance
      ((map_eq_bot_iff_of_injective _ Q.subtype_injective).mp he)
  have hN : normalizer (K : Set G) ≤ normalizer ((center Q).map Q.subtype : Set G) :=
    (normalizer_le_normalizer_characteristic_image K (pCore 2 K)).trans
      (normalizer_le_normalizer_characteristic_image Q (center Q))
  exact le_antisymm (normalizer_le_of_unique_maximalTwoLocal hu
    ((hQ2.to_subgroup (center Q)).map Q.subtype) hZ (hJK.trans hN)) hN

/-- The full normalizers of both core centers are exactly the two original
normalizers. This is the normalizer assertion of F.4.31(a), expressed first
on the local factors whose two-cores agree with those of the parabolics. -/
theorem Preparation.symplectic_core_center_normalizers
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) :
    ∀ i : Fin 2, normalizer
      ((center ((![L,residual H] i).pCoreIn 2)).map
        ((![L,residual H] i).pCoreIn 2).subtype : Set G) =
      normalizer (![L,residual H] i : Set G) := by
  have hb := d.symplectic_amalgam_blocks h hH.1.1.2 hp F hm hF he
  intro i
  fin_cases i
  · exact core_center_normalizer_of_unique hb.2.1.2.1.core_ne_bot L.le_normalizer d.unique_left
  have hTK := hH.1.1.2.trans (le_normalizer_residual H)
  have hK := d.symplectic_right_maximal h hH hp F hm hF he
  have hu := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hK).normalizer_unique
  have ho : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTK)
      (le_componentOrbit _ _)
  rw [ho] at hu
  exact core_center_normalizer_of_unique hb.2.2.2.1.core_ne_bot
    (sup_le (residual H).le_normalizer hTK) hu

/-- The whole full-normalizer intersection contains the original Sylow
subgroup, so its index in the original ambient group is odd, as required
by F.4.31(d). No equality of the inner and ambient Sylows is used. -/
theorem symplectic_middle_odd_index
    {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Odd (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G).index := by
  have hT := le_inf h.sylow_normalizes (hH.1.1.2.trans (le_normalizer_residual H))
  apply Nat.not_even_iff_odd.mp
  rw [even_iff_two_dvd]
  exact fun hh => T.not_dvd_index (hh.trans (index_dvd_of_le hT))

private theorem ambient_twoPerfect {κ : GroupClass}
    (h : IsSimpleQTKE κ G) : IsPPerfect 2 G := by
  let := h.simple
  let : Group.IsPerfect G := ⟨(IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (_root_.commutator G) inferInstance).resolve_left
      (fun he => h.nonabelian ((commutator_eq_bot_iff G).mp he))⟩
  intro N hN hq
  let := hN
  have hs : Subsingleton (G ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (G ⧸ N) hq.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The literal source parabolics have the same core centers and full
normalizers as the corresponding local factors. -/
theorem Preparation.symplectic_parabolic_core_center_normalizers
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) :
    ∀ i : Fin 2,
      let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i
      P.pCoreIn 2 = (![L,residual H] i).pCoreIn 2 ∧
      normalizer ((center (P.pCoreIn 2)).map (P.pCoreIn 2).subtype : Set G) =
        normalizer (![L,residual H] i : Set G) := by
  have hf := d.hypothesisF11 h hH.1.1.2
  have hs := d.symplectic_sourceS_le_factors h hH.1.1.2 hp F hm hF he
  intro i
  have hcore : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i).pCoreIn 2 =
      (![L,residual H] i).pCoreIn 2 := by
    have hh := hf.local_inf_parabolic_core i
    rw [inf_eq_right.mpr ((hf.parabolic_core_le_S i).trans (hs i))] at hh
    exact hh
  refine ⟨hcore,?_⟩
  rw [hcore]
  exact d.symplectic_core_center_normalizers h hH hp F hm hF he i

/-- The established ambient inputs for the symplectic F.4.31 argument:
normalizers of both parabolic core centers, both root centralizer bounds,
odd index of the whole middle, and two-perfectness. These do not assert
the remaining characteristic-two condition for every involution in Z(S),
a compatible full-normalizer extension, or the ambient order comparison. -/
theorem Preparation.symplectic_source_local_inputs
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) :
    m = n ∧
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∧
    (∀ i : Fin 2,
      let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i
      P.pCoreIn 2 = (![L,residual H] i).pCoreIn 2 ∧
      normalizer ((center (P.pCoreIn 2)).map (P.pCoreIn 2).subtype : Set G) =
        normalizer (![L,residual H] i : Set G)) ∧
    (∀ i : Fin 2, ∀ z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype,
      orderOf z = 2 → centralizer ({z} : Set G) ≤ normalizer (![L,residual H] i : Set G)) ∧
    Odd (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G).index ∧
    IsPPerfect 2 G := by
  exact ⟨(d.symplectic_amalgam_blocks h hH.1.1.2 hp F hm hF he).1,
    d.symplectic_normalizer_local_conditions h hH hp F hm hF he,
    d.symplectic_parabolic_core_center_normalizers h hH hp F hm hF he,
    d.symplectic_central_involution_centralizers h hH hp F hm hF he,
    symplectic_middle_odd_index h hH, ambient_twoPerfect h.qtke⟩

omit [Finite G] in
private theorem square_central_sylow_transport
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    {T : Sylow 2 G} {S C : Subgroup G} (hSC : S ≤ C)
    (hTS : (T : Subgroup G) ≤ normalizer (S : Set G))
    (a : C ≃* borel (F := F))
    (hSU : (S.subgroupOf C).map a.toMonoidHom = unipotent.subgroupOf borel)
    (z : S) (hz : z ≠ 1) (hsq : ∃ y : S, y^2=z) :
    ∃ g ∈ C, (T : Subgroup G) ≤ centralizer ({g*z.val*g⁻¹} : Set G) := by
  let e : S ≃* unipotent (F := F) := (subgroupOfEquivOfLe hSC).symm.trans
    ((a.subgroupMap (S.subgroupOf C)).trans
      ((MulEquiv.subgroupCongr hSU).trans (subgroupOfEquivOfLe unipotent_le_borel)))
  let ρ := (MulAut.congr e).toMonoidHom.comp
    (S.normalizerMonoidHom.comp (inclusion hTS))
  have hz' : e z ≠ 1 := e.map_ne_one_iff.mpr hz
  have hsq' : ∃ y, y^2=e z := by
    obtain ⟨y,hy⟩ := hsq
    exact ⟨e y,by rw [←map_pow,hy]⟩
  obtain ⟨b,hb,w,he,hfix⟩ := SourceFusionOrder.square_conjugate_fixed
    T.isPGroup' ρ hF hn (e z) hz' hsq'
  let β : borel (F := F) →* G := C.subtype.comp a.symm.toMonoidHom
  have hβ (u : unipotent (F := F)) :
      β ⟨u.val,unipotent_le_borel u.property⟩ = (e.symm u).val := by
    rfl
  let g := β ⟨b,hb⟩
  have hg : g ∈ C := (a.symm ⟨b,hb⟩).property
  have hconj : g*z.val*g⁻¹ = (e.symm w).val := by
    have hh : (⟨b,hb⟩ : borel (F := F)) *
      ⟨(e z).val,unipotent_le_borel (e z).property⟩ * (⟨b,hb⟩ : borel (F := F))⁻¹ =
        ⟨w.val,unipotent_le_borel w.property⟩ := Subtype.ext he
    have hh' := congrArg β hh
    simpa only [map_mul,map_inv,hβ,e.symm_apply_apply] using hh'
  refine ⟨g,hg,?_⟩
  intro t ht
  rw [hconj]
  apply mem_centralizer_singleton_iff.mpr
  have hh := congrArg (fun u : unipotent (F := F) => (e.symm u).val) (hfix ⟨t,ht⟩)
  change (e.symm (e (S.normalizerMonoidHom ⟨t,hTS ht⟩ (e.symm w)))).val = _ at hh
  rw [e.symm_apply_apply] at hh
  change t*(e.symm w).val*t⁻¹ = (e.symm w).val at hh
  exact (mul_inv_eq_iff_eq_mul).mp hh

/-- Nonidentity squares in the original common Sylow are conjugate into a
centralizer containing the original ambient Sylow. The conjugator lies in
the literal common Borel, including its odd Cartans. -/
theorem Preparation.symplectic_square_central_sylow
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (z : sourceS L H) (hz : z ≠ 1) (hsq : ∃ y : sourceS L H, y^2=z) :
    ∃ g ∈ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H),
      (T : Subgroup G) ≤ centralizer ({g*z.val*g⁻¹} : Set G) := by
  let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
  have hSC : sourceS L H ≤ C := le_sup_right
  have hf := d.hypothesisF11 h hTH
  have ha : Nonempty (C ≃* borel (F := F)) := by
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · exact ⟨(MulEquiv.subgroupCongr (ChapterF.Source.lemma_F_1_3_6 hf)).symm.trans e.middle⟩
    · exact ⟨(MulEquiv.subgroupCongr (ChapterF.Source.lemma_F_1_3_6 hf)).symm.trans e.middle⟩
  obtain ⟨a⟩ := ha
  obtain ⟨P,hP⟩ := hf.sylow_commonBorel
  have hPS : (P : Subgroup C) = (sourceS L H).subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hSC]
  let U := (unipotentSylow hF hm).subtype unipotent_le_borel
  let : (U : Subgroup (borel (F := F))).Normal := unipotent_normal_in_borel
  let := Sylow.unique_of_normal U (inferInstance : U.Normal)
  have hSU : ((sourceS L H).subgroupOf C).map a.toMonoidHom = unipotent.subgroupOf borel := by
    rw [←hPS]
    exact congrArg Sylow.toSubgroup (Subsingleton.elim (P.mapSurjective a.surjective) U)
  exact square_central_sylow_transport hF hm hSC
    (sylow_normalizes_sourceS h.sylow_normalizes hTH) a hSU z hz hsq

private theorem centralizer_characteristic_of_sylow_conjugate
    (hG : IsEvenCharacteristic G) (T : Sylow 2 G) (z g : G) (hz : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({g*z*g⁻¹} : Set G)) :
    HasCharacteristicTwo (centralizer ({z} : Set G)) := by
  let a := MulAut.conj g⁻¹
  let U := T.mapSurjective (f := a.toMonoidHom) a.surjective
  have hUC : (U : Subgroup G) ≤ centralizer ({z} : Set G) := by
    have hh := (map_mono (f := a.toMonoidHom) hT).trans
      (map_centralizer_le_centralizer_image ({g*z*g⁻¹} : Set G) a.toMonoidHom)
    change (T : Subgroup G).map a.toMonoidHom ≤ _
    simpa [a,mul_assoc] using hh
  exact Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le U (hG U)
    (isTwoLocal_involution_centralizer hz) hUC)

/-- The nonroot central involutions, expressed intrinsically as nonidentity
squares of the original S, have characteristic-two full ambient centralizers. -/
theorem Preparation.symplectic_square_centralizer_characteristicTwo
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (z : sourceS L H) (hz : orderOf z = 2) (hsq : ∃ y : sourceS L H, y^2=z) :
    HasCharacteristicTwo (centralizer ({z.val} : Set G)) := by
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz
  obtain ⟨g,_,hT⟩ := d.symplectic_square_central_sylow h hTH F hm hF he z hz1 hsq
  exact centralizer_characteristic_of_sylow_conjugate h.qtke.evenCharacteristic T z.val g
    (by simpa only [Subgroup.orderOf_coe] using hz) hT

private theorem center_orbit_central_sylow {T : Sylow 2 G} {K P : Subgroup G}
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hchar : HasCharacteristicTwo K)
    (horbit : ∀ x ∈ (center K).map K.subtype, x ≠ 1 →
      ∀ y ∈ (center K).map K.subtype, y ≠ 1 → ∃ g ∈ P, y = g*x*g⁻¹)
    (z : G) (hz : z ∈ (center K).map K.subtype) (hz2 : orderOf z = 2) :
    ∃ g ∈ P, (T : Subgroup G) ≤ centralizer ({g*z*g⁻¹} : Set G) := by
  let Z := (center K).map K.subtype
  have hZT : Z ≤ (T : Subgroup G) := by
    have hZQ : center K ≤ pCore 2 K :=
      (center_le_centralizer (pCore 2 K : Set K)).trans hchar
    obtain ⟨U,hU⟩ := exists_sylow_component hTK
    exact (map_mono hZQ).trans ((pCoreIn_le_sylow K U).trans (hU ▸ inf_le_left))
  have hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G) :=
    hTK.trans (normalizer_le_normalizer_characteristic_image K (center K))
  let N := Z.subgroupOf (T : Subgroup G)
  let : N.Normal := normal_subgroupOf_of_le_normalizer hTZ
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz2
  let : Nontrivial N := (nontrivial_iff_ne_bot N).mpr (by
    intro he
    have : (⟨z,hZT hz⟩ : (T : Subgroup G)) ∈ N := hz
    rw [he,mem_bot] at this
    exact hz1 (congrArg Subtype.val this))
  let : Fact (IsPGroup 2 (T : Subgroup G)) := ⟨T.isPGroup'⟩
  obtain ⟨C,_,hCN,hcard,hCZ⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) N inferInstance
  obtain ⟨c,hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (by rw [hcard])
  let x : G := c.val.val
  have hxZ : x ∈ Z := hCN c.property
  have hx2 : orderOf x = 2 := by simpa only [x,Subgroup.orderOf_coe] using hc
  have hx1 : x ≠ 1 := by intro he; simp [he] at hx2
  have hTC : (T : Subgroup G) ≤ centralizer ({x} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp (hCZ c.property) ⟨t,ht⟩))
  obtain ⟨g,hg,he⟩ := horbit z hz hz1 x hxZ hx1
  exact ⟨g,hg,he ▸ hTC⟩

/-- Both root-involution centralizers have characteristic two in the original
ambient group, by their actual source orbits into a Sylow center. -/
theorem Preparation.symplectic_root_centralizer_characteristicTwo
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (i : Fin 2) (z : G) (hz : z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype)
    (hz2 : orderOf z = 2) : HasCharacteristicTwo (centralizer ({z} : Set G)) := by
  have hTK : (T : Subgroup G) ≤ normalizer (![L,residual H] i : Set G) := by
    fin_cases i
    · exact h.sylow_normalizes
    · exact hTH.trans (le_normalizer_residual H)
  obtain ⟨g,_,hT⟩ := center_orbit_central_sylow hTK
    ((d.hypothesisF11 h hTH).local_core_selfCentralizing i)
    (d.symplectic_center_orbit h hTH hp F hm hF he i) z hz hz2
  exact centralizer_characteristic_of_sylow_conjugate h.qtke.evenCharacteristic T z g hz2 hT
omit [Finite G] in
private theorem center_preimage {X : Type*} [Group X]
    {K P : Subgroup G} {R : Subgroup X} (hKP : K ≤ P)
    (f : P →* X) (hf : Function.Injective f)
    (hR : (K.subgroupOf P).map f = R) (z : P)
    (hz : f z ∈ (center R).map R.subtype) :
    z.val ∈ (center K).map K.subtype := by
  have hzR : f z ∈ R := map_subtype_le (center R) hz
  obtain ⟨v,hv,hvz⟩ := hR.symm ▸ hzR
  have hzK : z.val ∈ K := hf hvz ▸ hv
  refine ⟨⟨z.val,hzK⟩,mem_center_iff.mpr ?_,rfl⟩
  intro k
  let kP : P := ⟨k.val,hKP k.property⟩
  have hkR : f kP ∈ R := hR ▸ mem_map_of_mem f k.property
  obtain ⟨r,hr,her⟩ := hz
  change r.val = f z at her
  have hh := congrArg Subtype.val (mem_center_iff.mp hr ⟨f kP,hkR⟩)
  change f kP * r.val = r.val * f kP at hh
  rw [her] at hh
  have he : kP*z=z*kP := hf (by simpa only [map_mul] using hh)
  exact Subtype.ext (congrArg (fun p : P => p.val) he)

private theorem central_split_transport
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    {J K P Q C S : Subgroup G}
    (hJP : J ≤ P) (hKQ : K ≤ Q) (hCP : C ≤ P) (hCQ : C ≤ Q) (hSC : S ≤ C)
    (hs : Chapter1.IsSylowIn 2 S C)
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P C Q hCP hCQ)
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F))
    (hJ : (J.subgroupOf P).map (pointParabolic.subtype.comp e.left.toMonoidHom) = pointLocal)
    (hK : (K.subgroupOf Q).map (planeParabolic.subtype.comp e.right.toMonoidHom) = planeLocal)
    (z : S) (hz : z ∈ center S) :
    z.val ∈ (center J).map J.subtype ∨ z.val ∈ (center K).map K.subtype ∨
      ∃ y : S, y^2=z := by
  obtain ⟨R,hR⟩ := hs
  have hRS : (R : Subgroup C) = S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [hR,map_subgroupOf_eq_of_le hSC]
  let U := (unipotentSylow hF (by omega)).subtype unipotent_le_borel
  let : (U : Subgroup (borel (F := F))).Normal := unipotent_normal_in_borel
  let := Sylow.unique_of_normal U (inferInstance : U.Normal)
  have hSU : (S.subgroupOf C).map e.middle.toMonoidHom = unipotent.subgroupOf borel := by
    rw [←hRS]
    exact congrArg Sylow.toSubgroup (Subsingleton.elim (R.mapSurjective (f := e.middle.toMonoidHom) e.middle.surjective) U)
  let a : S ≃* unipotent (F := F) := (subgroupOfEquivOfLe hSC).symm.trans
    ((e.middle.subgroupMap (S.subgroupOf C)).trans
      ((MulEquiv.subgroupCongr hSU).trans (subgroupOfEquivOfLe unipotent_le_borel)))
  have haz : a z ∈ center (unipotent (F := F)) := (centerCongr a ⟨z,hz⟩).property
  have hleft : (e.left ⟨z.val,(hSC.trans hCP) z.property⟩).val = (a z).val :=
    congrArg Subtype.val (e.left_commutes ⟨z.val,hSC z.property⟩)
  have hright : (e.right ⟨z.val,(hSC.trans hCQ) z.property⟩).val = (a z).val :=
    congrArg Subtype.val (e.right_commutes ⟨z.val,hSC z.property⟩)
  rcases SourceFusionOrder.center_local_or_square hF hn (a z) haz with hp | hq | hsq
  · left
    rw [←hleft] at hp
    exact center_preimage hJP _ (pointParabolic.subtype_injective.comp e.left.injective)
      hJ ⟨z.val,(hSC.trans hCP) z.property⟩ hp
  · right; left
    rw [←hright] at hq
    exact center_preimage hKQ _ (planeParabolic.subtype_injective.comp e.right.injective)
      hK ⟨z.val,(hSC.trans hCQ) z.property⟩ hq
  · right; right
    obtain ⟨y,hy⟩ := hsq
    exact ⟨a.symm y,by rw [←map_pow,hy,a.symm_apply_apply]⟩

/-- The literal central plane in the source has exactly the root-center
or Sylow-square alternatives needed in the characteristic-two argument. -/
theorem Preparation.symplectic_center_local_or_square
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (z : sourceS L H) (hz : z ∈ center (sourceS L H)) :
    z.val ∈ (center L).map L.subtype ∨
      z.val ∈ (center (residual H)).map (residual H).subtype ∨
      ∃ y : sourceS L H, y^2=z := by
  have hf := d.hypothesisF11 h hTH
  have hmn := (d.symplectic_amalgam_blocks h hTH hp F hm hF he).1
  have hm' : 1 < m := hmn.symm ▸ h.exponent
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let C := P 0 ⊓ P 1
  have hSC : sourceS L H ≤ C := le_inf (le_sup_right.trans le_sup_left)
    (le_sup_right.trans le_sup_left)
  have hs : Chapter1.IsSylowIn 2 (sourceS L H) C := by
    change Chapter1.IsSylowIn 2 (sourceS L H) (P 0 ⊓ P 1)
    rw [show P 0 ⊓ P 1 = ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) from
      ChapterF.Source.lemma_F_1_3_6 hf]
    exact hf.sylow_commonBorel
  have hres (i : Fin 2) : (![L,residual H] i).subgroupOf (P i) = solvableResidual (P i) := by
    rw [←d.parabolic_residuals h hTH hp i]
    exact comap_map_eq_self_of_injective (P i).subtype_injective _
  have hpoint (i : Fin 2) (a : P i ≃* pointParabolic (F := F)) :
      ((![L,residual H] i).subgroupOf (P i)).map
        (pointParabolic.subtype.comp a.toMonoidHom) = pointLocal := by
    rw [hres,←map_map,map_solvableResidual_eq a.toMonoidHom a.surjective]
    exact pointParabolic_solvableResidual_eq hF hm'
  have hplane (i : Fin 2) (a : P i ≃* planeParabolic (F := F)) :
      ((![L,residual H] i).subgroupOf (P i)).map
        (planeParabolic.subtype.comp a.toMonoidHom) = planeLocal := by
    rw [hres,←map_map,map_solvableResidual_eq a.toMonoidHom a.surjective]
    exact planeParabolic_solvableResidual_eq hF hm'
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · exact central_split_transport hF hm'
      (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_left)
      inf_le_left inf_le_right hSC hs e (hpoint 0 e.left) (hplane 1 e.right) z hz
  · have hh := central_split_transport hF hm'
      (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_left)
      inf_le_right inf_le_left hSC hs e.reverse (hpoint 1 e.right) (hplane 0 e.left) z hz
    rcases hh with hk | hl | hs
    · exact Or.inr (Or.inl hk)
    · exact Or.inl hl
    · exact Or.inr (Or.inr hs)

/-- The full characteristic-two clause of F.4.31(c), with no centralizer
hypothesis: it holds for every involution in the original Z(S). -/
theorem Preparation.symplectic_center_centralizer_characteristicTwo
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (z : G) (hz : z ∈ (center (sourceS L H)).map (sourceS L H).subtype)
    (hz2 : orderOf z = 2) :
    HasCharacteristicTwo (centralizer ({z} : Set G)) ∧
      generalizedFitting (centralizer ({z} : Set G)) = pCore 2 (centralizer ({z} : Set G)) := by
  have hc : HasCharacteristicTwo (centralizer ({z} : Set G)) := by
    obtain ⟨z,hz,rfl⟩ := hz
    change orderOf z.val = 2 at hz2
    rcases d.symplectic_center_local_or_square h hTH hp F hm hF he z hz with hl | hk | hs
    · exact d.symplectic_root_centralizer_characteristicTwo h hTH hp F hm hF he 0 z.val hl hz2
    · exact d.symplectic_root_centralizer_characteristicTwo h hTH hp F hm hF he 1 z.val hk hz2
    · exact d.symplectic_square_centralizer_characteristicTwo h hTH F hm hF he z
        (by simpa only [Subgroup.orderOf_coe] using hz2) hs
  exact ⟨hc,generalizedFitting_eq_pCore_of_selfCentralizing 2 hc⟩
/-- Both source root centers are elementary abelian TI subgroups, and their
full ambient normalizers are precisely the corresponding factor normalizers.
This is the symplectic specialization of F.4.34(1),(2). -/
theorem Preparation.symplectic_root_center_fusion
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (i : Fin 2) :
    IsElementaryAbelian 2 ((center (![L,residual H] i)).map (![L,residual H] i).subtype) ∧
    ChapterI.Section06To08.IsTISubgroup
      ((center (![L,residual H] i)).map (![L,residual H] i).subtype) ∧
    normalizer ((center (![L,residual H] i)).map (![L,residual H] i).subtype : Set G) =
      normalizer (![L,residual H] i : Set G) := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i
  let K := ![L,residual H] i
  have hKP : K ≤ P := le_sup_left.trans le_sup_left
  let a : planeParabolic (F := F) ≃* pointParabolic :=
    ((DiagramAutomorphisms.ExceptionalGraph.graphAut (F := F)).subgroupMap planeParabolic).trans
      (MulEquiv.subgroupCongr DiagramAutomorphisms.ExceptionalGraph.graphAut_map_plane)
  have hep : Nonempty (P ≃* pointParabolic (F := F)) := by
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · fin_cases i
      · exact ⟨e.left⟩
      · exact ⟨e.right.trans a⟩
    · fin_cases i
      · exact ⟨e.left.trans a⟩
      · exact ⟨e.right⟩
  obtain ⟨e⟩ := hep
  have hm' : 1 < m := (d.symplectic_amalgam_blocks h hH.1.1.2 hp F hm hF he).1.symm ▸ h.exponent
  have hres : K.subgroupOf P = solvableResidual P := by
    change (![L,residual H] i).subgroupOf P = solvableResidual P
    rw [←d.parabolic_residuals h hH.1.1.2 hp i]
    exact comap_map_eq_self_of_injective P.subtype_injective _
  have hR : (K.subgroupOf P).map (pointParabolic.subtype.comp e.toMonoidHom) = pointLocal := by
    rw [hres,←map_map,map_solvableResidual_eq e.toMonoidHom e.surjective]
    exact pointParabolic_solvableResidual_eq hF hm'
  let r := Representation.OneCohomology.SymplecticFour.rootElement 0 (1:F)
  have hr : r ∈ (center (pointLocal (F := F))).map pointLocal.subtype := by
    rw [PointRadicalAction.center_eq_root hF hm']
    exact (RootSubgroup.mem_group_iff 0 _).mpr ⟨1,rfl⟩
  have hrP : r ∈ pointParabolic (F := F) := pointLocal_le (map_subtype_le _ hr)
  have hr2 : orderOf r = 2 := by
    apply orderOf_eq_prime
    · change Representation.OneCohomology.SymplecticFour.rootElement 0 (1:F)^2=1
      rw [pow_two,RootSubgroup.element_add,CharTwo.add_self_eq_zero,RootSubgroup.element_zero]
    · intro heq
      exact one_ne_zero (RootSubgroup.element_injective 0
        (heq.trans (RootSubgroup.element_zero 0).symm))
  let z := e.symm ⟨r,hrP⟩
  have hz : z.val ∈ (center K).map K.subtype := by
    apply center_preimage hKP _ (pointParabolic.subtype_injective.comp e.injective) hR z
    simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,Subgroup.subtype_apply,z,
      e.apply_symm_apply] using hr
  have hz2 : orderOf z.val = 2 := by
    have hh := e.orderOf_eq z
    rw [show e z = ⟨r,hrP⟩ from e.apply_symm_apply _] at hh
    exact (Subgroup.orderOf_coe z).trans (hh.symm.trans
      ((Subgroup.orderOf_coe (⟨r,hrP⟩ : pointParabolic (F := F))).symm.trans hr2))
  have hPN : P ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKP).mp
      ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic i)
  exact center_orbit_fusion hPN ⟨z.val,hz,hz2⟩
    (d.symplectic_center_orbit h hH.1.1.2 hp F hm hF he i)
    (d.symplectic_central_involution_centralizers h hH hp F hm hF he i)

/-- All ambient assumptions (a)–(e) of F.4.31 and both TI conclusions of
F.4.34 are now proved on the original pair. Construction of the compatible
full-normalizer extension is still required before applying F.4.31 itself. -/
theorem Preparation.symplectic_source_ambient_inputs
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) :
    m = n ∧
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∧
    (∀ i : Fin 2,
      let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i
      P.pCoreIn 2 = (![L,residual H] i).pCoreIn 2 ∧
      normalizer ((center (P.pCoreIn 2)).map (P.pCoreIn 2).subtype : Set G) =
        normalizer (![L,residual H] i : Set G)) ∧
    (∀ i : Fin 2, ∀ z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype,
      orderOf z = 2 → centralizer ({z} : Set G) ≤ normalizer (![L,residual H] i : Set G)) ∧
    (∀ z ∈ (center (sourceS L H)).map (sourceS L H).subtype, orderOf z = 2 →
      generalizedFitting (centralizer ({z} : Set G)) =
        pCore 2 (centralizer ({z} : Set G))) ∧
    Odd (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G).index ∧
    IsPPerfect 2 G ∧
    (∀ i : Fin 2,
      IsElementaryAbelian 2 ((center (![L,residual H] i)).map (![L,residual H] i).subtype) ∧
      ChapterI.Section06To08.IsTISubgroup
        ((center (![L,residual H] i)).map (![L,residual H] i).subtype) ∧
      normalizer ((center (![L,residual H] i)).map (![L,residual H] i).subtype : Set G) =
        normalizer (![L,residual H] i : Set G)) := by
  obtain ⟨hmn,hlocal,hnorm,hcent,hodd,hperfect⟩ :=
    d.symplectic_source_local_inputs h hH hp F hm hF he
  exact ⟨hmn,hlocal,hnorm,hcent,
    fun z hz hz2 => (d.symplectic_center_centralizer_characteristicTwo
      h hH.1.1.2 hp F hm hF he z hz hz2).2,
    hodd,hperfect,d.symplectic_root_center_fusion h hH hp F hm hF he⟩


end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
