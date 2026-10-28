module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityPointBinary
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.RankOne.PointNormalizers

/-!
# Direct rank-one point control, including component-fixed points

The Baumann calculation makes C_T(v) Sylow in the full point centralizer.
If it exchanges the original components, moved binary maximality with this
same local Sylow makes L a C-component of C_G(v). The normal Sylow orbit is
exactly the original L₀, so C_G(v) lies in N_G(L₀) = M, contradicting escape.
This proves the missing component-stabilizer clause of PointSylowControl.

All opposite points, field degrees and fixed kernels are retained. This
route does not assert uniform stabilization of the entire L₀-fixed layer.
The literal selected-module application is in ModuleChoice.Source.
Source: Aschbacher--Smith, 1.2.8(3) and 10.2.9, pp.506--507 and750.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

omit D [Finite G] in
private theorem centralizer_core_ne_bot {v : G}
    (hvT : v ∈ (T : Subgroup G)) (hv1 : v ≠ 1)
    {X : Subgroup G} (hvX : v ∈ X) (hX : X ≤ centralizer ({v} : Set G)) :
    X.pCoreIn 2 ≠ ⊥ := by
  have hp : IsPGroup 2 (zpowers v) := T.isPGroup'.to_le (zpowers_le.mpr hvT)
  have hn : X ≤ normalizer (zpowers v : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [zpowers_eq_closure,centralizer_closure]
    exact hX
  have hle := le_pCoreIn_of_normalizes hp (zpowers_le.mpr hvX) hn
  intro he
  exact hv1 (mem_bot.mp (he ▸ hle (mem_zpowers v)))

private theorem binary_model
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hmodel : RankOneNatural D) :
    ∃ n : ℕ, 2 < n ∧ ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n) ∧
      ¬ ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4 := by
  have hnot : ¬ ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4 := by
    rintro ⟨F,_,_,hF,⟨e⟩⟩
    obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
    exact hna ⟨e.trans f⟩
  obtain ⟨n,hn,e,_⟩ := hmodel
  let : NeZero n := ⟨by omega⟩
  have hc : Nat.card (GaloisField 2 n) = 2^n := GaloisField.card 2 n (by omega)
  have hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n) :=
    ⟨GaloisField 2 n,inferInstance,inferInstance,hc,
      ⟨e.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 n))⟩⟩
  have hne : n ≠ 2 := by
    rintro rfl
    exact hnot hm
  exact ⟨n,by omega,hm,hnot⟩

include D in
/-- A subgroup of the original Sylow containing an exchanger has precisely
the original two-component orbit. -/
theorem point_orbit_eq_original {R : Subgroup G} (hRT : R ≤ (T : Subgroup G))
    (hm : ¬ R ≤ normalizer (L : Set G)) : conjugateSpanBy L R = localOrbit T L := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => hm (hRT.trans h)
  obtain ⟨t,ht,htn,hpair,horbit⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  obtain ⟨r,hr,hrn⟩ := Set.not_subset.mp hm
  have he : L.map (MulAut.conj r).toMonoidHom = L.map (MulAut.conj t).toMonoidHom :=
    (horbit r (hRT hr)).resolve_left (fun h => hrn (mem_normalizer_iff_map_conj_eq.mpr h))
  have hpartner : L.map (MulAut.conj t).toMonoidHom ≤ conjugateSpanBy L R := by
    rw [←he,conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun s : R => L.map (MulAut.conj (s : G)).toMonoidHom) ⟨r,hr⟩
  apply le_antisymm
  · rw [conjugateSpanBy_eq_iSup_conj]
    apply iSup_le
    intro s
    rw [hpair]
    exact (horbit s (hRT s.property)).elim
      (fun h => h.le.trans le_sup_left) (fun h => h.le.trans le_sup_right)
  · rw [hpair]
    exact sup_le (le_conjugateSpanBy L R) hpartner

/-- A saturated escaping opposite point has a Sylow centralizer fixing L.
If it moved L, arbitrary-local-Sylow maximality would make L a component
of C_G(v), whose Sylow orbit is the original L₀. Its normality contradicts escape. -/
theorem point_sylow_normalizes_component
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hmodel : RankOneNatural D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hvne : v ≠ 1) (hout : ¬ centralizer ({v} : Set G) ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G))) :
    (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  by_contra hm
  let H := centralizer ({v} : Set G)
  let R := (T : Subgroup G) ⊓ H
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hvT := D.fullModule_le_sylow hu (partner_le_fullModule D ht hv)
  have hvH : v ∈ H := mem_centralizer_singleton_iff.mpr rfl
  have hvL := hcross hv
  have hLH : L ≤ H := fun l hl => mem_centralizer_singleton_iff.mpr (hvL l hl)
  have hRH : R ≤ H := inf_le_right
  have hcore : H ∈ Chapter1.H G := centralizer_core_ne_bot hvT hvne hvH le_rfl
  have hSyl : Chapter1.IsSylowIn 2 R H :=
    (point_sylow_normalizer_and_sylow D hna hmodel ht htn hv hs).2
  have hlocal : L ∈ Chapter1.L G R := by
    refine ⟨D.maximal.1.1.subgroupOf_of_le le_sup_left
      (sup_le le_sup_left (inf_le_left.trans le_sup_right)),?_,?_⟩
    · exact hSyl.restrict le_sup_right (sup_le hLH hRH)
    · exact centralizer_core_ne_bot hvT hvne
        (mem_sup_right (show v ∈ R from ⟨hvT,hvH⟩)) (sup_le hLH hRH)
  obtain ⟨n,hn,hbinary,hnot⟩ := binary_model D hna hmodel
  have hcomp := Chapter1.Section02.MovedMaximalityPoint.binary_component_in_overgroup
    D.simpleQTKE hlocal hLH hcore hSyl hm hn hbinary hnot
  have hnorm := Chapter1.Section02.MovedMaximalityPoint.relative_sylow_orbit_normalized
    D.simpleQTKE hLH hcore hSyl hcomp
  rw [point_orbit_eq_original D inf_le_left hm] at hnorm
  exact hout hnorm

/-- Direct rank-one point control for every field degree and every fixed kernel.
No uniform fixed-layer stabilization or half-Sylow uniqueness is required. -/
theorem pointSylowControl_direct
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hmodel : RankOneNatural D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    PointSylowControl D t := by
  intro v hv hvne hout hs
  exact ⟨(point_sylow_normalizer_and_sylow D hna hmodel ht htn hv hs).1,
    point_sylow_normalizes_component D hna hmodel ht htn hcross hv hvne hout hs⟩

end CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
