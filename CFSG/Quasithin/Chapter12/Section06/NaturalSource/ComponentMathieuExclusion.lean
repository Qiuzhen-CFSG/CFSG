module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentMathieuStabilizer
public import Theory.Representation.Mathieu.M22James.MovedStabilizer.Transport

/-!
# Excluding the original cubic Mathieu component

Construct the literal U_H/V₁ action and its whole component commutator.
The chief-section equivalence proves displacement four on that component
for the same original V-star involution. Equality with the ambient
rank-four displacement retains every ambient fixed layer.

A nonsingular point in the original V₅ has nonzero quotient image in this
moved space. The native Mathieu calculation gives its component stabilizer
a nontrivial perfect subgroup, while the earlier TI and nonsingular
centralizer inputs make that same stabilizer solvable. This excludes M₂₂.
Together with the preceding cover exclusions, the selected component is
simple and the original rank-two Sylow action is faithful.

The TI and nonsingular-centralizer inputs remain explicit (12.2.6 and
12.6.2; the latter retains qt-d-12634-central). The remaining simple
component branches, 12.6.26, later local alternatives and universal
NaturalReduction are still obligations. No conclusion is inferred for
unmarked modules or for the entire ambient quotient.

Source: Aschbacher–Smith, proof of 12.6.26, printed pp.832–833,
using the moved-point consequence of H.12.1(5),(7), pp.393–394.
-/
public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
  (hm : Chapter1.Section02.LocalModels.IsM22Cover (Nonabelian.Setup.star H c.K))

include hz hTV hTz hbound hH hn a hm in
/-- Exclude the actual cubic Mathieu component using the original nonsingular
point and its literal stabilizer, retaining the genuine earlier inputs. -/
theorem SourceHypothesis.original_mathieuCover_excluded
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) : False := by
  classical
  let E := D.fullSetup hZ T z
  let h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  let := h.point_normal_in_UH
  let := h.point_quotient_elementary
  obtain ⟨σ,κ,hσ,_⟩ := h.faithful_point_quotient
  obtain ⟨C,hC,_,_,_,_,⟨ec,⟨em⟩⟩,t,ht,hto,_,hdisp,hVC,U,N,hirr,hd,hCN,eC,_⟩ :=
    S.original_mathieuCover_commutator_of_binary_section D hZ z hz hTV hTz hbound hH hn c a hm σ hσ κ
  let B := Nonabelian.Setup.star H c.K
  let : B.Normal := (S.original_cubicCover_component_normal D hZ z hz hH c (Or.inr hm)).1
  obtain ⟨w,hw5,hw⟩ := S.original_perpendicular_has_nonsingular D hZ z
  have hwU : w.val ∈ E.UH H := (le_conjugateSpanBy _ _) hw5
  let v := (κ.coordinates ⟨w.val,hwU⟩).toAdd
  have hv0 : v ≠ 0 := by
    intro he
    have hw1 : w.val ∈ E.V₁ := (κ.coordinates_eq_one_iff ⟨w.val,hwU⟩).mp he
    have ho : orderOf z.val = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian _ z.property) (fun he => hz (Subtype.ext he))
    change w.val ∈ zpowers z.val at hw1
    rw [mem_zpowers_iff_mem_range_orderOf,ho] at hw1
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hw1
    have hn2 : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · exact nonsingular_ne_one D hw (Subtype.ext (by simpa using he.symm))
    · have hwz : w = z := Subtype.ext (by simpa using he.symm)
      exact S.original_point_singular D hZ z hz hTz (hwz ▸ hw)
  have hv5 : v ∈ κ.imageSpace E.V₅ :=
    (κ.mem_imageSpace_iff E.V₅ v).mpr ⟨⟨w.val,hwU⟩,hw5,rfl⟩
  let u : C.toSubmodule := ⟨v,hVC hv5⟩
  have hum : u.val ∈ (σ t - LinearMap.id).range := hdisp.symm ▸ hv5
  let X := B ⊔ zpowers t
  let tx : X := ⟨t,(le_sup_right : zpowers t ≤ X) (mem_zpowers t)⟩
  have hdc : fixedCodim C.toRepresentation (zpowers t) = 4 := by
    have he := fixedCodim_map_equivariant (C.toRepresentation.comp X.subtype)
      (sectionRepresentation (σ.comp X.subtype) U N) (MonoidHom.id X)
      eC.toLinearEquiv (fun g v => LinearMap.congr_fun (eC.isIntertwining' g) v) (zpowers tx)
    simp only [Subgroup.map_id] at he
    rw [fixedCodim_zpowers_eq_displacement_rank] at he ⊢
    exact he.trans hd
  have hs := S.original_mathieuCover_point_stabilizer_solvable D hZ z hz hTV hTz hbound hH hn
    c a hm hTI hns σ κ w hw hwU
  exact Sporadic.Mathieu.M22TripleCover.MovedStabilizer.original_moved_stabilizer_not_solvable
    (G := Nonabelian.Setup.Hstar H) σ B C ec em t
    (by simpa only [hto] using pow_orderOf_eq_one t) hdc
    (S.original_binary_displacement_bound D hZ z hz hTV hTz hbound hH hn σ κ t ht)
    u hum hv0 hs
include hz hTV hTz hbound hH hn a in
/-- All nonsimple selected-component rows are excluded under the genuine earlier
TI and nonsingular-centralizer inputs. The simple rows still need analysis. -/
theorem SourceHypothesis.original_selectedComponent_simple
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    IsSimpleGroup (Nonabelian.Setup.star H c.K) := by
  rcases S.original_selectedComponent_simple_or_mathieu_cover D hZ z hz hTV hTz
    hbound hns hH hn c a with hs|⟨_,hm,_⟩
  · exact hs
  · exact (S.original_mathieuCover_excluded D hZ z hz hTV hTz hbound hH hn c a hm hTI hns).elim

include hz hTV hTz hbound hH hn a in
/-- In the remaining rank-two branch the original Sylow E₉ acts faithfully
on the same selected component; no central-cover alternative remains. -/
theorem SourceHypothesis.original_rank_two_sylow_faithful
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    Function.Injective (a.residualSylowAction P) := by
  let B := Nonabelian.Setup.star H c.K
  let : IsSimpleGroup B := S.original_selectedComponent_simple D hZ z hz hTV hTz
    hbound hH hn c a hTI hns
  let := c.component.2
  apply S.original_rank_two_centerless_sylow_faithful D hZ z hz hTz hH c a hr
  rcases (inferInstance : (center B).Normal).eq_bot_or_eq_top with h|h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp h)).elim

end CFSG.Quasithin.Chapter12.Section06
