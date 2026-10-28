module
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.OriginalFixedSpace
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsExclusion
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalProduct

/-!
# Original Section12.6 orthogonal exclusion at the same ambient Sylow

The earlier structural statement supplies Sylow invariance and local TI.
The original fixed-space theorem gives full coordinates, and the actual
nonsingular-centralizer theorem gives the global intersection bound.
A nonidentity point fixed by the original Sylow is singular. The original
centralizer-escape theorem and the marked singular orbit put its full
centralizer in the literal source family Hz. The proved terminal source
contradiction then excludes the orthogonal chosen-module row.

Only the original source, its marking, the same-G,T earlier structural and
module statements, and the multiple-overgroup guard remain as inputs.
Source: Aschbacher--Smith 12.6.23--34, printed pp.829--838.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
open Section02
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original orthogonal chosen-module source is impossible, with every
Section12.6 local centralizer and terminal premise derived at the same G,T. -/
theorem SourceHypothesis.original_orthogonal_impossible_at
    (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V S.chosen.normalizes)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) : False := by
  classical
  have hs := (structural L S.source).2.2 V S.chosen
  have hTV := hs.1
  have hTI : CentralLine.HasTIConjugatesIn V (M L) := hs.2.2.1
  have hZ := S.original_fixed_space_eq_bot D structural modules hmany
  have hns := S.original_nonsingular_centralizer_le_of_ti D hTV hTI
  have hlog := (S.fixed_free_intersections_of_control D hTV hTI hZ hns).1
  have hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2^3 := by
    intro g hg
    let W := V ⊓ V.map (MulAut.conj g).toMonoidHom
    let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (show W ≤ V from inf_le_left)
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    have hd := (hlog g hg).2
    change Nat.log 2 (Nat.card W) ≤ 3 at hd
    rw [hn,Nat.log_pow (by decide)] at hd
    change Nat.card W ≤ 2^3
    rw [hn]
    exact Nat.pow_le_pow_right (by decide) hd
  let A := V.subgroupOf (T : Subgroup G)
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer S.chosen.le_sylow).mpr hTV
  have hA : A ≠ ⊥ := by
    intro ha
    apply S.chosen.ne_bot
    rw [←map_subgroupOf_eq_of_le S.chosen.le_sylow]
    change A.map (T : Subgroup G).subtype = ⊥
    rw [ha,Subgroup.map_bot]
  have hne := center_inf_ne_bot_of_normal T.isPGroup' A hA
  obtain ⟨x,hx,hxne⟩ := (center (T : Subgroup G) ⊓ A).bot_or_exists_ne_one.resolve_left hne
  let z : V := ⟨(x : G),hx.2⟩
  have hz : z ≠ 1 := by
    intro he
    apply hxne
    apply Subtype.ext
    exact congrArg (fun a : V => (a : G)) he
  let E := D.fullSetup hZ T z
  have hTz : (T : Subgroup G) ≤ normalizer (E.V₁ : Set G) := by
    have hTC : (T : Subgroup G) ≤ Gv (z : G) := by
      intro y hy
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (mem_center_iff.mp hx.1 ⟨y,hy⟩)
    apply hTC.trans
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    rw [Nonabelian.Setup.V₁,zpowers_eq_closure,centralizer_closure]
    rfl
  have hsz := S.original_point_singular D hZ z hz hTz
  obtain ⟨v,hv,hvne,hout⟩ := S.original_centralizer_escape D structural modules hmany L V S.source S.chosen
  let w : V := ⟨v,hv⟩
  have hw : w ≠ 1 := fun he => hvne (congrArg Subtype.val he)
  have hsw : ¬ D.Nonsingular w := fun hh => hout (hns w hh)
  obtain ⟨l,hl⟩ := D.fixed_free_orbit_of_same_form S.chosen hZ w z hw hz (by simp [hsw,hsz])
  have houtz : ¬ E.Gz ≤ E.M := by
    intro hc
    apply hout
    apply CentralLine.centralizer_le_of_conjugate (L.le_normalizer l.property)
    have he : (MulAut.conj (l : G)) v = (z : G) := congrArg Subtype.val hl
    rw [he]
    rw [E.Gz_eq] at hc
    exact hc
  have hH := E.Gz_mem_Hz hz hTz houtz
  exact S.original_abelian_point_overgroup_impossible D hZ z hz hTV hTz hbound hTI hns hH

end CFSG.Quasithin.Chapter12.Section06
