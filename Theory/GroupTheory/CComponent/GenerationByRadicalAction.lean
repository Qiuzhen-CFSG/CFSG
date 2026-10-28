module

public import Theory.GroupTheory.NormalQuotientActionSupplements
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.Commutator.PerfectSolvableSupplement

/-!
# Generation by components using their radical quotient actions

Assume the perfect residual normalizes each original ambient C-component,
distinct components commute, and the simple radical quotients have solvable
outer groups. The characteristic quotient action kernels have component
supplements. Finite successive adjustment gives a supplement by their common
kernel. If that kernel were nonsolvable, one of its C-components would lift
to an original ambient component lying in its own action kernel, contradicting
nonabelian simplicity of its radical quotient. The resulting solvable supplement
vanishes in the perfect quotient by the component layer.

All components are indexed in the original ambient group. No equality between
the component families of the group and its residual, or commuting-product
residual formula, is assumed.

Source application: Aschbacher--Smith, A.3.9(1), printed p.46.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Original components generate the residual when their radical actions have solvable outer groups. -/
theorem cComponentLayer_eq_residual_of_radical_actions
    (hnormal : ∀ L : Subgroup G, L.IsCComponent →
      solvableResidual G ≤ normalizer (L : Set G))
    (hcomm : ∀ B C : Subgroup G, B.IsCComponent → C.IsCComponent → B ≠ C → ⁅B, C⁆ = ⊥)
    (houter : ∀ L : Subgroup (solvableResidual G), L.IsCComponent →
      Group.IsSolvable (MulAut.Outer (L ⧸ solvableRadical L))) :
    cComponentLayer G = solvableResidual G := by
  classical
  let R := solvableResidual G
  have hLR {L : Subgroup G} (hL : L.IsCComponent) : L ≤ R := by
    let := hL.perfect
    exact le_solvableResidual_of_isPerfect L
  have hHR : cComponentLayer G ≤ R := sSup_le fun _ hL => hLR hL
  let I := {L : Subgroup G // L.IsCComponent}
  let D (i : I) : Subgroup R := i.val.subgroupOf R
  have hD (i : I) : (D i).IsCComponent := i.property.subgroupOf (hLR i.property)
  let hDN (i : I) : (D i).Normal := normal_subgroupOf_of_le_normalizer
    (hnormal i.val i.property)
  let C (i : I) : Subgroup R := (normalQuotientAction (D i) (solvableRadical (D i))).ker
  let hCN (i : I) : (C i).Normal := inferInstance
  have hsupp (i : I) : D i ⊔ C i = ⊤ := by
    let : Group.IsSolvable (MulAut.Outer (D i ⧸ solvableRadical (D i))) :=
      houter (D i) (hD i)
    exact sup_normalQuotientAction_ker_eq_top_of_perfect (D i) _
  have hcross (i j : I) (hne : i ≠ j) : D i ≤ C j := by
    apply le_trans _ (centralizer_le_normalQuotientAction_ker (D j) _)
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply map_injective R.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le (hLR i.property),
      map_subgroupOf_eq_of_le (hLR j.property), map_bot]
    exact hcomm i.val j.val i.property j.property
      (fun he => hne (Subtype.ext he))
  let K : Subgroup R := ⨅ i, C i
  let : K.Normal := ⟨by
    intro x hx g
    exact mem_iInf.mpr fun i => (hCN i).conj_mem x (mem_iInf.mp hx i) g⟩
  have hsK : Group.IsSolvable K := by
    by_contra hn
    obtain ⟨A, hAcomp⟩ := exists_isCComponent_of_not_isSolvable hn
    let E : Subgroup R := A.map K.subtype
    have hE : E.IsCComponent := hAcomp.map_subtype (inferInstance : K.Normal).isSubnormal
    let L : Subgroup G := E.map R.subtype
    have hL : L.IsCComponent := hE.map_subtype (inferInstance : R.Normal).isSubnormal
    let i : I := ⟨L, hL⟩
    have he : D i = E := by
      dsimp [D, i, L]
      exact comap_map_eq_self_of_injective R.subtype_injective E
    have hEK : E ≤ K := map_subtype_le A
    have hi : D i ≤ C i := by
      rw [he]
      exact hEK.trans (iInf_le C i)
    exact (hD i).not_isMulCommutative_quotient_solvableRadical
      (isMulCommutative_of_le_normalQuotientAction_ker (D i) _ hi)
  let H : Subgroup R := (cComponentLayer G).subgroupOf R
  let := cComponentLayer_characteristic (G := G)
  let : H.Normal := inferInstance
  have hsup : H ⊔ K = ⊤ := sup_iInf_eq_top_of_independent_supplements D C hCN hsupp
    hcross H (fun i => comap_mono (le_cComponentLayer i.property))
  let := hsK
  have htop : H = ⊤ := by
    apply top_unique
    simpa only [solvableResidual_eq_top] using
      (inferInstance : H.Normal).isSubnormal.solvableResidual_le_of_sup_eq_top K hsup
  have hm := congrArg (Subgroup.map R.subtype) htop
  simpa only [H, map_subgroupOf_eq_of_le hHR, ← MonoidHom.range_eq_map, range_subtype] using hm

end Subgroup
