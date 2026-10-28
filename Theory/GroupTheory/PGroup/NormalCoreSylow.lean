module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Restricting p-core Sylow control to a normal subgroup

Suppose the ambient p-core is a Sylow p-subgroup of a subgroup `K`.
For any normal subgroup `N`, the intrinsic p-core of `N` is then Sylow
in `K ∩ N`, expressed here as `K.subgroupOf N`.

Normality identifies `O_p(N)` with `O_p(G) ∩ N`: its ambient image is
normal by characteristic-normal transitivity, and the reverse inclusion is
a normal p-subgroup of `N`. Every p-subgroup of the restricted `K` maps
into its normal Sylow `O_p(G)`, so its image in `N` lies in `O_p(N)`.
This gives maximality of the restricted core directly.

This standard finite-group transfer supplies the restriction from the
centralizer in `Pstar` to the centralizer in the normal closure `L` in
Stellmacher (4.6), `refs/latex/stellmacher-n-group.tex`.
-/

/-- If the ambient p-core is Sylow in `K`, the core of a normal subgroup
is Sylow in the restriction of `K` to that subgroup. -/
public theorem pCore_sylow_restrict_normal
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (N K : Subgroup G) [N.Normal]
    (hSyl : ∃ T : Sylow p K, (T : Subgroup K).map K.subtype = pCore p G) :
    ∃ T : Sylow p (K.subgroupOf N),
      (T : Subgroup (K.subgroupOf N)).map (K.subgroupOf N).subtype = pCore p N := by
  obtain ⟨T, hT⟩ := hSyl
  have hcoreK : pCore p G ≤ K := by
    rw [← hT]
    exact Subgroup.map_subtype_le _
  have hcoreN : pCore p N = (pCore p G).subgroupOf N := by
    apply le_antisymm
    · apply Subgroup.map_le_iff_le_comap.mp
      exact le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,
        (pCore_isPGroup (p := p) (G := N)).map N.subtype⟩
    · exact le_sSup ⟨inferInstance,
        (pCore_isPGroup (p := p) (G := G)).comap_of_injective N.subtype
          N.subtype_injective⟩
  have hcoreKN : pCore p N ≤ K.subgroupOf N := by
    rw [hcoreN]
    exact Subgroup.comap_mono hcoreK
  have hTnormal : (T : Subgroup K).Normal := by
    have hEq : (T : Subgroup K) = (pCore p G).subgroupOf K := by
      rw [← hT]
      exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective _).symm
    rw [hEq]
    infer_instance
  have hbound : ∀ R : Subgroup (K.subgroupOf N), IsPGroup p R →
      R.map (K.subgroupOf N).subtype ≤ pCore p N := by
    intro R hR
    let RG : Subgroup G := (R.map (K.subgroupOf N).subtype).map N.subtype
    have hRGK : RG ≤ K := by
      rintro x ⟨n, ⟨r, hr, rfl⟩, rfl⟩
      exact r.property
    have hRGp : IsPGroup p RG :=
      (hR.map (K.subgroupOf N).subtype).map N.subtype
    have hRKp : IsPGroup p (RG.subgroupOf K) :=
      hRGp.comap_of_injective K.subtype K.subtype_injective
    have hRKT : RG.subgroupOf K ≤ (T : Subgroup K) := by
      let _ : (T : Subgroup K).Normal := hTnormal
      have heq := T.is_maximal'
        (hRKp.to_sup_of_normal_right T.isPGroup') le_sup_right
      exact (le_sup_left : RG.subgroupOf K ≤ RG.subgroupOf K ⊔ (T : Subgroup K)).trans
        heq.le
    have hRGcore : RG ≤ pCore p G := by
      rw [← hT, ← Subgroup.map_subgroupOf_eq_of_le hRGK]
      exact Subgroup.map_mono hRKT
    rw [hcoreN]
    exact Subgroup.map_le_iff_le_comap.mp hRGcore
  let U : Subgroup (K.subgroupOf N) := (pCore p N).subgroupOf (K.subgroupOf N)
  have hUp : IsPGroup p U :=
    (pCore_isPGroup (p := p) (G := N)).comap_of_injective
      (K.subgroupOf N).subtype (K.subgroupOf N).subtype_injective
  let U' : Sylow p (K.subgroupOf N) :=
    { U with
      isPGroup' := hUp
      is_maximal' := by
        intro R hR hUR
        exact le_antisymm (Subgroup.map_le_iff_le_comap.mp (hbound R hR)) hUR }
  refine ⟨U', ?_⟩
  exact Subgroup.map_subgroupOf_eq_of_le hcoreKN
