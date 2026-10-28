module

public import Stellmacher.OmegaOneCenterMap
public import Theory.GroupTheory.NormalClosureSupplement
public import BenderSuzuki.External.Huppert.IV.Basic

/-!
# Comparing V across a normal Sylow supplement

Suppose `E` is normal in `G`, `S` is Sylow in `G`, and `Q` is
Sylow in `E`. If `ES = G`, the image of `Q` lies in `S`, contains
`Ω₁(Z(S))`, and is normalized by `S`, then `vSubgroup S` lies in
the ambient image of `vSubgroup Q`.

The central involutions of `S` lie in `Ω₁(Z(Q))`. The latter subgroup
is normalized by `S`, since it is characteristic in the normalized
image of `Q`. Thus taking its normal closure in `G` gives the same
result as taking it in `E` and mapping back. The injective omega-center
map theorem identifies this closure with `vSubgroup Q`.

This is the normal-closure comparison required for the application of
(2.3) to `E = O²(Pstar)O₂(C)` in Stellmacher (4.6).
Source: `refs/latex/stellmacher-n-group.tex`, second paragraph of (4.6).
-/

namespace Stellmacher.SectionTwo

/-- The ambient Sylow's central-involution closure lies in the closure for
a normalized Sylow subgroup of a normal supplement. -/
public theorem vSubgroup_le_map_of_normal_supplement
    {G : Type*} [Group G] (E : Subgroup G) [E.Normal]
    (S : Sylow 2 G) (Q : Sylow 2 E)
    (hgen : E ⊔ (S : Subgroup G) = ⊤)
    (hQS : (Q : Subgroup E).map E.subtype ≤ (S : Subgroup G))
    (hZQ : zSubgroup S ≤ (Q : Subgroup E).map E.subtype)
    (hSN : (S : Subgroup G) ≤
      Subgroup.normalizer (((Q : Subgroup E).map E.subtype : Subgroup G) : Set G)) :
    vSubgroup S ≤ (vSubgroup Q).map E.subtype := by
  let QG : Subgroup G := (Q : Subgroup E).map E.subtype
  let W : Subgroup G := omegaOneCenterAmbient QG
  have hZW : zSubgroup S ≤ W := by
    intro z hz
    obtain ⟨_hzS, hzpow, hzcent⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hz
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hZQ hz, hzpow, fun q hq ↦ hzcent q (hQS hq)⟩
  have hSNW : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := by
    let K : Subgroup QG :=
      (omega₁ (Subgroup.center QG) (p := 2)).map (Subgroup.center QG).subtype
    let _ : (omega₁ (Subgroup.center QG) (p := 2)).Characteristic :=
      omega₁_characteristic (Subgroup.center QG)
    let _ : K.Characteristic := inferInstance
    exact hSN.trans
      (BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic QG K)
  have hWmap : W = (omegaOneCenterAmbient (Q : Subgroup E)).map E.subtype :=
    omegaOneCenterAmbient_map_injective E.subtype E.subtype_injective (Q : Subgroup E)
  have hWE : W ≤ E := by
    rw [hWmap]
    exact Subgroup.map_subtype_le _
  have hWsub : W.subgroupOf E = omegaOneCenterAmbient (Q : Subgroup E) := by
    rw [hWmap]
    exact Subgroup.comap_map_eq_self_of_injective E.subtype_injective _
  calc
    vSubgroup S ≤ Subgroup.normalClosure (W : Set G) := Subgroup.normalClosure_mono hZW
    _ = (Subgroup.normalClosure (W.subgroupOf E : Set E)).map E.subtype :=
      Subgroup.normalClosure_eq_map_of_normal_supplement E (S : Subgroup G) W hgen hWE hSNW
    _ = (vSubgroup Q).map E.subtype := by rw [hWsub]; rfl

end Stellmacher.SectionTwo
