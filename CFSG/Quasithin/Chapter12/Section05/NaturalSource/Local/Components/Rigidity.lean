module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Actions
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components
public import Theory.GroupTheory.CComponent.QuasisimpleImageRigidity
/-!
# Rigidity of quasisimple containing components in the natural local cases

At i = 3 or 4 the actual residual has the full automorphism group on Vᵢ.
Thus it and any containing component have the same nontrivial action image.
The containing component's two-core lies in the original Sylow T, which
normalizes Lᵢ. The quasisimple supplement theorem then gives Kᵢ = Lᵢ when
Kᵢ/O₂(Kᵢ) is quasisimple. All subgroups and maps are restricted inside Gᵢ;
no ambient normality is substituted for relative normality.

The nonquasisimple alternative is excluded separately in Four and remains
an obligation in the i = 3 source branch.
Source: Aschbacher--Smith, proof of 12.5.3, printed p.818.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The natural-action cases of the source's quasisimple non-enlargement step. -/
theorem local_component_eq_of_quasisimple
    (i : ℕ) (hi : i = 3 ∨ i = 4) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi i))
    (hLK : s.marking.Li i ≤ K) [IsQuasisimple (K ⧸ pCore 2 K)] :
    s.marking.Li i = K := by
  have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
  let H := s.marking.Gi i
  let B := (s.marking.Li i).subgroupOf H
  let C := K.subgroupOf H
  let f : H →* MulAut (s.marking.Vi i) := (s.marking.Vi i).normalizerMonoidHom
  let e : C ≃* K := subgroupOfEquivOfLe hK.1
  let : IsQuasisimple (C ⧸ pCore 2 C) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  let : Nontrivial (MulAut (s.marking.Vi i)) := s.marking.localAut_nontrivial i hi
  have hf : Function.Surjective (f.comp B.subtype) := by
    intro α
    obtain ⟨l, hl⟩ := s.marking.LiAction_surjective i hi α
    exact ⟨⟨⟨l, s.marking.Li_le_Gi i l.property⟩, l.property⟩, hl⟩
  have hBf : B.map f = ⊤ := by
    rw [← range_subtype B, ← MonoidHom.range_comp]
    exact MonoidHom.range_eq_top.mpr hf
  have hCf : C.map f = ⊤ := top_unique (by
    rw [← hBf]
    exact map_mono (comap_mono hLK))
  have hT := s.sylow_le_Gi i hidx
  have hcT : C.pCoreIn 2 ≤ (T.subtype hT : Subgroup H) :=
    (pCoreIn_le_of_subnormal 2 hK.2.subnormal).trans
      (pCore_isPGroup.le_sylow_of_normal (T.subtype hT))
  have hn : pCore 2 C ≤ normalizer (B.subgroupOf C : Set C) := by
    intro x hx y
    exact s.sylow_normalizes_Li i hidx
      (hcT (mem_map_of_mem C.subtype hx)) (y : G)
  have he := Theory.GroupTheory.IsCComponent.eq_of_image_eq_of_twoCore_normalizes
    f hK.2 (comap_mono hLK)
    (hBf.trans hCf.symm) (hCf ▸ top_ne_bot) hn
  calc
    s.marking.Li i = ((s.marking.Li i).subgroupOf H).map H.subtype :=
      (map_subgroupOf_eq_of_le (s.marking.Li_le_Gi i)).symm
    _ = (K.subgroupOf H).map H.subtype := congrArg (map H.subtype) he
    _ = K := map_subgroupOf_eq_of_le hK.1

end SylowExteriorMarking

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
