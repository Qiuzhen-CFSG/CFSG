module
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.PGroupCore
public import Mathlib.GroupTheory.PGroup
/-! # The two-core of a component-Sylow generated group
If a component K and a Sylow two-subgroup S generate G, the actual
S-conjugate orbit K₀ is normal. Its centralizer in S is normal in K₀S,
hence lies in O₂(G). Conversely each component centralizes the solvable
normal subgroup O₂(G), which lies in S. Thus C_S(K₀)=O₂(G), without
assuming K normal or requiring a catalogue or center computation.
Source: Aschbacher--Smith Notation 2.5.4, printed p.554. -/
public section
namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem IsComponent.sylow_centralizer_orbit_eq_pCore {K : Subgroup G}
    (hK : IsComponent G K) (S : Sylow 2 G) (hgen : K⊔(S:Subgroup G)=⊤) :
    (S:Subgroup G)⊓centralizer (componentOrbit K (S:Subgroup G):Set G)=pCore 2 G := by
  let D := componentOrbit K (S:Subgroup G)
  let Q := (S:Subgroup G)⊓centralizer (D:Set G)
  have hSD := le_normalizer_componentOrbit K (S:Subgroup G)
  have hSQ : (S:Subgroup G)≤normalizer (Q:Set G) := by
    intro s hs a
    exact and_congr ((S:Subgroup G).le_normalizer hs a)
      ((normalizer_le_normalizer_centralizer D (hSD hs)) a)
  have hN : Q.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le ((le_componentOrbit K (S:Subgroup G)).trans
      ((le_centralizer_iff.mp (show Q≤centralizer (D:Set G) from inf_le_right)).trans
        (centralizer_le_normalizer _))) hSQ
  have hQp : IsPGroup 2 Q := S.isPGroup'.to_le inf_le_left
  have hQC : Q≤pCore 2 G := le_sSup ⟨hN,hQp⟩
  have hDC : D≤centralizer (pCore 2 G:Set G) := by
    apply iSup_le
    intro s
    have := (pCore_isPGroup (p:=2) (G:=G)).isNilpotent
    exact (hK.map_conj (s:G)).le_centralizer_of_solvable_normal (pCore 2 G)
  exact le_antisymm hQC (le_inf (pCore_isPGroup.le_sylow_of_normal S)
    (le_centralizer_iff.mp hDC))
end Theory.GroupTheory
