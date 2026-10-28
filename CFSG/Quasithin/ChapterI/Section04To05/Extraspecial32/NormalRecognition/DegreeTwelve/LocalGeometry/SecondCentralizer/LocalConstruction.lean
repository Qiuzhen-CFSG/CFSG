module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.Models
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.LocalConstruction.Inputs
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.LocalConstruction.Control
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.LocalConstruction.SylowPlacement
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.LocalConstruction.AmalgamModel
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.Orbits

/-!
# Assembly of the local second-centralizer seed

The long core orbit proves `C_H(t) = C_Q(t)`. The latter lies in the literal
join `⟨Q,gQg⁻¹⟩`, so the local marked model contains the full centralizer of
`z` inside `C_G(t)`. The fusion-sensitive normalizer argument then gives
Sylow order sixteen and centralizer containment for every first-class element.

The final assembly constructs the orbit profile from relative quaternion
normality and the marked local isomorphism from the fusion eight and selected
configuration. Thus the original local hypotheses supply every field of
`LocalSeed`, including the marking of the original ambient involution `t`.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 2.7, 4.1 and the opening of 4.2.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z t : G}

/-- Application to the selected literal core intersection. The two remaining
local producers have separate contracts; no full-centralizer classification,
ambient order, or mixed-pair count is used in this assembly. -/
public theorem nonempty_localSeed_of_localModel_of_orbits (h : Hypotheses z)
    (d : FusionEightData z) (a : SelectedFusionData h)
    (o : Census.OrbitData z a.u) (m : LocalModelData z t a.g)
    (htE : t ∈ coreIntersection z a.g) (ht : orderOf t = 2)
    (hnt : ¬ IsConj z t) : Nonempty (LocalSeed z t) := by
  let L := localCentralizer z t a.g
  let f : Model 4 →* Centralizer t := L.subtype.comp m.equiv.symm.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp m.equiv.symm.injective
  have hcentral : f (centralInvolution 4) = distinguished t := Subtype.ext m.central
  have hfirst (x : Model 4) : IsConj z (f x : G) ↔ FirstClass x := by
    change IsConj z ((m.equiv.symm x : Centralizer t) : G) ↔ FirstClass x
    simpa only [MulEquiv.apply_symm_apply] using m.first (m.equiv.symm x)
  have hzI : z ∈ Centralizer t := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (coreInG_le z htE.1)).symm
  let zI : Centralizer t := ⟨z, hzI⟩
  have hzL : zI ∈ L := (show coreInG z ≤ coreInG z ⊔ conjugateCore z a.g
    from le_sup_left) h.involution_mem_coreInG
  let zL : L := ⟨zI, hzL⟩
  let w := m.equiv zL
  have hfw : f w = zI := congrArg L.subtype (m.equiv.symm_apply_apply zL)
  have hw : FirstClass w := (m.first zL).mp (IsConj.refl z)
  apply nonempty_localSeed_of_one_centralizer f hf hcentral hfirst w hw
  intro y hy
  have hyz : (y : G) ∈ Centralizer z := by
    rw [hfw] at hy
    exact mem_centralizer_singleton_iff.mpr
      (congrArg (Centralizer t).subtype (mem_centralizer_singleton_iff.mp hy))
  have hycommon : (y : G) ∈ Centralizer z ⊓ Centralizer t := ⟨hyz, y.property⟩
  rw [commonCentralizer_eq_core_of_orbits h d o htE.1 ht hnt] at hycommon
  have hyL : y ∈ L := (show coreInG z ≤ coreInG z ⊔ conjugateCore z a.g
    from le_sup_left) hycommon.1
  exact ⟨m.equiv ⟨y, hyL⟩, congrArg L.subtype (m.equiv.symm_apply_apply ⟨y, hyL⟩)⟩

/-- The local `C₂ × S₄` subgroup, Sylow placement, and first-class centralizer
control from source 4.1 and the opening of 4.2. Both local construction inputs
are discharged using the selected configuration and relative quaternion normality. -/
public theorem nonempty_localSeed (h : Hypotheses z) (hn : QuaternionSubgroupsNormal z)
    (d : FusionEightData z) (a : SelectedFusionData h) (t : G)
    (htE : t ∈ coreIntersection z a.g) (ht : orderOf t = 2) (hnt : ¬ IsConj z t)
    (hclasses : ∀ x : G, orderOf x = 2 → IsConj z x ∨ IsConj t x) :
    Nonempty (LocalSeed z t) := by
  obtain ⟨m⟩ := nonempty_localModelData h hn d a t htE ht hnt hclasses
  exact nonempty_localSeed_of_localModel_of_orbits h d a
    (Census.orbitData_of_quaternion_normal h hn d a) m htE ht hnt

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
