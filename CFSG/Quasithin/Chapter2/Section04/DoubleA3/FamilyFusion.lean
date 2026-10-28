module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.CoreFusion
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.PureFusion

/-!
# Six-point fusion on all four paired-cubic elementary subgroups

Once the core has order sixteen, its residual central factor vanishes.
The original outside conjugator then exchanges the two mixed elementary
subgroups. Conjugation preserves the size of an ambient class intersection,
so the core and first mixed-subgroup bounds cover the complete four-family.
This gives exactly the elementary-sixteen fusion input of the source37
factor argument, including elementary subgroups inside the Thompson group.

Source: Aschbacher–Smith 2.4.37, printed p.550.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
private theorem class_card_conjugate (A : Subgroup G) (i y : G) :
    Nat.card {a : A.map (MulAut.conj y).toMonoidHom // IsConj i (a : G)} =
      Nat.card {a : A // IsConj i (a : G)} := by
  let e := (MulAut.conj y).subgroupMap A
  have he (a : A) : IsConj i (a:G) ↔ IsConj i ((e a : A.map (MulAut.conj y).toMonoidHom) : G) := by
    have hh : IsConj (a:G) ((e a : A.map (MulAut.conj y).toMonoidHom) : G) :=
      isConj_iff.mpr ⟨y,rfl⟩
    exact ⟨fun h => h.trans hh,fun h => h.trans hh.symm⟩
  exact (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv he)).symm

namespace SourcePairCoordinates
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} (c : SourcePairCoordinates d T)

 theorem cross_conjugate_of_core_card (hQ : Nat.card (twoCore d.H)=16) :
    (((c.U₁ ⊔ c.V₂) ⊔ c.D).map (MulAut.conj c.x⁻¹).toMonoidHom) =
      (c.V₁ ⊔ c.U₂) ⊔ c.D := by
  have hD : c.D=⊥ := Subgroup.card_eq_one.mp (by have hh := c.core_card; rw [hQ] at hh; omega)
  have hs := FourModuleOrbit.square_fixes_modules c.orbit.toInputs ⟨c.x⁻¹,(T : Subgroup G).inv_mem c.x_mem⟩ 1
  have hV : c.V₂.map (MulAut.conj c.x⁻¹).toMonoidHom = c.U₂ := by
    change (c.U₂.conjBy c.x⁻¹).conjBy c.x⁻¹ = c.U₂
    rw [conjBy_conjBy,←pow_two]
    exact hs
  rw [hD,sup_bot_eq,sup_bot_eq,Subgroup.map_sup,hV]
end SourcePairCoordinates

namespace SourceCentralizerGeometry
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}
    (g : SourceCentralizerGeometry c)

 theorem family_fusion_bound (hQ : Nat.card (twoCore d.H)=16)
    (hcross : Nat.card {a : ((c.U₁ ⊔ c.V₂) ⊔ c.D : Subgroup G) // IsConj g.z₂ (a:G)} ≤6) :
    ∀ A ∈ elementaryAbelianMaxSubgroups ((d.S : Subgroup d.H).map d.H.subtype),
      Nat.card {a : A // IsConj g.z₂ (a:G)} ≤6 := by
  intro A hA
  rw [c.four_family] at hA
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hA
  rcases hA with rfl | rfl | rfl | rfl
  · exact g.core_fusion_bound hQ
  · rw [class_card_conjugate]
    exact g.core_fusion_bound hQ
  · exact hcross
  · rw [←c.cross_conjugate_of_core_card hQ,class_card_conjugate]
    exact hcross

 theorem elementary_sixteen_fusion (b : SourceComponentGeometry d) (hz : b.z=g.z₂)
    (hQ : Nat.card (twoCore d.H)=16)
    (hcross : Nat.card {a : ((c.U₁ ⊔ c.V₂) ⊔ c.D : Subgroup G) // IsConj g.z₂ (a:G)} ≤6) :
    SourceElementarySixteenFusion b := by
  apply b.elementarySixteenFusion_of_maximum_family
    ((d.S : Subgroup d.H).map d.H.subtype) (twoCore d.H)
    (sSup_le (fun _ h => h.1))
  · rw [c.four_family]
    exact Set.mem_insert _ _
  · exact hQ
  · rw [hz]
    exact g.family_fusion_bound hQ hcross
end SourceCentralizerGeometry
end CFSG.Quasithin.Chapter2.DoubleA3
