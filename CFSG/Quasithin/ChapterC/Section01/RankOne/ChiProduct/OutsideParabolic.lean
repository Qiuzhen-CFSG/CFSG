module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Selection
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic
/-!
# An escaping minimal parabolic in characteristic two

Characteristic two and a proper control overgroup force the Sylow subgroup
to be nontrivial. Its normalizer lies in control, so the general
normalizer-plus-minimal-parabolics generation theorem produces an escaping
minimal parabolic. The conclusion retains the actual internal Sylow subgroup.
No solvability hypothesis is used.

Source: Aschbacher–Smith B.6.5–6 and C.1.28, printed pp.113,133.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct
variable {G : Type*} [Group G] [Finite G]

theorem exists_minimalParabolic_outside_control
    (T : Sylow 2 G) (hf : generalizedFitting G = pCore 2 G)
    (M : Subgroup G) (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M)
    (hM : M ≠ ⊤) :
    ∃ (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H),
      ChapterB.IsMinimalParabolicOver (T.subtype hTH) ⊤ ∧ ¬ H ≤ M := by
  have hT : (T : Subgroup G) ≠ ⊥ := by
    intro ht
    have hQ : pCore 2 G = ⊥ := le_bot_iff.mp (ht ▸ pCore_isPGroup.le_sylow_of_normal T)
    have hc := (ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf
    rw [hQ] at hc
    apply hM
    apply top_unique
    intro x _
    have hx : x ∈ (⊥ : Subgroup G) := hc (by
      intro y hy
      have hy1 : y = 1 := hy
      rw [hy1,mul_one,one_mul])
    exact (show (⊥ : Subgroup G) ≤ M from bot_le) hx
  have hNM := (normalizer_le_characteristicNormalizerClosure_self
    (T : Subgroup G) hT).trans hcpu
  have hex : ∃ H : Subgroup G, ChapterB.IsMinimalParabolicOver T H ∧ ¬ H ≤ M := by
    by_contra! hn
    have hh := sup_le (sSup_le hn) hNM
    change sSup {P | ChapterB.IsMinimalParabolicOver T P} ⊔
      normalizer (T : Set G) ≤ M at hh
    rw [ChapterB.minimalParabolics_sup_normalizer T] at hh
    exact hM (top_unique hh)
  obtain ⟨H,hH,hout⟩ := hex
  have hTH := hH.1.1.le
  refine ⟨H,hTH,?_,hout⟩
  apply (ChapterB.isMinimalParabolicOver_top_iff _).mpr
  have hu := Solvable.uniqueMaximalContaining_of_minimalParabolic T H hH
  obtain ⟨N,hN,hTN,hn⟩ := (uniqueMaximalContaining_top_iff _).mp hu
  refine ⟨⟨N,⟨hN,hTN⟩,?_⟩,?_⟩
  · intro A hA
    exact hn A hA.1 hA.2
  · intro ht
    exact hH.2 ((normal_subgroupOf_iff_le_normalizer hTH).mp ht)
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct
