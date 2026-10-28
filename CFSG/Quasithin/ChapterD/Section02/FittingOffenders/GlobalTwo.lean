module
public import Theory.Representation.BinaryTwoPlaneRecognition.OrderThirtySix
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.Defs
public import Theory.Representation.BinaryOffender.ComponentSum
public import Theory.GroupAction.SubgroupConjugation

/-!
# Exhausting the original actor in the two-support case

The literal addition map for the two marked order-three supports gives
complementary binary planes. Conjugation of the original factors transports
their moved spaces, so permutation of those factors preserves the union of
the planes. The faithful two-plane endpoint then makes any original subgroup
of order 36 the whole actor when the cubic ratio is greater than one.

This is the final index-two exclusion in source D.2.22, printed p.189. The
source assembly supplies the canonical support family, its ambient
permutation action, and the original subgroup RA of order 36.
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- D.2.22 on the original marked factors and their actual moved spaces. -/
theorem SupportFactors.eq_top_of_card_thirty_six
    (hf : Function.Injective ρ) {P : Subgroup G} (d : SupportFactors ρ P 2)
    (hperm : ∀ g : G, ∀ i : Fin 2, ∃ j, (d.ambient i).conjBy g = d.ambient j)
    (L : Subgroup G) (hL : Nat.card L = 36) (hlow : 1 < cubicRatio ρ) : L = ⊤ := by
  classical
  let U := fun i : Fin 2 => subspaceCommutator ρ ⊤ (d.ambient i)
  have hdis : Disjoint (U 0) (U 1) := by
    apply Submodule.disjoint_def.mpr
    intro v hv hw
    let f : (i : Fin 2) → U i := Pi.single 0 ⟨v,hv⟩
    let g : (i : Fin 2) → U i := Pi.single 1 ⟨v,hw⟩
    have he : (∑ i, (f i : V)) = ∑ i, (g i : V) := by
      simp [f,g,Fin.sum_univ_two]
    have hh := congrArg (fun x => ((x 0 : U 0) : V)) (d.add_bijective.1 he)
    simpa [f,g] using hh
  have hsum : U 0 ⊔ U 1 = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨w,hw⟩ := d.add_bijective.2 v
    have hw' : (w 0 : V) + (w 1 : V) = v := by simpa only [Fin.sum_univ_two] using hw
    exact Submodule.mem_sup.mpr ⟨w 0,(w 0).property,w 1,(w 1).property,hw'⟩
  have hcompl : IsCompl (U 0) (U 1) := ⟨hdis,codisjoint_iff.mpr hsum⟩
  have hmaps (g : G) (i : Fin 2) : ∃ j, (U i).map (ρ g) = U j := by
    obtain ⟨j,hj⟩ := hperm g i
    refine ⟨j,?_⟩
    change (subspaceCommutator ρ ⊤ (d.ambient i)).map (ρ g) = _
    rw [moved_map_conjugate]
    exact congrArg (fun K : Subgroup G => subspaceCommutator ρ ⊤ K) hj
  have hmove (g : G) (v : V) (hv : v ∈ U 0 ∨ v ∈ U 1) :
      ρ g v ∈ U 0 ∨ ρ g v ∈ U 1 := by
    obtain ⟨i,hi⟩ : ∃ i : Fin 2, v ∈ U i := by
      rcases hv with h|h
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
    obtain ⟨j,hj⟩ := hmaps g i
    have hh : ρ g v ∈ U j := hj ▸ Submodule.mem_map_of_mem hi
    fin_cases j
    · exact Or.inl hh
    · exact Or.inr hh
  have hunion (g : G) (v : V) :
      (ρ g v ∈ U 0 ∨ ρ g v ∈ U 1) ↔ (v ∈ U 0 ∨ v ∈ U 1) := by
    constructor
    · intro hv
      simpa only [ρ.inv_self_apply] using hmove g⁻¹ (ρ g v) hv
    · exact hmove g v
  exact Representation.BinaryTwoPlaneRecognition.eq_top_of_card_thirty_six ρ hf
    (U 0) (U 1) hcompl (d.support_dim 0) (d.support_dim 1) hunion L hL hlow

end CFSG.Quasithin.ChapterD.FittingConfigurations
