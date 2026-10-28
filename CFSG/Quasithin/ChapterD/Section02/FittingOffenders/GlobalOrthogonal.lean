module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.GlobalTwo
public import Theory.Representation.BinaryTwoPlaneRecognition.OrderThirtySix.Omega

/-!
# Marking the two support planes as the natural Ω⁺₄ module

The literal support-sum map gives two complementary binary planes. Their
permutation action embeds the original group in the isometry group of the
orthogonal sum of the two anisotropic plane forms. The S₃ × S₃ identification
from D.2.14 gives exponent dividing six. Together with cubic ratio greater
than one, this identifies the image with the genuine Siegel-generated
Ω-subgroup and retains the exact coordinate/action intertwining.

The exponent premise matters: another order-36 subgroup of the full
isometry group has cyclic Sylow subgroups of order four.
Source: Aschbacher–Smith D.2.22, case (5), printed p.189.
-/

public section
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
open Subgroup Representation.BinaryOffender
variable {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem SupportFactors.exists_isometry_embedding
    (hf : Function.Injective ρ) {P : Subgroup G} (d : SupportFactors ρ P 2)
    (hperm : ∀ g : G, ∀ i : Fin 2, ∃ j, (d.ambient i).conjBy g = d.ambient j) :
    ∃ (c : V ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
      (f : G →* OrthogonalFourBinary.TerminalLines.IsometryGroup),
      Function.Injective f ∧ ∀ g v, c (ρ g v) = (f g).val (c v) := by
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
  exact Representation.BinaryTwoPlaneRecognition.exists_isometry_embedding ρ hf
    (U 0) (U 1) hcompl (d.support_dim 0) (d.support_dim 1) hunion


open scoped ENNReal

theorem SupportFactors.exists_omega_coordinates [Finite G]
    (hf : Function.Injective ρ) {P : Subgroup G} (d : SupportFactors ρ P 2)
    (hperm : ∀ g : G, ∀ i : Fin 2, ∃ j, (d.ambient i).conjBy g = d.ambient j)
    (e₀ : G ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) (hlow : 1 < cubicRatio ρ) :
    ∃ (c : V ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
      (e : G ≃* OrthogonalFourBinary.omega),
      ∀ g v, c (ρ g v) = (e g).val.val (c v) := by
  obtain ⟨c,f,hf',hcoord⟩ := d.exists_isometry_embedding ρ hf hperm
  have hc3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_fin]
    decide
  have hcard : Nat.card G = 36 := by
    have hh := Nat.card_congr e₀.toEquiv
    rw [Nat.card_prod,hc3] at hh
    exact hh
  have hpow (x : Equiv.Perm (Fin 3)) : x ^ 6 = 1 := by
    simpa only [hc3] using (pow_card_eq_one' (x := x))
  have h6 (g : G) : g ^ 6 = 1 := by
    apply e₀.injective
    rw [map_pow,map_one]
    exact Prod.ext (hpow (e₀ g).1) (hpow (e₀ g).2)
  obtain ⟨e,_,he⟩ := Representation.BinaryTwoPlaneRecognition.exists_omega_equiv_of_exponent_six
    ρ c f hf' hcoord hcard h6 hlow
  exact ⟨c,e,he⟩

end CFSG.Quasithin.ChapterD.FittingConfigurations
