module
public import Theory.GroupTheory.RealElementInvolutionCentralizer
public import Theory.Mathieu.M22.Properties.SevenNonreal
public import Theory.SpecificGroups.Janko4.Model.SevenCentralizerBounds
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Placement
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension

/-!
# Nonreal seven-elements and binary automizer exclusion in J4

The certified symmetric-linear subgroup makes every seven-centralizer even.
A real seven would therefore have an inverter in an involution centralizer.
Both full native involution centralizers map onto Aut(M22) with kernels of
orders 24576 and 2048, coprime to seven. Their images would be real sevens,
contradicting the native Mathieu cocode trace obstruction.

The full automizers of PSL3(2) and PSL4(2) contain real sevens. Coprime
lifting consequently excludes either automizer as a two-core quotient of
any subgroup of the actual J4 carrier. No upper bound on an ambient
seven-centralizer and no full Sylow placement are needed.

Source: ATLAS J4 classes 7A--7B and its two involution centralizers;
Aschbacher--Smith 12.1.1, printed p.788. The actual matrix quotients and
permutation/cocode certificates retain their imported source attribution.
-/

public noncomputable section
open Subgroup
namespace Janko4.SevenNonreal
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
open Sporadic.Mathieu
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem not_real_of_hom {G : Type*} [Group G] [Finite G]
    (f : G →* MulAut M22) (hk : Nat.Coprime 7 (Nat.card f.ker))
    (x : G) (hx : orderOf x = 7) : ¬ IsConj x x⁻¹ := by
  have hp : IsPGroup 7 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hx,pow_one])
  have hi := injective_comp_subtype_of_coprime_ker f hk (zpowers x) hp
  have ho := orderOf_injective (f.comp (zpowers x).subtype) hi
    (⟨x,mem_zpowers x⟩ : zpowers x)
  change orderOf (f x) = orderOf (⟨x,mem_zpowers x⟩ : zpowers x) at ho
  rw [←Subgroup.orderOf_coe,hx] at ho
  intro hr
  exact Sporadic.Mathieu.SevenNonreal.aut_m22_not_real (f x) ho
    (by simpa only [map_inv] using f.map_isConj hr)

private theorem first_not_real (x : InvolutionCentralizers.First.centralizer)
    (hx : orderOf x = 7) : ¬ IsConj x x⁻¹ := by
  open InvolutionCentralizers.First.QuotientExtension in
  let f := centralizerQuotientEquivAut.toMonoidHom.comp (QuotientGroup.mk' R)
  have hf : Function.Surjective f :=
    InvolutionCentralizers.First.QuotientExtension.centralizerQuotientEquivAut.surjective.comp
      (QuotientGroup.mk'_surjective _)
  have ha : Nat.card (MulAut M22) = 887040 :=
    (Nat.card_congr MathieuCode.m22PairStabilizerEquivAut.toEquiv).symm.trans
      MathieuCode.m22PairStabilizer_card
  have hc := f.ker.card_mul_index
  rw [index_ker,f.range_eq_top_of_surjective hf,card_top,ha,
    OuterReduction.OddIndex.modelCentralizer_card] at hc
  have hk : Nat.card f.ker = 24576 := by omega
  exact not_real_of_hom f (by rw [hk]; decide) x hx

private theorem second_not_real (x : InvolutionCentralizers.Second.ambientCentralizer)
    (hx : orderOf x = 7) : ¬ IsConj x x⁻¹ := by
  apply not_real_of_hom InvolutionCentralizers.Second.ambientExtension.rightHom _ x hx
  change Nat.Coprime 7 (Nat.card InvolutionCentralizers.Second.ambientKernel)
  rw [InvolutionCentralizers.Second.ambientKernel_card]
  decide

/-- The proved even seven-centralizer and the two full involution centralizers
exclude real seven-elements in the native J4 carrier. -/
theorem not_real (x : Janko4.Model) (hx : orderOf x = 7) : ¬ IsConj x x⁻¹ := by
  intro hr
  have heven : 2 ∣ Nat.card (centralizer (zpowers x : Set Janko4.Model)) :=
    (by decide : 2 ∣ 840).trans (SevenCentralizerBounds.seven_centralizer_divisible x hx)
  obtain ⟨z,a,hz,hxz,haz,ha⟩ := Theory.GroupTheory.real_element_in_involution_centralizer x hr heven
  let y : centralizer ({z} : Set Janko4.Model) := ⟨x,hxz⟩
  have hy : orderOf y = 7 := (Subgroup.orderOf_coe y).symm.trans hx
  have hyr : IsConj y y⁻¹ := isConj_iff.mpr ⟨⟨a,haz⟩,Subtype.ext ha⟩
  rcases InvolutionCentralizers.centralizer_equiv_first_or_second z hz with h | h
  · obtain ⟨e⟩ := h
    exact first_not_real (e y) ((e.orderOf_eq y).trans hy)
      (by simpa only [map_inv,MulEquiv.coe_toMonoidHom] using e.toMonoidHom.map_isConj hyr)
  · obtain ⟨e⟩ := h
    exact second_not_real (e y) ((e.orderOf_eq y).trans hy)
      (by simpa only [map_inv,MulEquiv.coe_toMonoidHom] using e.toMonoidHom.map_isConj hyr)

/-- Neither full binary point automizer can be a two-core quotient of a J4 subgroup. -/
theorem no_binary_automizer_section
    (n : ℕ) (hn : n = 3 ∨ n = 4) (H : Subgroup Janko4.Model)
    (e : (H ⧸ pCore 2 H) ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) : False := by
  obtain ⟨y,hy,hr⟩ := BinaryLinear.OuterCyclic.aut_binary_real_seven n hn
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : Nat.Coprime 7 (Nat.card f.ker) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    obtain ⟨m,hm⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [hm]
    exact (by decide : Nat.Coprime 7 2).pow_right m
  obtain ⟨x,hx,_,hreal⟩ := f.exists_real_prime_lift hf hk y hy hr
  apply not_real (x : Janko4.Model) (by rw [Subgroup.orderOf_coe]; exact hx)
  exact H.subtype.map_isConj hreal
end Janko4.SevenNonreal
