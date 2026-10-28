module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.ResidualCoordinates.SourceMarking
public import Theory.GroupAction.MaximalCosetOrbit
public import Theory.Representation.PSL3Two.NaturalDualMarking.SylowFixed

/-!
# Recovering the original natural--dual seed

The original plane generator has a nonzero component in the natural support:
otherwise the Sylow element exchanging the supports forces both components
into the central line, and the plane would generate only the fixed factor.
Separation makes this component fixed by the same local Sylow as the chosen
suitable u. The unique nonzero fixed vector of the point-parabolic Sylow
then identifies the two modulo Z. Thus the original generator is u*b*c
modulo Z, for b in the dual support and c in the fixed factor.

The genuine paired sections, exchanged supports and fixed-factor decomposition
are the explicit 14.6.22--23 inputs from qt-e-suitable-component-supports.
The component exclusions and final marking remain with
qt-e-suitable-component-marking; suitable-choice assembly remains with
qt-e-suitable-existence. No seed projection or replacement choice of u is
assumed here.

Source: Aschbacher--Smith, 14.6.22--24, printed pp.1038--1042, especially
the decomposition of the same plane generator in the last paragraph on p.1042.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
variable {G : Type*} [Group G] [Finite G]
variable {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)

omit [Finite G] in
private theorem support_fixed_factor_normalized (C : Subgroup G) (hZC : D.V₁ ≤ C)
    (hfixed : ∀ x ∈ D.H, ∀ c ∈ C, ⁅c,x⁆ ∈ D.V₁) :
    D.H ≤ normalizer (C : Set G) := by
  apply le_normalizer_iff.mpr
  intro x hx c hc
  have hh := C.mul_mem (C.inv_mem (hZC (hfixed x hx c hc))) hc
  simpa [commutatorElement_def,mul_assoc] using hh

include h in
/-- The exchanged supports and generation by the original plane force its
natural projection to be nonzero modulo the central line. -/
theorem seed_natural_factor_not_mem_line
    (hplus : D.Vplus = D.V) (hcard : Nat.card D.V = 4)
    (A B C : Subgroup G) (hAU : A ≤ D.UH) (hCU : C ≤ D.UH)
    (hZA : D.V₁ ≤ A) (hZC : D.V₁ ≤ C)
    (hsep : A ⊓ (B ⊔ C) ≤ D.V₁)
    (hfixed : ∀ x ∈ D.H, ∀ c ∈ C, ⁅c,x⁆ ∈ D.V₁)
    (s : G) (hs : s ∈ (D.T : Subgroup G))
    (hsB : B.map (MulAut.conj s).toMonoidHom = A)
    (u : G) (huA : u ∈ A) (huZ : u ∉ D.V₁)
    (a b c v : G) (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ C)
    (hv : v ∈ D.V) (hvZ : v ∉ D.V₁) (he : v = a*b*c) :
    a ∉ D.V₁ := by
  intro haZ
  have hVU : D.V ≤ D.UH := by rw [←hplus]; exact le_conjugateSpanBy _ _
  have hseed : v * (a*b*c)⁻¹ ∈ D.V₁ := by rw [he,mul_inv_cancel]; exact D.V₁.one_mem
  have hsP : s ∈ suitableQuotientCentralizer h a := by
    refine ⟨hs,?_⟩
    apply (h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H (hAU ha)))).mpr
    refine ⟨h.T_le_H hs,?_⟩
    intro z hz
    have hsz : Commute z s := h.H_centralizes (h.T_le_H hs) z ((zpowers_le.mpr haZ) hz)
    rw [hsz.commutator_eq]
    exact D.V₁.one_mem
  have hbfix := seed_dual_factor_fixed h hcard hVU C hCU hfixed a b c v
    (hAU ha) hc hv hseed s hsP
  have hbsA : (MulAut.conj s) b ∈ A := hsB ▸ mem_map_of_mem _ hb
  have hbA : b ∈ A := by
    have hh := A.mul_mem (hZA hbfix) hbsA
    simpa [commutatorElement_def,MulAut.conj_apply,mul_assoc] using hh
  have hbZ := hsep ⟨hbA,(show B ≤ B ⊔ C from le_sup_left) hb⟩
  have hvC : v ∈ C := by
    rw [he]
    exact C.mul_mem (C.mul_mem (hZC haZ) (hZC hbZ)) hc
  have hi : D.V₁.relIndex D.V = 2 := by
    have hh := (D.V₁.subgroupOf D.V).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (h.point_lt.le.trans h.plus_le)).toEquiv,
      h.point_card,hcard] at hh
    change 2 * D.V₁.relIndex D.V = 4 at hh
    omega
  have hVC : D.V ≤ C := by
    rw [←sup_zpowers_eq_of_relIndex_prime (h.point_lt.le.trans h.plus_le)
      Nat.prime_two hi hv hvZ]
    exact sup_le hZC (zpowers_le.mpr hvC)
  have hUC : D.UH ≤ C := by
    change conjugateSpanBy D.Vplus D.H ≤ C
    rw [hplus]
    exact conjugateSpanBy_le hVC (support_fixed_factor_normalized C hZC hfixed)
  exact huZ (hsep ⟨huA,(show C ≤ B ⊔ C from le_sup_right) (hUC (hAU huA))⟩)

omit [Finite G] in
private theorem separated_product_fixed_left
    (A B Z : Subgroup G) (hn : A ≤ normalizer (B : Set G))
    (hZB : Z ≤ B) (hsep : A ⊓ B ≤ Z)
    (a b x : G) (ha : a ∈ A) (hb : b ∈ B)
    (hxA : x ∈ normalizer (A : Set G)) (hxB : x ∈ normalizer (B : Set G))
    (hfix : ⁅a*b,x⁆ ∈ Z) : ⁅a,x⁆ ∈ Z := by
  have hcA : ⁅a,x⁆ ∈ A := by
    have hh := A.mul_mem ha (A.inv_mem ((hxA a).mp ha))
    simpa [commutatorElement_def,mul_assoc] using hh
  have hcB : ⁅b,x⁆ ∈ B := by
    have hh := B.mul_mem hb (B.inv_mem ((hxB b).mp hb))
    simpa [commutatorElement_def,mul_assoc] using hh
  apply hsep ⟨hcA,?_⟩
  have hm : a*⁅b,x⁆*a⁻¹ ∈ B := (hn ha _).mp hcB
  have he : ⁅a,x⁆ = (a*⁅b,x⁆*a⁻¹)⁻¹ * ⁅a*b,x⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul]
    group
  rw [he]
  exact B.mul_mem (B.inv_mem hm) (hZB hfix)

include h in
/-- Separation preserves fixation of the natural projection when the actor
normalizes both supports and fixes the original plane modulo its line. -/
theorem seed_natural_factor_fixed
    (hcard : Nat.card D.V = 4) [IsMulCommutative D.UH]
    (A B C : Subgroup G) (hAU : A ≤ D.UH) (hBU : B ≤ D.UH) (hCU : C ≤ D.UH)
    (hZC : D.V₁ ≤ C) (hsep : A ⊓ (B ⊔ C) ≤ D.V₁)
    (hfixed : ∀ x ∈ D.H, ∀ c ∈ C, ⁅c,x⁆ ∈ D.V₁)
    (a b c v x : G) (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ C)
    (hv : v ∈ D.V) (he : v = a*b*c) (hx : x ∈ (D.T : Subgroup G))
    (hxA : x ∈ normalizer (A : Set G)) (hxB : x ∈ normalizer (B : Set G)) :
    ⁅a,x⁆ ∈ D.V₁ := by
  have hn : A ≤ normalizer ((B ⊔ C : Subgroup G) : Set G) :=
    (Subgroup.centralizer_le_normalizer _).trans' <|
      (centralizer_le (show B ⊔ C ≤ D.UH from sup_le hBU hCU)).trans' <|
        (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans' hAU
  have hxC := support_fixed_factor_normalized C hZC hfixed (h.T_le_H hx)
  have hxBC := normalizer_inf_normalizer_le_normalizer_sup B C ⟨hxB,hxC⟩
  apply separated_product_fixed_left A (B ⊔ C) D.V₁ hn (hZC.trans le_sup_right)
    hsep a (b*c) x ha (mul_mem_sup hb hc) hxA hxBC
  rw [←mul_assoc,←he]
  exact plane_line_commutator D.V D.V₁ (D.T : Subgroup G)
    (h.point_lt.le.trans h.plus_le) hcard h.point_card h.T_normalizes_V h.normalizes_point
    (commutator_mem_commutator hv hx)

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair

namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Matrix.PSL3Two.NaturalDualMarking
variable {G : Type*} [Group G] [Finite G]

/-- Construct the seed factors for the original suitable u from the same
natural/dual action and the original plane, without a seed-marking premise. -/
theorem source_exists_natural_dual_seed
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (A B C : Subgroup G)
    (hAU : A ≤ conjugateSpanBy (localModule T M) Mc)
    (hBU : B ≤ conjugateSpanBy (localModule T M) Mc)
    (hCU : C ≤ conjugateSpanBy (localModule T M) Mc)
    (hZC : centralInvolutions T ≤ C)
    (hsep : A ⊓ (B ⊔ C) ≤ centralInvolutions T)
    (hpair : ∀ x ∈ Mc, A.map (MulAut.conj x).toMonoidHom = A ∨
      A.map (MulAut.conj x).toMonoidHom = B)
    (q : (Mc ⊓ normalizer (A : Set G) : Subgroup G) →* BinaryLinear.GL Space)
    (hq : Function.Surjective q)
    (n : BinaryConjugationSection (Mc ⊓ normalizer (A : Set G)) A (centralInvolutions T)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp q))
    (d : BinaryConjugationSection (Mc ⊓ normalizer (A : Set G)) B (centralInvolutions T)
      (Representation.dual (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp q)))
    (hcover : ∀ v ∈ conjugateSpanBy (localModule T M) Mc,
      ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, v = a*b*c)
    (hfixed : ∀ x ∈ Mc, ∀ c ∈ C, ⁅c,x⁆ ∈ centralInvolutions T)
    (s : G) (hs : s ∈ (T : Subgroup G))
    (hsB : B.map (MulAut.conj s).toMonoidHom = A)
    (u : G) (huA : u ∈ A)
    (hu : ComponentSupports.Suitable
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) Mc u) :
    ∃ b ∈ B, ∃ c ∈ C, ∃ v ∈ localModule T M,
      v ∉ centralInvolutions T ∧ v*(u*b*c)⁻¹ ∈ centralInvolutions T := by
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let P := h.kernel (zpowers u)
  have huz : u ∉ centralInvolutions T := by
    intro hz
    apply hu.2.2.2.1
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (h.H_centralizes (pCoreIn_le 2 Mc hx) u hz).symm
  obtain ⟨v,hv,hvZ⟩ := SetLike.exists_of_lt h.point_lt
  obtain ⟨a,ha,b,hb,c,hc,he⟩ := hcover v ((le_conjugateSpanBy _ _) hv)
  have haZ := seed_natural_factor_not_mem_line h rfl hcard A B C hAU hCU
    n.kernel_le hZC hsep hfixed s hs hsB u huA huz a b c v ha hb hc hv hvZ he
  have hsep' : A ⊓ B ≤ centralInvolutions T :=
    (inf_le_inf_left A (show B ≤ B ⊔ C from le_sup_left)).trans hsep
  obtain ⟨_,_,action,hpoint,hactor⟩ := source_parabolic_action_of_natural_pair
    hG T hempty hM hunique hmany hcard e hab A B C hsep' hpair q hq n d hcover hfixed u huA hu
  let := h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  have hu2 : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu.1
  have hPL : P ≤ Mc ⊓ normalizer (A : Set G) :=
    point_kernel_le_support_normalizer h A B (n.section_le.trans inf_le_left)
      n.kernel_le hsep' hpair u huA huz hu2
  have hBP : B ≤ P := by
    intro x hx
    apply (mem_point_kernel_iff h u (h.UH_le_H hu.1) hu2 x).mpr
    refine ⟨h.UH_le_H (hBU hx),?_⟩
    have hcU : conjugateSpanBy (localModule T M) Mc ≤
        centralizer (conjugateSpanBy (localModule T M) Mc : Set G) :=
      le_centralizer_iff_isMulCommutative.mpr inferInstance
    have hxu : Commute u x := hcU (hBU hx) u hu.1
    rw [hxu.commutator_eq]
    exact (centralInvolutions T).one_mem
  have hr : (q.comp (inclusion hPL)).range =
      MulAction.stabilizer (BinaryLinear.GL Space) (n.coordinates ⟨u,huA⟩).toAdd := by
    have hact : q.comp (inclusion hPL) = action.actor := by
      apply MonoidHom.ext
      intro x
      exact (hactor x (hPL x.property)).symm
    rw [hact,action.image,hpoint]
  obtain ⟨t,ht,f,hf,hcompat,d',_⟩ := normalized_action q d hPL hBP
    (n.coordinates ⟨u,huA⟩).toAdd
    (fun he => huz ((n.coordinates_eq_one_iff ⟨u,huA⟩).mp he)) hr
  obtain ⟨S,hS⟩ := suitable_quotient_sylow_of_local_normalizer h u Mc le_rfl hu.2.2.2.2.2
  have hfix : ∀ x : P, x ∈ (S : Subgroup P) →
      BinaryLinear.OuterCyclic.slEquivLinear 3 (f x) (t (n.coordinates ⟨a,ha⟩).toAdd) =
        t (n.coordinates ⟨a,ha⟩).toAdd := by
    intro x hx
    have hxT : (x : G) ∈ (T : Subgroup G) := by
      have hxS : (x : G) ∈ suitableQuotientCentralizer h u := by
        rw [←hS]
        exact ⟨x,hx,rfl⟩
      exact hxS.1
    have hafix := seed_natural_factor_fixed h hcard A B C hAU hBU hCU hZC hsep
      hfixed a b c v x ha hb hc hv he hxT (hPL x.property).2
      (d.normalized (hPL x.property))
    rw [hcompat,actorEquiv_apply]
    exact congrArg t ((n.fixed_coordinate_iff_commutator_mem (inclusion hPL x) ⟨a,ha⟩).mpr hafix)
  have hacoord : n.coordinates ⟨a,ha⟩ = n.coordinates ⟨u,huA⟩ := by
    rcases natural_sylow_fixed_zero_or_point f hf S _ hfix with hz | hp
    · exact (haZ ((n.coordinates_eq_one_iff ⟨a,ha⟩).mp (t.map_eq_zero_iff.mp hz))).elim
    · exact t.injective (hp.trans ht.symm)
  have hauZ : a*u⁻¹ ∈ centralInvolutions T := by
    apply (n.coordinates_eq_one_iff (⟨a,ha⟩ * ⟨u,huA⟩⁻¹)).mp
    rw [map_mul,map_inv,hacoord,mul_inv_cancel]
  refine ⟨b,hb,c,hc,v,hv,hvZ,?_⟩
  convert hauZ using 1
  rw [he]
  group

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
