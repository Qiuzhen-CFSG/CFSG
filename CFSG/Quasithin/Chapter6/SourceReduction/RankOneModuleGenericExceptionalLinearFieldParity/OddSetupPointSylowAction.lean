module
public import Theory.GroupAction.PrimitivePrimeSylowAction
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupCartanSylowAction

/-!
# The primitive-prime action on the original natural point

The Cartan acts faithfully on Z₁ = Ω₁Z(T) ∩ V. A primitive-prime Sylow
of this Cartan is already Sylow in Aut(Z₁), by the binary general linear
order calculation. Thus the stabilizer of Z₁ in any p-group containing
that Cartan Sylow is exactly its product with the pointwise centralizer,
with trivial intersection of these factors.

The literal L/O₂(L) action kernel preserves every Sylow subgroup of L.
The natural point generates V under L, so within that kernel point
invariance is equivalent to invariance of V itself. Neither assertion
assumes that a normalizer of L preserves the chosen module.

The actual full C_K Sylow is supplied by OddSetupSylowFactorization;
the Chapter12 consumer applies these results to that same Sylow and
chosen module. Full Sylow invariance, residual/global TI, and final parity
remain with qt-d-1222-linear-field-parity. The independent Suzuki premise
is retained there as solvability of the literal residual action kernel.
Source: Aschbacher–Smith, proof of 5.1.17, printed p.640
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H A B : Subgroup G} {n : ℕ}

/-- The original Cartan acts faithfully on the original natural point. -/
theorem fundamental_cartan_point_disjoint_centralizer
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n)) (hn : 0 < n)
    (hodd : Odd n) (hnat : IsNaturalModule L D.moduleSubgroup n)
    (c : CartanPair T L H A B) :
    Disjoint A (centralizer ((setup T L D.moduleSubgroup H A).V₁ : Set G)) := by
  let Z := (setup T L D.moduleSubgroup H A).V₁
  have hZne : Z ≠ ⊥ := by
    intro he
    have hc := fundamental_point_card D hTL hpsl hodd hnat
    change Nat.card Z = 2^n at hc
    rw [he,card_bot] at hc
    have hp : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
    omega
  apply disjoint_iff.mpr
  apply bot_unique
  intro a ha
  apply mem_bot.mpr
  by_contra hne
  let C := zpowers a
  have hCA : C ≤ A := zpowers_le.mpr ha.1
  have hCne : C ≠ ⊥ := by
    intro he
    exact hne (mem_bot.mp (he ▸ mem_zpowers a))
  have hCZ : C ≤ centralizer (Z : Set G) := zpowers_le.mpr ha.2
  have hZ : Z ≤ D.moduleSubgroup ⊓ centralizer (C : Set G) :=
    le_inf inf_le_right (le_centralizer_iff.mp hCZ)
  exact hZne (bot_unique (hZ.trans_eq (natural_cartan_subgroup_fixed_eq_bot c hnat C hCA hCne)))

/-- The primitive Cartan Sylow gives exactly the p-action of the point
stabilizer in any p-overgroup, on the unchanged selected module. -/
theorem fundamental_primitive_sylow_point_stabilizer
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n)) (hn : 0 < n)
    (hodd : Odd n) (hnat : IsNaturalModule L D.moduleSubgroup n)
    (c : CartanPair T L H A B) {p : ℕ} [Fact p.Prime]
    (ho : orderOf (2 : ZMod p) = n) (P : Subgroup G) (hP : IsPGroup p P)
    (R : Sylow p A) (hRP : (R : Subgroup A).map A.subtype ≤ P) :
    let Z := (setup T L D.moduleSubgroup H A).V₁
    P ⊓ normalizer (Z : Set G) =
      (R : Subgroup A).map A.subtype ⊔ (P ⊓ centralizer (Z : Set G)) ∧
    Disjoint ((R : Subgroup A).map A.subtype) (P ⊓ centralizer (Z : Set G)) := by
  let Z := (setup T L D.moduleSubgroup H A).V₁
  let := D.module_elementary
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_le (show Z ≤ D.moduleSubgroup from inf_le_right)
  have hAZ : A ≤ normalizer (Z : Set G) :=
    (c.left_le.trans (fundamental_point_normalizer D hTL hpsl hodd hnat).ge).trans inf_le_right
  let f := Z.normalizerMonoidHom.comp (inclusion hAZ)
  have hd := fundamental_cartan_point_disjoint_centralizer D hTL hpsl hn hodd hnat c
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply bot_unique
    intro a ha
    have hm : inclusion hAZ a ∈ Z.normalizerMonoidHom.ker := ha
    rw [normalizerMonoidHom_ker] at hm
    exact Subtype.ext (hd.le_bot ⟨a.property,hm⟩)
  exact ⟨primitive_torus_point_stabilizer Z A P hn ho
    (fundamental_point_card D hTL hpsl hodd hnat) hAZ hf
    (c.left_cyclic_and_card hTL hpsl).2 hP R hRP,
    hd.mono (map_subtype_le _) inf_le_right⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H A : Subgroup G} {n : ℕ}

private theorem left_quotient_kernel_normalizes_sylow (S : Sylow 2 L) :
    (normalizerQuotientAction L (pCore 2 L)).ker.map (normalizer (L : Set G)).subtype ≤
      normalizer ((S : Subgroup L).map L.subtype : Set G) := by
  rintro _ ⟨g,hg,rfl⟩
  let a := L.normalizerMonoidHom g
  let q := QuotientGroup.mk' (pCore 2 L)
  have he (l : L) : q (a l) = q l := by
    have hh := DFunLike.congr_fun hg (q l)
    change (pCore 2 L).quotientAut a (QuotientGroup.mk' (pCore 2 L) l) =
      QuotientGroup.mk' (pCore 2 L) l at hh
    simpa only [quotientAut_apply_mk] using hh
  have hle : (S : Subgroup L).map a.toMonoidHom ≤ S := by
    rintro _ ⟨l,hl,rfl⟩
    have hd : l⁻¹*a l ∈ pCore 2 L := QuotientGroup.eq.mp (he l).symm
    have hh := (S : Subgroup L).mul_mem hl (((pCore_isPGroup (p := 2) (G := L)).le_sylow_of_normal S) hd)
    change a l ∈ (S : Subgroup L)
    simpa only [mul_inv_cancel_left] using hh
  have hs : (S : Subgroup L).map a.toMonoidHom = S :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (f := a.toMonoidHom) a.injective])
  apply mem_normalizer_iff_map_conj_eq.mpr
  change ((S : Subgroup L).map L.subtype).map (MulAut.conj (g : G)).toMonoidHom = _
  rw [map_map,show (MulAut.conj (g : G)).toMonoidHom.comp L.subtype =
    L.subtype.comp a.toMonoidHom from rfl,←map_map,hs]

/-- The natural point generates the original module under the original L. -/
theorem fundamental_module_generated_by_point
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n)) (hn : 0 < n)
    (hodd : Odd n) (hnat : IsNaturalModule L D.moduleSubgroup n) :
    conjugateSpanBy (setup T L D.moduleSubgroup H A).V₁ L = D.moduleSubgroup := by
  have hLV : L ≤ normalizer (D.moduleSubgroup : Set G) := by
    obtain ⟨F,_,_,_,_,hm⟩ := hnat
    exact hm.normalizes
  rcases hnat.invariant_subgroup _ (conjugateSpanBy_le inf_le_right hLV)
      (le_normalizer_conjugateSpanBy _ _) with hh | hh
  · have hz : (setup T L D.moduleSubgroup H A).V₁ = ⊥ :=
      bot_unique ((le_conjugateSpanBy _ _).trans hh.le)
    have hc := fundamental_point_card D hTL hpsl hodd hnat
    change Nat.card (setup T L D.moduleSubgroup H A).V₁ = 2^n at hc
    rw [hz,card_bot] at hc
    have hp : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
    omega
  · exact hh

/-- Within the literal quotient kernel, preserving the natural point is
exactly preserving the original module, not merely its quotient marking. -/
theorem fundamental_kernel_point_stabilizer_eq_module_stabilizer
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n)) (hn : 0 < n)
    (hodd : Odd n) (hnat : IsNaturalModule L D.moduleSubgroup n) :
    let C := (normalizerQuotientAction L (pCore 2 L)).ker.map
      (normalizer (L : Set G)).subtype
    C ⊓ normalizer ((setup T L D.moduleSubgroup H A).V₁ : Set G) =
      C ⊓ normalizer (D.moduleSubgroup : Set G) := by
  let C := (normalizerQuotientAction L (pCore 2 L)).ker.map
    (normalizer (L : Set G)).subtype
  let Z := (setup T L D.moduleSubgroup H A).V₁
  have hcL : C ≤ normalizer (L : Set G) := map_subtype_le _
  have hgen := fundamental_module_generated_by_point (H := H) (A := A) D hTL hpsl hn hodd hnat
  apply le_antisymm
  · refine le_inf inf_le_left ?_
    have hh := normalizes_conjugateSpanBy Z L (C ⊓ normalizer (Z : Set G))
      inf_le_right (inf_le_left.trans hcL)
    change C ⊓ normalizer (Z : Set G) ≤ normalizer (D.moduleSubgroup : Set G)
    change conjugateSpanBy Z L = D.moduleSubgroup at hgen
    rwa [hgen] at hh
  · obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
    have hSm : (S : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
      rw [hS,subgroupOf_map_subtype]
    have hZ : Z = D.moduleSubgroup ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G) := by
      rw [hSm]
      exact fundamental_point_eq_sylow_fixed D hTL hpsl hodd
    refine le_inf inf_le_left ?_
    change C ⊓ normalizer (D.moduleSubgroup : Set G) ≤ normalizer (Z : Set G)
    rw [hZ]
    exact (le_inf inf_le_right ((inf_le_left.trans (left_quotient_kernel_normalizes_sylow S)).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
