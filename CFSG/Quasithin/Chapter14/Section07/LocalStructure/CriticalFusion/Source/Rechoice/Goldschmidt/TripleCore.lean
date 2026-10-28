module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import Theory.GroupTheory.SpecificGroups.KleinFourFixedAut
public import Theory.ElementaryAbelian.PrimePlane
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow


/-!
# The right Goldschmidt quotient, intersection and central module in 14.7.70

Relative normality of Y_E in N_G(E) makes its Sylow intersection with T a
Sylow subgroup of Y_E. The residual/Sylow supplement therefore puts Y_E
inside YT. Its full conjugation action on the elementary four-group E gives
the actual quotient YT/O₂(YT) ≃ S₃, since the action kernel is a two-group.

The intersection with L₁T fixes the original nonidentity point z of E. Both
its action image and kernel are two-groups, so Sylow maximality identifies
the intersection with the prescribed T. This uses no assumed triple.

O₂(I) lies in T, which centralizes V₁. Its normality implies that it centralizes
the entire I-span V_I, even before nontriviality of O₂(I) is established.
Once that nontriviality is known, the genuine 1.1.4(6) makes I characteristic
two. Thus V_I lies in Z(O₂(I)) and is elementary, by its involution generators.
This proves the elementary/centrality portion of the B.2.14 application
directly; neither a new B.2.14 premise nor later Lemma 14.7.71 is used.

The left S₃ quotient and the preliminary five-chief-factor calculation are
still required. This module does not construct CoreFacts or assert the source
theorem. Their assembly, including the F.6.5 classification application,
remains with qt-14-07-rechoice-triple-core; final rank-three recognition stays
with qt-14-07-rechoice-goldschmidt.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Lemma 14.7.70, printed p.1074 (PDF p.1091), and B.2.14(2), printed p.78.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {d : Data T L V F W} {c : CriticalPath (L := L) F}

private theorem normal_le_residual_sup_sylow (N A : Subgroup G)
    (hAN : A ≤ N) (hTN : (T : Subgroup G) ≤ N) [(A.subgroupOf N).Normal] :
    A ≤ (pResidual 2 A).map A.subtype ⊔ (T : Subgroup G) := by
  obtain ⟨S, hS⟩ := (T.subtype hTN).exists_subgroupOf_eq_of_normal (A.subgroupOf N)
  have hs := congrArg (fun B : Subgroup (A.subgroupOf N) =>
    (B.map (A.subgroupOf N).subtype).map N.subtype) (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup, Subgroup.map_sup, map_embedded_pResidual, map_subgroupOf_eq_of_le hAN,
    ← MonoidHom.range_eq_map, range_subtype, map_subgroupOf_eq_of_le hAN,
    hS, subgroupOf_map_subtype] at hs
  apply le_trans hs.symm.le
  apply sup_le le_sup_left
  exact (map_mono inf_le_left).trans (by
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTN]
    exact le_sup_right)

namespace Geometry
variable (h : Geometry d c)
include h

/-- Relative normality in N_G(E) puts Y_E in its residual/Sylow supplement. -/
theorem YE_le_YT : YE c ≤ YT c := by
  let := h.YE_normal
  exact normal_le_residual_sup_sylow _ _ h.YE_normalizes h.T_normalizes

/-- The actual conjugation action of YT on E. -/
def rightAction : YT c →* MulAut (E c) :=
  (E c).normalizerMonoidHom.comp (inclusion h.YT_normalizes_E)

/-- The Y_E action remains full after adjoining the prescribed Sylow. -/
theorem rightAction_surjective : Function.Surjective h.rightAction := by
  intro a
  obtain ⟨y, hy⟩ := h.full_action a
  exact ⟨⟨y, h.YE_le_YT y.property⟩, hy⟩

/-- The kernel is the literal relative centralizer, with no quotient convention change. -/
theorem rightAction_ker : h.rightAction.ker = (centralizer (E c : Set G)).subgroupOf (YT c) := by
  rw [rightAction, ← MonoidHom.comap_ker, normalizerMonoidHom_ker]
  rfl

/-- The ambient two-group centralizer controls the complete action kernel. -/
theorem rightAction_ker_two : IsPGroup 2 h.rightAction.ker := by
  rw [h.rightAction_ker]
  exact h.centralizer_two.comap_subtype

/-- The preceding elementary rank-two group is a genuine four-group. -/
theorem E_isKleinFour : IsKleinFour (E c) := by
  let := h.elementary
  have hc : Nat.card (E c) = 4 := IsElementaryAbelian.card_eq_prime_sq_of_primeRank_two h.rank_two
  let : Nontrivial (E c) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩

/-- Conjugation constructs the actual YT/O₂(YT) ≃ S₃. -/
def rightQuotientEquiv : ((YT c) ⧸ pCore 2 (YT c)) ≃* Equiv.Perm (Fin 3) := by
  let := h.E_isKleinFour
  let e := IsKleinFour.autEquivPermThree (E c)
  let f := e.toMonoidHom.comp h.rightAction
  have hf : Function.Surjective f := e.surjective.comp h.rightAction_surjective
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact h.rightAction_ker_two
  exact (QuotientGroup.quotientMulEquivOfEq
    (ker_eq_twoCore_of_surjective_perm_three f hf hk).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- Restricting YT to I transports its intrinsic two-core quotient. -/
theorem quotient_right : Nonempty (((right c) ⧸ pCore 2 (right c)) ≃* Equiv.Perm (Fin 3)) := by
  let e := subgroupOfEquivOfLe (YT_le_I c)
  exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans h.rightQuotientEquiv⟩

/-- The intersection fixes the original nonidentity point of E. Its action
and its action kernel are both two-groups. -/
theorem intersection_two : IsPGroup 2 (group F L ⊓ YT c : Subgroup G) := by
  let := h.E_isKleinFour
  let A := group F L ⊓ YT c
  let f := h.rightAction.comp (inclusion (inf_le_right : A ≤ YT c))
  have hz : d.z ∈ E c := (le_sup_left : F.Vi 1 ≤ E c) (d.point ▸ mem_zpowers d.z)
  let z : E c := ⟨d.z, hz⟩
  have hz1 : z ≠ 1 := fun he => d.z_ne_one (congrArg Subtype.val he)
  have hr : IsPGroup 2 f.range :=
    IsKleinFour.isPGroup_aut_subgroup_of_fixed_ne_one f.range hz1 (by
      rintro a ⟨x, rfl⟩
      apply Subtype.ext
      change (x : G) * d.z * (x : G)⁻¹ = d.z
      have hx := mem_centralizer_iff.mp (group_centralizes_point d x.property.1)
        d.z (d.point ▸ mem_zpowers d.z)
      rw [← hx, mul_inv_cancel_right])
  have hk : IsPGroup 2 f.ker := by
    rw [show f.ker = h.rightAction.ker.comap (inclusion inf_le_right) from rfl]
    exact h.rightAction_ker_two.comap_of_injective _ (inclusion_injective _)
  have hp : IsPGroup 2 (⊤ : Subgroup A) := by
    have he : f.range.comap f = ⊤ := by
      ext x
      exact ⟨fun _ => mem_top x, fun _ => ⟨x, rfl⟩⟩
    exact he ▸ hr.comap_of_ker_isPGroup f hk
  exact hp.of_equiv Subgroup.topEquiv

/-- The two actual vertices meet in the prescribed ambient Sylow. -/
theorem intersection : left c ⊓ right c = (sylow c : Subgroup (I c)) := by
  have he : group F L ⊓ YT c = (T : Subgroup G) :=
    T.is_maximal' h.intersection_two (le_inf le_sup_right le_sup_right)
  change (group F L).subgroupOf (I c) ⊓ (YT c).subgroupOf (I c) = _
  exact congrArg (fun A : Subgroup G => A.subgroupOf (I c)) he


/-- Assemble the triple once the independent left parabolic calculation is
available. The right quotient and prescribed Sylow intersection are proved here;
the displayed left quotient remains an intermediate obligation. -/
theorem triple_of_left_quotient
    (hleft : Nonempty (((left c) ⧸ pCore 2 (left c)) ≃* Equiv.Perm (Fin 3))) :
    ChapterF.IsGoldschmidtTriple (left c) (right c) :=
  ⟨generated c, hleft, h.quotient_right, sylow c, h.intersection⟩

end Geometry

/-- The core lies in the prescribed Sylow, and its centralizer is I-invariant. -/
theorem VI_le_core_centralizer (d : Data T L V F W) (c : CriticalPath (L := L) F) :
    VI c ≤ centralizer ((I c).pCoreIn 2 : Set G) := by
  have hQT : (I c).pCoreIn 2 ≤ (T : Subgroup G) := by
    have hq := pCoreIn_le_sylow (I c) (sylow c)
    simpa only [sylow_coe, map_subgroupOf_eq_of_le (T_le_I c)] using hq
  have hz : F.Vi 1 ≤ centralizer (T : Set G) :=
    le_centralizer_iff.mp ((le_sup_right : (T : Subgroup G) ≤ group F L).trans
      (group_centralizes_point d))
  have hn : I c ≤ normalizer ((I c).pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map,
      range_subtype] using (pCore 2 (I c)).le_normalizer_map (I c).subtype
  exact conjugateSpanBy_le (hz.trans (centralizer_le hQT))
    (hn.trans (normalizer_le_normalizer_centralizer _))

/-- The literal two-core centralizes the entire source conjugate span. -/
theorem core_centralizes_VI (d : Data T L V F W) (c : CriticalPath (L := L) F) :
    pCore 2 (I c) ≤ centralizer ((VI c).subgroupOf (I c) : Set (I c)) := by
  intro q hq
  apply mem_centralizer_iff.mpr
  intro v hv
  apply Subtype.ext
  exact (mem_centralizer_iff.mp (VI_le_core_centralizer d c hv) q
    (mem_map_of_mem (I c).subtype hq)).symm

/-- Source 1.1.4(6) applies to I once its core is nontrivial. -/
theorem local_characteristic_two (d : Data T L V F W) (c : CriticalPath (L := L) F)
    (hne : pCore 2 (I c) ≠ ⊥) : I c ∈ Chapter1.He G :=
  Chapter1.lemma_1_1_4_6 T (d.counterexample.qtke.evenCharacteristic T)
    (Geometry.local_and_sqtk (d := d) (c := c) hne).1

/-- The source conjugate span lies inside the self-centralizing core. -/
theorem VI_le_core (d : Data T L V F W) (c : CriticalPath (L := L) F)
    (hne : pCore 2 (I c) ≠ ⊥) : VI c ≤ (I c).pCoreIn 2 :=
  (le_inf (VI_le_I d c) (VI_le_core_centralizer d c)).trans
    (local_characteristic_two d c hne)

/-- The elementary and centrality clauses used from B.2.14 follow directly
from its source argument on the actual central involution seed. -/
theorem VI_elementary (d : Data T L V F W) (c : CriticalPath (L := L) F)
    (hne : pCore 2 (I c) ≠ ⊥) : IsElementaryAbelian 2 (VI c) := by
  let := d.natural.chosen.elementary
  let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
  let : IsMulCommutative (conjugateSpanBy (F.Vi 1) (I c)) := le_centralizer_iff_isMulCommutative.mp
    ((VI_le_core_centralizer d c).trans (centralizer_le (VI_le_core d c hne)))
  exact conjugateSpanBy_elementary_of_commutative (F.Vi 1) (I c)


/-- The kernel equality in 14.7.70 follows from the preceding geometry alone:
centralization of the conjugate span needs no classification input. -/
theorem Geometry.core_identification (h : Geometry d c) :
    pCore 2 (I c) = centralizer ((VI c).subgroupOf (I c) : Set (I c)) :=
  h.core_eq_centralizer (core_centralizes_VI d c)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt
