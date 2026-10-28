module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.Elementary
public import CFSG.Quasithin.Chapter4.Section01.NormalizerUniqueness
public import Theory.GroupTheory.PGroup.SubnormalCore
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.CComponent.Basic

/-!
# Residuals and component cores in 15.3.12

We form `Y_L = O²(Y₊ ∩ L)`, `Y_C = O²(C_{Y₊}(L/O₂(L)))`, and
`R = O₂(Y₊S)` in the common ambient group. The section centralizer is the
actual kernel on `L/O₂(L)`. The two-residual definitions using normal
subgroups of two-power index and two-group quotients are identified.

The elementary part of 15.3.12 uses the Sylow conclusion of 15.3.11(1)
and the orbit bound of 1.2.1(3). Two-perfect subgroups normalize a component
whose orbit has size at most two. Subnormal core monotonicity then puts
`O₂(L)` in `R`; relative normality puts `O₂(Y_L)` there as well.

There is an obstruction to the printed assertion `|Y_C| = 3`. The residual
`Y_C` is normal in `Y₊`. If `Y₊` is normal in a group with self-centralizing
two-core, a subgroup `Y_C` of order three would lie in its trivial
three-core. `printed_order_obstruction` applies this to the actual local
facts 15.3.11(6),(7), with the orbit bound of 1.2.1(3) explicit. It is not a
counterexample to the full standing counterexample setup, whose existence
is the eventual contradiction of the section. It shows that the stronger
order assertion is incompatible with these earlier local facts.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.12, printed pp.1124–1125 (PDF pp.1141–1142). The proof's final sentence
has `|Y_C|₃ = 3`, as do the uses in 15.3.18 and the proof of 15.3.37;
15.3.23 repeats the stronger printed order. We do not identify the two claims.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Chapter15.Section03.ComponentIntersection
variable {G : Type*} [Group G]

/-- The source subgroup `Y_L = O²(Y₊ ∩ L)`. -/
noncomputable def intersectionResidual (Y L : Subgroup G) : Subgroup G :=
  Stellmacher.twoResidualAmbient (Y ⊓ L)
/-- The source subgroup `Y_C`, using the action on the two-core quotient. -/
noncomputable def centralizerResidual (Y L : Subgroup G) : Subgroup G :=
  Stellmacher.twoResidualAmbient (Chapter4.sectionCentralizerIn Y L)
/-- The source subgroup `R = O₂(Y₊S)`. -/
def localCore (Y S : Subgroup G) : Subgroup G := (Y ⊔ S).pCoreIn 2

/-- Intrinsic two-core quotient; exponent hypotheses belong on this quotient. -/
abbrev TwoCoreQuotient (Y : Subgroup G) := Y ⧸ pCore 2 Y

/-- Every induced automorphism agrees with conjugation by an element of `L`.
The difference lies in the genuine section-action kernel. -/
def InducesInnerOnTwoCoreQuotient (Y L : Subgroup G) : Prop :=
  ∀ y ∈ Y, ∃ l ∈ L, l⁻¹ * y ∈ Chapter4.sectionCentralizer L

/-- An inner action in particular preserves the subgroup acted upon. -/
theorem InducesInnerOnTwoCoreQuotient.normalizes {Y L : Subgroup G}
    (h : InducesInnerOnTwoCoreQuotient Y L) : Y ≤ normalizer (L : Set G) := by
  intro y hy
  obtain ⟨l, hl, hc⟩ := h y hy
  have hn := ((Chapter4.le_sectionCentralizer_iff _ L).mp le_rfl).1 hc
  have hm := (normalizer (L : Set G)).mul_mem (L.le_normalizer hl) hn
  simpa only [mul_inv_cancel_left] using hm

variable [Finite G]

/-- The index and quotient conventions for the finite two-residual agree. -/
theorem twoResidualAmbient_eq_map_pResidual (H : Subgroup G) :
    Stellmacher.twoResidualAmbient H = (pResidual 2 H).map H.subtype := by
  unfold Stellmacher.twoResidualAmbient Stellmacher.twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN, n, hn⟩
    exact ⟨hN, IsPGroup.of_card hn⟩
  · rintro ⟨hN, hp⟩
    exact ⟨hN, IsPGroup.iff_card.mp hp⟩

private theorem normalizes_residual {H X : Subgroup G}
    (h : X ≤ normalizer (H : Set G)) :
    X ≤ normalizer (Stellmacher.twoResidualAmbient H : Set G) := by
  rw [twoResidualAmbient_eq_map_pResidual]
  exact h.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))

omit [Finite G] in
private theorem normalizes_inf {X A B : Subgroup G}
    (hA : X ≤ normalizer (A : Set G)) (hB : X ≤ normalizer (B : Set G)) :
    X ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro x hx a ha
  exact ⟨(hA hx a).mp ha.1, (hB hx a).mp ha.2⟩

omit [Finite G] in
/-- The residual stays in the actual intersection. -/
theorem intersectionResidual_le (Y L : Subgroup G) : intersectionResidual Y L ≤ Y ⊓ L :=
  map_subtype_le _
omit [Finite G] in
/-- The residual stays in the actual section centralizer. -/
theorem centralizerResidual_le (Y L : Subgroup G) :
    centralizerResidual Y L ≤ Chapter4.sectionCentralizerIn Y L := map_subtype_le _

/-- Normalization of `L` makes `Y_L` normal in `Y₊`. -/
theorem normalizes_intersectionResidual {Y L : Subgroup G}
    (h : Y ≤ normalizer (L : Set G)) :
    Y ≤ normalizer (intersectionResidual Y L : Set G) :=
  normalizes_residual (normalizes_inf Y.le_normalizer h)

/-- The kernel of the section action, and then its residual, is normal in `Y₊`. -/
theorem normalizes_centralizerResidual {Y L : Subgroup G}
    (h : Y ≤ normalizer (L : Set G)) :
    Y ≤ normalizer (centralizerResidual Y L : Set G) :=
  normalizes_residual (Chapter4.sectionCentralizerIn_normalized h)

/-- The centralizer residual is two-perfect. -/
theorem centralizerResidual_isPPerfect (Y L : Subgroup G) :
    IsPPerfect 2 (centralizerResidual Y L) := by
  rw [centralizerResidual, twoResidualAmbient_eq_map_pResidual]
  exact isPPerfect_embedded_pResidual 2 _

/-- The intersection residual is two-perfect. -/
theorem intersectionResidual_isPPerfect (Y L : Subgroup G) :
    IsPPerfect 2 (intersectionResidual Y L) := by
  rw [intersectionResidual, twoResidualAmbient_eq_map_pResidual]
  exact isPPerfect_embedded_pResidual 2 (Y ⊓ L)

/-- Order-three generation supplies the two-perfectness used in 15.3.12. -/
theorem theta_isPPerfect (H : Subgroup G) : IsPPerfect 2 (theta H) := by
  have hres : (pResidual 2 (theta H)).map (theta H).subtype = theta H := by
    apply le_antisymm (map_subtype_le _) ((closure_le _).mpr ?_)
    rintro x ⟨hxH, hx3⟩
    have hx : x ∈ theta H := subset_closure ⟨hxH, hx3⟩
    refine ⟨⟨x, hx⟩, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
    have ho : orderOf (⟨x, hx⟩ : theta H) = 3 :=
      (orderOf_injective (theta H).subtype (theta H).subtype_injective _).symm.trans hx3
    change Nat.Coprime 2 (orderOf (⟨x, hx⟩ : theta H))
    rw [ho]
    decide
  rw [← hres]
  exact isPPerfect_embedded_pResidual 2 _

/-- The index bound is the orbit-size conclusion of source 1.2.1(3). -/
theorem normalizes_of_index_le_two {Y L I : Subgroup G}
    (hYI : Y ≤ I) (hY : IsPPerfect 2 Y)
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2) :
    Y ≤ normalizer (L : Set G) := by
  let N := (normalizer (L : Set G)).subgroupOf I
  have hpos := N.index_ne_zero_of_finite
  have hcases : N.index = 1 ∨ N.index = 2 := by change N.index ≤ 2 at hindex; omega
  have hres : pResidual 2 I ≤ N := by
    rcases hcases with h | h
    · rw [Subgroup.index_eq_one.mp h]
      exact le_top
    · let := normal_of_index_eq_two h
      exact sInf_le ⟨inferInstance, IsPGroup.of_card (h.trans (pow_one 2).symm)⟩
  have hYres : Y ≤ (pResidual 2 I).map I.subtype := by
    have hmono := embedded_pResidual_mono 2 hYI
    rw [(pResidual_eq_top_iff 2 Y).mpr hY] at hmono
    intro y hy
    exact hmono ⟨⟨y, hy⟩, trivial, rfl⟩
  intro y hy
  obtain ⟨i, hi, rfl⟩ := hYres hy
  exact hres hi

private theorem core_le_core_of_normalizes {p : ℕ} {A B : Subgroup G}
    (hAB : A ≤ B) (hBA : B ≤ normalizer (A : Set G)) : A.pCoreIn p ≤ B.pCoreIn p :=
  pCoreAmbient_mono_of_isSubnormalIn A B p hAB
    (normal_subgroupOf_of_le_normalizer hBA).isSubnormal

/-- Core containment from source 15.3.11(1), S-invariance of Y, and component normalization. -/
theorem cores_le_localCore {Y S I L : Subgroup G}
    (hLI : L ≤ I) (hL : (L.subgroupOf I).IsCComponent)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hYI : Y ≤ I) (hSY : S ≤ normalizer (Y : Set G))
    (hYL : Y ≤ normalizer (L : Set G)) :
    L.pCoreIn 2 ⊔ (intersectionResidual Y L).pCoreIn 2 ≤ localCore Y S := by
  have hYSI : Y ⊔ S ≤ I := sup_le hYI (hP ▸ map_subtype_le _)
  have hcoreI : I.pCoreIn 2 ≤ S := hP ▸ I.pCoreIn_le_sylow P
  have hIYS : I.pCoreIn 2 ≤ (Y ⊔ S).pCoreIn 2 := by
    have hinf : I.pCoreIn 2 ≤ (Y ⊔ S) ⊓ I.pCoreIn 2 :=
      le_inf (hcoreI.trans le_sup_right) le_rfl
    exact hinf.trans (inf_pCoreIn_le_of_le 2 hYSI)
  apply sup_le
  · exact (pCoreAmbient_mono_of_isSubnormalIn L I 2 hLI hL.subnormal).trans hIYS
  · exact (core_le_core_of_normalizes
      ((intersectionResidual_le Y L).trans inf_le_left)
      (normalizes_intersectionResidual hYL)).trans
      (core_le_core_of_normalizes le_sup_left (sup_le Y.le_normalizer hSY))

/-- The literal core-product containment in 15.3.12(1), using the preceding
local facts and the component orbit bound. No component normalization or
normality of the core product is assumed. -/
theorem core_product_le_of_local_facts {Y S M I L : Subgroup G}
    (hI : I ∈ outsideFamily Y S M) (hSM : S ≤ M)
    (htheta : theta (M ⊓ I) = Y)
    (hLI : L ≤ I) (hL : (L.subgroupOf I).IsCComponent)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2) :
    (L.pCoreIn 2 : Set G) * ((intersectionResidual Y L).pCoreIn 2 : Set G) ⊆
      (localCore Y S : Set G) := by
  have hYI : Y ≤ I := le_sup_left.trans hI.1.2
  have hMIY : M ⊓ I ≤ normalizer (Y : Set G) := by
    rw [← htheta]
    exact (M ⊓ I).le_normalizer.trans (normalizer_le_normalizer_theta (M ⊓ I))
  have hSY : S ≤ normalizer (Y : Set G) :=
    (le_inf hSM (le_sup_right.trans hI.1.2)).trans hMIY
  have hYL := normalizes_of_index_le_two hYI
    (htheta ▸ theta_isPPerfect (M ⊓ I)) hindex
  have hcores := cores_le_localCore hLI hL P hP hYI hSY hYL
  rintro x ⟨a, ha, b, hb, rfl⟩
  exact (localCore Y S).mul_mem (hcores (mem_sup_left ha)) (hcores (mem_sup_right hb))

omit [Finite G] in
private theorem odd_core_eq_bot_of_He {H : Subgroup G} (hH : H ∈ Chapter1.He G) :
    H.pCoreIn 3 = ⊥ := by
  have hcent : H.pCoreIn 3 ≤ centralizer (H.pCoreIn 2 : Set G) := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (pCore_commute_of_ne 2 3 (by decide) b hb a ha)
  have hle : H.pCoreIn 3 ≤ H.pCoreIn 2 :=
    (le_inf (H.pCoreIn_le 3) hcent).trans hH
  have hd := IsPGroup.disjoint_of_ne 3 2 (by decide) (H.pCoreIn 3) (H.pCoreIn 2)
    (H.isPGroup_pCoreIn 3) (H.isPGroup_pCoreIn 2)
  exact eq_bot_iff.mpr (fun _ hx => hd.le_bot ⟨hx, hle hx⟩)

/-- The literal order-three claim is incompatible with the displayed local characteristic-two inputs. -/
theorem centralizerResidual_card_ne_three {Y L H : Subgroup G}
    (hYH : Y ≤ H) (hHY : H ≤ normalizer (Y : Set G))
    (hH : H ∈ Chapter1.He G) (hYL : Y ≤ normalizer (L : Set G)) :
    Nat.card (centralizerResidual Y L) ≠ 3 := by
  intro hcard
  have hCY : centralizerResidual Y L ≤ Y := (centralizerResidual_le Y L).trans inf_le_left
  have hCp : IsPGroup 3 (centralizerResidual Y L) := IsPGroup.of_card (hcard.trans (pow_one 3).symm)
  have hCcore : centralizerResidual Y L ≤ Y.pCoreIn 3 :=
    le_pCoreIn_of_normalizes hCp hCY (normalizes_centralizerResidual hYL)
  have hcore : Y.pCoreIn 3 ≤ H.pCoreIn 3 := core_le_core_of_normalizes hYH hHY
  have hbot : centralizerResidual Y L = ⊥ :=
    eq_bot_iff.mpr ((hCcore.trans hcore).trans (odd_core_eq_bot_of_He hH).le)
  have : Nat.card (centralizerResidual Y L) = 1 := Subgroup.card_eq_one.mpr hbot
  omega

/-- The displayed local facts (15.3.11(6),(7) and the component orbit bound)
exclude the stronger printed order in 15.3.12(2). -/
theorem printed_order_obstruction {Y S M I L : Subgroup G}
    (hI : I ∈ outsideFamily Y S M)
    (htheta : theta (M ⊓ I) = Y)
    (hHe : M ⊓ I ∈ Chapter1.He G)
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2) :
    Nat.card (centralizerResidual Y L) ≠ 3 := by
  have hY : IsPPerfect 2 Y := htheta ▸ theta_isPPerfect (M ⊓ I)
  have hYI : Y ≤ I := le_sup_left.trans hI.1.2
  apply centralizerResidual_card_ne_three (H := M ⊓ I)
  · rw [← htheta]
    exact (closure_le _).mpr fun _ hx => hx.1
  · rw [← htheta]
    exact (M ⊓ I).le_normalizer.trans (normalizer_le_normalizer_theta (M ⊓ I))
  · exact hHe
  · exact normalizes_of_index_le_two hYI hY hindex

end CFSG.Quasithin.Chapter15.Section03.ComponentIntersection

end
