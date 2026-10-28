module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalNaturalDegree
public import Theory.GroupTheory.ReducedNormal.SylowCentralSeed
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalNaturalDegree
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldQrc
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldDegree

/-!
# A natural constituent suffices for the Cartan degree bound

Let U be any nontrivial natural L-module inside the original Sylow T,
normalized by T. Its intersection with Ω₁Z(T) is nontrivial. The actual
Hall Cartan acts freely on a nonidentity point of this intersection, so
its orbit and zero fill C_U(T ∩ L). This line is reduced in AT by the
Sylow-central seed theorem and has faithful Cartan action.

When the original H centralizes omega and O₂(AH) = 1, the actual Borel
residual and common-normal argument supply the qrc bound on this line.
The compatible Hall B fixes the seed pointwise and normalizes A, even
though no normalization of the whole constituent by B is assumed. The
regular cyclic torus bound then gives n ≤ 4. Thus the natural constituent
row of 5.1.3 suffices for small Cartan generation, including repeated
natural modules, without classifying the whole original omega-span.

The stationary selection consumer constructs this constituent from the
original source input. The imports of internal proofs continue the same
Cartan qrc argument while preserving existing public interfaces.

Source: Aschbacher--Smith 5.1.3 and 5.1.6(1--2), printed pp.630--632,
with 3.1.5--6 and B.2.14 (`refs/quasithin.pdf`).
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
/-- The Cartan span of the constituent's central Sylow points is its full
natural Sylow-fixed line. No model for the whole omega-span is assumed. -/
theorem Input.natural_seed_cartan_span
    {T : Sylow 2 G} {L W H A B U : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (c : CartanPair T L H A B)
    [IsElementaryAbelian 2 U]
    (hUT : U ≤ (T : Subgroup G)) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hU0 : U ≠ ⊥) (hm : IsNaturalModule L U n) :
    let V := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G) ⊓ U) A
    V = U ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ∧
    Nat.card V = 2^n ∧
    A ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) ∧
    A ⊓ centralizer (V : Set G) = ⊥ := by
  let Z := omegaOneCenterAmbient (T : Subgroup G) ⊓ U
  let V := conjugateSpanBy Z A
  let C := U ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G)
  have hCc := (hm.sylow_intersection_geometry T h.sylow_normalizes).1
  have hDc := c.left_card h.linear h.sylow_normalizes
  change Nat.card C = 2^n at hCc
  have hZC : Z ≤ C := by
    intro z hz
    exact ⟨hz.2,fun t ht =>
      ((mem_omegaOneCenterAmbient_iff _ _).mp hz.1).2.2 t ht.1⟩
  have hLU : L ≤ normalizer (U : Set G) := by
    obtain ⟨F,_,_,_,_,m⟩ := hm
    exact m.normalizes
  have hTinter : (T : Subgroup G) ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans inf_normalizer_le_normalizer_inf
  have hnorm : A ⊔ (T : Subgroup G) ≤ normalizer (C : Set G) := by
    apply (le_inf (sup_le ((c.left_le.trans inf_le_left).trans
      hLU) hTU)
      (sup_le (c.left_le.trans inf_le_right) hTinter |>.trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hVC : V ≤ C := conjugateSpanBy_le hZC (le_sup_left.trans hnorm)
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hU0 hUT hTU)
  have hzZ : (z:G) ∈ Z := by
    exact ⟨(mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hUT z.property.1,
        elemPow_eq_one_of_isElementaryAbelian (p:=2) (z:G) z.property.1,z.property.2.2⟩,
      z.property.1⟩
  have hz0 : (z:G) ≠ 1 := fun he => hz1 (Subtype.ext he)
  have hoA : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have hfree (x : G) (hx : x ∈ A) (he : x*(z:G)*x⁻¹=(z:G)) : x=1 := by
    have ho : Odd (orderOf x) := hoA.of_dvd_nat (by
      rw [←Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_natCard _)
    exact natural_odd_point_stabilizer hm (c.left_le hx).1 ho
      hzZ.2 hz0 he
  let orb : A → V := fun d =>
    ⟨(d:G)*(z:G)*(d:G)⁻¹,subset_closure ⟨d,d.property,z,hzZ,rfl⟩⟩
  have horb0 (d : A) : orb d ≠ 1 := by
    intro he
    apply hz0
    have hh := congrArg Subtype.val he
    change (MulAut.conj (d:G)) (z:G) = 1 at hh
    exact (MulAut.conj (d:G)).map_eq_one_iff.mp hh
  have hi : Function.Injective orb := by
    intro a b he
    have hh : (b:G)*(z:G)*(b:G)⁻¹=(a:G)*(z:G)*(a:G)⁻¹ :=
      (congrArg Subtype.val he).symm
    have hf := hfree ((a:G)⁻¹*(b:G)) (A.mul_mem (A.inv_mem a.property) b.property) (by
      calc
        (a:G)⁻¹*(b:G)*(z:G)*((a:G)⁻¹*(b:G))⁻¹ =
            (a:G)⁻¹*((b:G)*(z:G)*(b:G)⁻¹)*(a:G) := by group
        _ = (z:G) := by rw [hh]; group)
    exact Subtype.ext (inv_mul_eq_one.mp hf)
  let f : Option A → V := fun d => d.elim 1 orb
  have hfi : Function.Injective f := by
    intro a b he
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact (horb0 b he.symm).elim
    | some a =>
      cases b with
      | none => exact (horb0 a he).elim
      | some b => exact congrArg some (hi he)
  have hlow := Nat.card_le_card_of_injective f hfi
  have hopt : Nat.card (Option A) = Nat.card A+1 := by
    let : Fintype A := Fintype.ofFinite A
    simp only [Nat.card_eq_fintype_card,Fintype.card_option]
  rw [hopt,hDc] at hlow
  have hp : 0 < (2:ℕ)^n := pow_pos (by decide) _
  have he : V = C := eq_of_le_of_card_ge hVC (by omega)
  change V = C ∧ Nat.card V = 2^n ∧ A ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) ∧ _
  refine ⟨he,by rw [he]; exact hCc,by rw [he]; exact hnorm,?_⟩
  apply _root_.eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  apply hfree x hx.1
  exact mul_inv_eq_iff_eq_mul.mpr ((hx.2 z (le_conjugateSpanBy Z A hzZ)).symm)


private theorem natural_seed_reduced
    {T : Sylow 2 G} {L W H A B U : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n) (c : CartanPair T L H A B)
    [IsElementaryAbelian 2 U]
    (hUT : U ≤ (T : Subgroup G)) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hU0 : U ≠ ⊥) (hm : IsNaturalModule L U n) :
    conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G) ⊓ U) A ∈
      reducedFamily (A ⊔ (T : Subgroup G)) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G) ⊓ U
  let X := conjugateSpanBy Z A
  let J := A ⊔ (T : Subgroup G)
  have hg := h.natural_seed_cartan_span c hUT hTU hU0 hm
  have hXU : X ≤ U := hg.1.le.trans inf_le_left
  let : IsElementaryAbelian 2 X := IsElementaryAbelian.of_le hXU
  have hXJ : X ≤ J := hXU.trans (hUT.trans le_sup_right)
  have hspan : X = conjugateSpanBy Z J := le_antisymm
    (conjugateSpanBy_mono le_rfl le_sup_left)
    (conjugateSpanBy_le (le_conjugateSpanBy Z A) hg.2.2.1)
  have hr := reduced_of_sylow_central_seed T J X Z le_sup_right hXJ hg.2.2.1
    (le_conjugateSpanBy Z A)
    (fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz.1).2.2) hspan
  exact ⟨hXJ,inferInstance,hr.normal,hr.quotient_pCore_eq_bot⟩

private theorem natural_seed_qrc
    {T : Sylow 2 G} {L W H A B U : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) [IsElementaryAbelian 2 U]
    (hUT : U ≤ (T : Subgroup G)) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hU0 : U ≠ ⊥) (hm : IsNaturalModule L U n) (hz : (A ⊔ H).pCoreIn 2 = ⊥) :
    Chapter3.QrcHypotheses T (normalizer (L : Set G)) (A ⊔ (T : Subgroup G)) H
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G) ⊓ U) A) := by
  let X := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G) ⊓ U) A
  let J := A ⊔ (T : Subgroup G)
  have hg := h.natural_seed_cartan_span c hUT hTU hU0 hm
  have hr := natural_seed_reduced h c hUT hTU hU0 hm
  let := hr.2.1
  have hn : J ≤ normalizer (X : Set G) := reduced_normalizes hr
  have hc := reduced_torus_centralizer hr
    (torus_join_card c h.sylow_normalizes h.linear le_rfl) hg.2.2.2
  refine ⟨le_sup_right,
    sup_le (c.left_le.trans (inf_le_left.trans L.le_normalizer)) h.sylow_normalizes,
    hH,hr.1,hn,hr.2.1,?_,hc,Or.inl (cartan_residual_normalized h hH c hz)⟩
  exact Chapter3.Section02.internalActionImage_core_of_reduced J X hr.1 hn
    (show IsPReduced 2 (X.subgroupOf J) from
      ⟨hr.2.2.choose,IsElementaryAbelian.subgroupOf hr.1,hr.2.2.choose_spec⟩)

private theorem natural_seed_cubic
    {T : Sylow 2 G} {L W H A B U : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) [IsElementaryAbelian 2 U]
    (hUT : U ≤ (T : Subgroup G)) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hU0 : U ≠ ⊥) (hm : IsNaturalModule L U n)
    (hHC : H ≤ omegaCentralizer T) (hz : (A ⊔ H).pCoreIn 2 = ⊥) :
    let X := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G) ⊓ U) A
    let hq := natural_seed_qrc h hH c hUT hTU hU0 hm hz
    letI := hq.module_elementary
    Representation.BinaryOffender.cubicRatio (ChapterD.UniqueFactor.imageRepresentation
      (A ⊔ (T : Subgroup G)) X hq.module_normalized) ≤ 2 := by
  let Z := omegaOneCenterAmbient (T : Subgroup G) ⊓ U
  let X := conjugateSpanBy Z A
  let hq := natural_seed_qrc h hH c hUT hTU hU0 hm hz
  have hd : ChapterD.QRCConfiguration (A ⊔ (T : Subgroup G)) H (T : Subgroup G) X := by
    apply hq.toQRCConfiguration
    rintro ⟨N,hNc,hN,hn⟩
    have hNT : N ≤ (T : Subgroup G) := hNc.trans (hq.core_eq_centralizer ▸ inf_le_left)
    have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
    have hgen : Chapter3.generated (A ⊔ (T : Subgroup G)) H = A ⊔ H := by
      rw [Chapter3.generated_eq_sup,sup_assoc,sup_eq_right.mpr hTH]
    have hnorm : A ⊔ H ≤ normalizer (N : Set G) := by
      simpa only [hgen] using (Chapter3.normalIn_iff_le_normalizer.mp hn).2
    have hc := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hNT)
      (hNT.trans (hTH.trans le_sup_right)) hnorm
    exact hN (bot_unique (hz ▸ hc))
  have hne : X ≠ ⊥ := by
    intro he
    have hh := (h.natural_seed_cartan_span c hUT hTU hU0 hm).2.1
    change Nat.card X = 2^n at hh
    rw [he,Subgroup.card_bot] at hh
    have hp : 1 < (2:ℕ)^n := Nat.one_lt_pow (by have := h.exponent; omega) (by decide)
    omega
  have hBV : H ⊓ normalizer (L : Set G) ≤ normalizer (X : Set G) := by
    rw [inf_comm,←c.sylow_sup_right h.sylow_normalizes hH.1.1.2]
    apply sup_le (le_sup_right.trans hq.module_normalized)
    exact normalizes_conjugateSpanBy Z A B
      ((c.right_le.trans inf_le_right).trans
        (hHC.trans ((centralizer_le inf_le_left).trans (Subgroup.centralizer_le_normalizer _))))
      c.right_normalizes_left
  exact normalized_cubicRatio_le_two hq h.qtke h.maximal hd hne hBV
/-- One Sylow-invariant natural constituent suffices to bound the original
field degree by four when H centralizes omega and the Cartan join has zero core. -/
theorem Input.natural_seed_cartan_degree_le_four
    {T : Sylow 2 G} {L W H A B U₀ : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B)
    [IsElementaryAbelian 2 U₀]
    (hUT : U₀ ≤ (T : Subgroup G)) (hTU : (T : Subgroup G) ≤ normalizer (U₀ : Set G))
    (hU0 : U₀ ≠ ⊥) (hm : IsNaturalModule L U₀ n)
    (hHC : H ≤ omegaCentralizer T) (hz : (A ⊔ H).pCoreIn 2 = ⊥) : n ≤ 4 := by
  let X := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G) ⊓ U₀) A
  let J := A ⊔ (T : Subgroup G)
  let U := (T : Subgroup G) ⊓ L
  let hq := natural_seed_qrc h hH c hUT hTU hU0 hm hz
  let := hq.module_elementary
  have hg := h.natural_seed_cartan_span c hUT hTU hU0 hm
  have hJ : J ≤ normalizer (X : Set G) := hq.module_normalized
  let f := ChapterD.UniqueFactor.actionHom A X (le_sup_left.trans hJ)
  let C := ChapterD.internalActionImage A X (le_sup_left.trans hJ)
  obtain ⟨F,_,_,_,_,⟨e⟩⟩ := c.left_equiv_units h.linear h.sylow_normalizes
  let : IsCyclic A := isCyclic_of_injective e.toMonoidHom e.injective
  let : IsCyclic C := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rw [ChapterD.UniqueFactor.actionHom_ker]
    apply _root_.eq_bot_iff.mpr
    intro a ha
    apply mem_bot.mpr
    apply Subtype.ext
    exact mem_bot.mp (hg.2.2.2 ▸ (show (a:G) ∈ A ⊓ centralizer (X : Set G) from
      ⟨a.property,ha⟩))
  have hregA := Theory.GroupAction.faithful_cyclic_binary_singer_regular f hfi
    h.exponent (c.left_card h.linear h.sylow_normalizes) hg.2.1
  have hreg : ∀ v w : X, v ≠ 1 → w ≠ 1 → ∃! a : C, a.val v = w := by
    intro v w hv hw
    obtain ⟨a,ha,hu⟩ := hregA v w hv hw
    refine ⟨f.rangeRestrict a,ha,?_⟩
    intro b hb
    obtain ⟨a',ha'⟩ := f.rangeRestrict_surjective b
    rw [←ha'] at hb ⊢
    exact congrArg f.rangeRestrict (hu a' hb)
  have hTB : (T : Subgroup G) ≤ normalizer (localBorel T L : Set G) :=
    (le_inf h.sylow_normalizes
      ((le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans
        inf_normalizer_le_normalizer_inf |>.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hTN : (T : Subgroup G) ≤ normalizer ((U ⊔ A : Subgroup G) : Set G) :=
    hTB.trans (Prime.cartan_subgroup_preimage_normalized c h.sylow_normalizes h.linear le_rfl)
  have hUC : U ≤ centralizer (X : Set G) := by
    apply le_centralizer_iff.mp
    change conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G) ⊓ U₀) A ≤ _
    rw [hg.1]
    exact inf_le_right
  have hN : ChapterD.internalActionImage J X hJ ≤ normalizer (C : Set (MulAut X)) :=
    image_normalizes_torus hJ (inf_le_left.trans le_sup_right) le_sup_left hUC
      (sup_le (le_sup_right.trans (U ⊔ A).le_normalizer) hTN)
  have hc := Theory.GroupTheory.regular_cyclic_normalizer_cubic_card_le
    C (ChapterD.internalActionImage J X hJ)
    hreg hN (ChapterD.UniqueFactor.imageRepresentation J X hJ) (fun _ _ => rfl)
      (natural_seed_cubic h hH c hUT hTU hU0 hm hHC hz)
  rw [hg.2.1] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc


end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
