module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction

/-!
# Quotient and component detection for the intrinsic Ξ reduction

The odd complement embeds in H/O₂(H). Its commutator identity descends,
so the published Fitting reduction detects an ordinary component once the
supercritical argument supplies the two Fitting premises. The lift retains
its actual quotient image, quasisimple quotient and noncentral commutator.
Normality of the complement image instead gives normality of X by conjugate
generation and the intrinsic two-residual identity.

The A.3.3(7) deduction uses its full universal dichotomy explicitly; the
solvable branch is excluded by the detected ordinary component. None of
these lemmas assumes T is Sylow in H. FittingConditions is an intermediate
proof obligation, not a replacement for the source hypotheses.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Proposition 1.3.4, printed pp.509–510, and
Proposition A.3.3(7), printed pp.42–43.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G]

/-- The image of an ambient subgroup in H/O₂(H). -/
def quotientImage (H A : Subgroup G) : Subgroup (XiQuotient H) :=
  (A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))

/-- The chosen complement lies in the overgroup. -/
theorem LocalInput.complement_le_overgroup {p : ℕ} {T X P H : Subgroup G}
    (h : LocalInput p T X P H) : P ≤ H :=
  le_sup_right.trans (h.complement.le.trans (le_sup_left.trans h.overgroup))

/-- An odd complement embeds in the quotient by the overgroup's two-core. -/
noncomputable def LocalInput.quotientComplementEquiv {p : ℕ} {T X P H : Subgroup G}
    (h : LocalInput p T X P H) : P ≃* quotientImage H P := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  let R := P.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  have hd : Disjoint (pCore 2 H) R :=
    pCore_isPGroup.disjoint_of_coprime h.odd_complement.isPGroup.comap_subtype
      (Nat.coprime_two_left.mpr h.odd)
  have hi : Function.Injective (q.subgroupMap R) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    have hc : (a : H) ∈ pCore 2 H := (QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val ha)
    exact Subtype.ext (hd.le_bot ⟨hc, a.property⟩)
  exact (subgroupOfEquivOfLe h.complement_le_overgroup).symm.trans
    (MulEquiv.ofBijective (q.subgroupMap R) ⟨hi, q.subgroupMap_surjective R⟩)

/-- The quotient complement retains its actual elementary/extraspecial alternative. -/
theorem LocalInput.quotient_odd_complement {p : ℕ} {T X P H : Subgroup G}
    (h : LocalInput p T X P H) : XiOddQuotient p (quotientImage H P) :=
  h.odd_complement.of_mulEquiv h.quotientComplementEquiv

/-- The quotient complement is noncyclic. -/
theorem LocalInput.quotient_complement_not_cyclic [Finite G]
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H) :
    ¬ IsCyclic (quotientImage H P) := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  exact h.quotient_odd_complement.not_isCyclic

/-- Normality of the complement image implies normality of X itself.
Conjugate generation, rather than an identification X̄ = P̄ in general,
is what justifies the normal branch. -/
theorem LocalInput.normal_of_complement_quotient_normal
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H)
    (hn : (quotientImage H P).Normal) : (X.subgroupOf H).Normal := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let R := (quotientImage H P).comap q
  let C := R.map H.subtype
  let _ := hn
  have hCH : C ≤ H := map_subtype_le R
  have hCn : (C.subgroupOf H).Normal := by
    have he : C.subgroupOf H = R := by
      change (R.map H.subtype).comap H.subtype = R
      rw [comap_map_eq, H.subtype.ker_eq_bot_iff.mpr H.subtype_injective, sup_bot_eq]
    rw [he]
    infer_instance
  have hPC : P ≤ C := by
    rw [← map_subgroupOf_eq_of_le h.complement_le_overgroup]
    exact map_mono (le_comap_map q (P.subgroupOf H))
  have hXC : X ≤ C := h.le_of_complement_le hPC
    ((normal_subgroupOf_iff_le_normalizer hCH).mp hCn)
  have he : quotientImage H X = quotientImage H P := by
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      intro x hx
      obtain ⟨y, hy, he⟩ := hXC hx
      exact (show y = x from Subtype.ext he) ▸ hy
    · exact map_mono (subgroupOf_mono H (le_sup_right.trans h.complement.le))
  apply h.normal_of_quotient_normal
  change (quotientImage H X).Normal
  rw [he]
  exact hn

/-- The commutator identity descends to the quotient using the actual images. -/
theorem LocalInput.quotient_complement_eq_commutator
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H) :
    quotientImage H P = ⁅quotientImage H P, quotientImage H (T ⊓ normalizer P)⁆ := by
  have hSH : T ⊓ normalizer P ≤ H := inf_le_left.trans (le_sup_right.trans h.overgroup)
  have hi : P.subgroupOf H = ⁅P.subgroupOf H, (T ⊓ normalizer P).subgroupOf H⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le h.complement_le_overgroup,
      map_subgroupOf_eq_of_le hSH]
    exact h.complement_eq_commutator_normalizer
  exact congrArg (map (QuotientGroup.mk' (pCore 2 H))) hi |>.trans
    (map_commutator _ _ _)

/-- The exact Fitting premises used by the component-detection step.
This is an intermediate target, not an assumption on a member of Ξ. -/
def FittingConditions (p : ℕ) (P H : Subgroup G) : Prop :=
  IsCyclic (pCore p (XiQuotient H)) ∧
    ∀ r : ℕ, r.Prime → Odd r → r ≠ p →
      quotientImage H P ≤ centralizer (pCore r (XiQuotient H) : Set (XiQuotient H))

/-- The quotient form of detection, with every subgroup transport discharged. -/
theorem LocalInput.detect_component_of_fitting [Finite G]
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H)
    (hf : FittingConditions p P H) :
    quotientImage H P ≤ centralizer (fittingSubgroup (XiQuotient H) : Set (XiQuotient H)) ∧
      ∃ Lbar : Subgroup (XiQuotient H), IsComponent (XiQuotient H) Lbar ∧
        ⁅Lbar, quotientImage H P⁆ ≠ ⊥ := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  let _ := hf.1
  exact fitting_reduction (quotientImage H P) (quotientImage H (T ⊓ normalizer P))
    h.quotient_odd_complement.isPGroup h.quotient_complement_not_cyclic
    (pCore_quotient_pCore_eq_bot 2) h.quotient_complement_eq_commutator hf.2

/-- The output of detection retains the actual ordinary component image.
The stronger commutator exclusion modulo O₂(H) is convenient for lifting. -/
structure ComponentDetection (P H L : Subgroup G) : Prop where
  mem : L ∈ cComponentsIn H
  quasisimple : IsQuasisimple (XiQuotient L)
  component : IsComponent (XiQuotient H) (quotientImage H L)
  noncentral : ¬ ⁅L, P⁆ ≤ H.pCoreIn 2

/-- Lift detection in H/O₂(H) to an ambient C-component, transporting the
actual quotient isomorphism rather than only a family name. -/
theorem LocalInput.lift_detected_component [Finite G]
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H)
    {Lbar : Subgroup (XiQuotient H)} (hLbar : IsComponent (XiQuotient H) Lbar)
    (hne : ⁅Lbar, quotientImage H P⁆ ≠ ⊥) :
    ∃ L : Subgroup G, ComponentDetection P H L ∧ quotientImage H L = Lbar := by
  obtain ⟨D, hD, hqD, heD, hnD⟩ :=
    lift_noncentralized_component (P.subgroupOf H) hLbar hne
  let L := D.map H.subtype
  have hLH : L ≤ H := map_subtype_le D
  have he : L.subgroupOf H = D := by
    change (D.map H.subtype).comap H.subtype = D
    rw [comap_map_eq, H.subtype.ker_eq_bot_iff.mpr H.subtype_injective, sup_bot_eq]
  have hq : quotientImage H L = Lbar := by
    change (L.subgroupOf H).map _ = Lbar
    rwa [he]
  let e : D ≃* L := D.equivMapOfInjective H.subtype H.subtype_injective
  let eqv : XiQuotient D ≃* XiQuotient L :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  refine ⟨L, ⟨⟨hLH, he.symm ▸ hD⟩, IsQuasisimple.of_mulEquiv eqv, hq.symm ▸ hLbar,
    ?_⟩, hq⟩
  intro hn
  apply hnD
  apply (map_le_map_iff_of_injective H.subtype_injective).mp
  rw [map_commutator, map_subgroupOf_eq_of_le h.complement_le_overgroup]
  exact hn

/-- The noncentral commutator is also noncentral modulo the component's
intrinsic two-core, by subnormal core monotonicity. -/
theorem ComponentDetection.noncentral_component_core [Finite G]
    {P H L : Subgroup G} (h : ComponentDetection P H L) :
    ¬ ⁅L, P⁆ ≤ L.pCoreIn 2 := by
  have hd := pCoreIn_le_of_subnormal 2 h.mem.2.subnormal
  have hm := map_mono (f := H.subtype) hd
  rw [map_pCoreIn_of_injective 2 (L.subgroupOf H) H.subtype H.subtype_injective,
    map_subgroupOf_eq_of_le h.mem.1] at hm
  exact fun hc => h.noncentral (hc.trans hm)

/-- Complete detection and lifting once the two Fitting premises have been supplied. -/
theorem LocalInput.exists_component_of_fitting [Finite G]
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H)
    (hf : FittingConditions p P H) : ∃ L : Subgroup G, ComponentDetection P H L := by
  obtain ⟨_, Lbar, hLbar, hn⟩ := h.detect_component_of_fitting hf
  obtain ⟨L, hL, _⟩ := h.lift_detected_component hLbar hn
  exact ⟨L, hL⟩

/-- The lifted exclusion is precisely nontriviality of the quotient commutator. -/
theorem ComponentDetection.quotient_commutator_ne_bot
    {P H L : Subgroup G} (h : ComponentDetection P H L) (hPH : P ≤ H) :
    ⁅quotientImage H L, quotientImage H P⁆ ≠ ⊥ := by
  intro hc
  have hn : ⁅L.subgroupOf H, P.subgroupOf H⁆ ≤ pCore 2 H := by
    rw [← QuotientGroup.ker_mk' (pCore 2 H), ← Subgroup.map_eq_bot_iff, map_commutator]
    exact hc
  apply h.noncentral
  have hm := map_mono (f := H.subtype) hn
  rwa [map_commutator, map_subgroupOf_eq_of_le h.mem.1,
    map_subgroupOf_eq_of_le hPH] at hm

/-- The A.3.3(7) step: a detected component lies in its commutator with P.
The only earlier-result parameter is the universal source dichotomy, including
its solvable-radical alternative. It is not a component-containment assumption. -/
theorem ComponentDetection.le_commutator_of_A_3_3_7 [Finite G]
    (hA337 : ∀ (Y : Type u) [Group Y] [Finite Y] (B D : Subgroup Y),
      B.IsCComponent → ⁅B, D⁆ ≤ solvableRadical Y ∨
        ⁅B, D⁆ = componentOrbit B D)
    {P H L : Subgroup G} (h : ComponentDetection P H L) (hPH : P ≤ H) :
    L ≤ ⁅L, P⁆ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hn := h.quotient_commutator_ne_bot hPH
  have hb : quotientImage H L ≤ ⁅quotientImage H L, quotientImage H P⁆ := by
    rcases h.component.commutator_dichotomy (quotientImage H P) with hc | hc
    · exact (hn hc).elim
    · rw [hc]
      exact le_componentOrbit _ _
  rcases hA337 H (L.subgroupOf H) (P.subgroupOf H) h.mem.2 with hs | he
  · let _ : Group.IsSolvable (⁅L.subgroupOf H, P.subgroupOf H⁆ : Subgroup H) :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective hs)
    let _ : Group.IsSolvable ((⁅L.subgroupOf H, P.subgroupOf H⁆).map q) :=
      Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
    have hb' : quotientImage H L ≤ (⁅L.subgroupOf H, P.subgroupOf H⁆).map q := by
      rwa [map_commutator]
    exact ((component_isCComponent h.component).not_isSolvable
      (Group.isSolvable_of_isSolvable_injective (inclusion_injective hb'))).elim
  · have hl : L.subgroupOf H ≤ ⁅L.subgroupOf H, P.subgroupOf H⁆ := by
      rw [he]
      exact le_componentOrbit _ _
    have hm := map_mono (f := H.subtype) hl
    rwa [map_commutator, map_subgroupOf_eq_of_le h.mem.1,
      map_subgroupOf_eq_of_le hPH] at hm

end CFSG.Quasithin.Chapter1.XiEmbedding
