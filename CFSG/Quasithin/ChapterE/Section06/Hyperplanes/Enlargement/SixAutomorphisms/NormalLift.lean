module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.Generation
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable

/-!
# A strictly larger relatively normal component in E.6.23

For A₁ = A ∩ Uᵍ ≠ 1, the genuine E.6.1 hypotheses make H = C_G(A₁)
an SQTK-group. The actual A₆ component X of C_G(A) has three-rank two.
Transporting it to C_H(A) permits the ordinary-component specialization
of I.3.1(3), giving X ≤ Y with Y a normal component of H.

Strictness is a separate argument. A normal A₆ in a group of three-rank
at most two has index prime to three: its center is trivial, its centralizer
has order prime to three, and its actual outer group has order four.
The actual A₃/A₅ block L is its own prime-to-three residual, using its
two-perfectness and simple quotient by O₂(L). Thus if Y = X, the escaping
conjugate Lᵍ, which lies in H, must lie in X. This is the contradiction.

The only explicit earlier-source input is the universal ordinary-component
specialization of I.3.1(3), identical to the input used in `SevenLifting`.
An ordinary component is a special case of a two-component; this interface
does not identify the two notions or assume general two-components are
quasisimple. Its output here is an ordinary component. The nonidentity
intersection is supplied by the published `FurtherLift` contract, so this
step needs no additional E.6.15, odd-core or seven-exclusion premise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the further
enlargement in E.6.23, printed p.254 (PDF p.265), and I.3.1(3), printed
pp.414–415 (PDF pp.425–426). The index argument is the elementary
centralizer/outer-action argument used in A.3.18, printed pp.51–52;
compare `Theory.GroupTheory.CComponent.ThreeResidual`.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.NormalLift
open ComponentBalance
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem elementaryNine_of_rank {H : Type*} [Group H] [Finite H]
    (h : 2 ≤ primeRank 3 H) :
    ∃ E : Subgroup H, IsElementaryAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  let P : Sylow 3 H := Classical.choice inferInstance
  have hn : ¬ IsCyclic P := by
    intro hc
    have hr := P.primeRank_le_one_of_isCyclic hc
    omega
  obtain ⟨E, _, hcard, he⟩ :=
    P.isPGroup'.exists_normal_elementary_prime_sq_of_odd_not_isCyclic (by decide) hn
  let _ := he
  refine ⟨E.map (P : Subgroup H).subtype, IsElementaryAbelian.map_subtype, ?_⟩
  simpa only [Subgroup.card_map_of_injective (P : Subgroup H).subtype_injective] using hcard

private theorem normal_six_index_coprime_three (X : Subgroup G) [X.Normal]
    (e : X ≃* alternatingGroup (Fin 6)) (hr : primeRank 3 G ≤ 2) :
    Nat.Coprime 3 X.index := by
  have hz : center X = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have he := (centerCongr e ⟨x, hx⟩).property
    change e x ∈ center (alternatingGroup (Fin 6)) at he
    rw [alternatingGroup.center_eq_bot (by simp)] at he
    exact mem_bot.mpr (e.injective (by simpa only [map_one] using mem_bot.mp he))
  have hx : 2 ≤ primeRank 3 X := by
    rw [primeRank_congr 3 e]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  obtain ⟨A, hA, ha⟩ := elementaryNine_of_rank hx
  let _ := hA
  let E := A.map X.subtype
  let _ : IsElementaryAbelian 3 E := IsElementaryAbelian.map_subtype
  have hc : Nat.Coprime 3 (Nat.card (centralizer (X : Set G))) := by
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    apply prime_not_dvd_card_centralizer_of_full_rank X E (map_subtype_le A) _ hr hz
    simpa only [E, card_map_of_injective X.subtype_injective] using ha
  have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer X)) := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv, AlternatingSix.ShadowLocal.outer_card]
    decide
  let f : G →* MulAut.Outer X :=
    (QuotientGroup.mk' (MulAut.innerSubgroup X)).comp MulAut.conjNormal
  have hk : f.ker = X ⊔ centralizer (X : Set G) := by
    change ((QuotientGroup.mk' (MulAut.innerSubgroup X)).comp
      (MulAut.conjNormal : G →* MulAut X)).ker = _
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', MulAut.conjNormal_comap_innerSubgroup]
  have hf : Nat.Coprime 3 f.ker.index := by
    rw [index_ker]
    exact ho.coprime_dvd_right f.range.card_subgroup_dvd_card
  rw [hk] at hf
  rw [← relIndex_mul_index (show X ≤ X ⊔ centralizer (X : Set G) from le_sup_left)]
  apply Nat.Coprime.mul_right _ hf
  rw [relIndex_sup_left]
  exact hc.coprime_dvd_right (relIndex_dvd_card _ _)

private theorem smallBlock_conjugate_le_normal_six {U L X H : Subgroup G}
    (hL : SmallBlock U L) (g : G)
    (hLH : L.map (MulAut.conj g).toMonoidHom ≤ H) (hXH : X ≤ H)
    (hn : (X.subgroupOf H).Normal)
    (e : X ≃* alternatingGroup (Fin 6)) (hr : primeRank 3 H ≤ 2) :
    L.map (MulAut.conj g).toMonoidHom ≤ X := by
  have hchi : ChapterC.IsChiZeroBlock L := hL.2.2.elim (fun h => Or.inr (Or.inl h))
    (fun h => Or.inr (Or.inr h))
  let D := (L.map (MulAut.conj g).toMonoidHom).subgroupOf H
  let f : L ≃* D := ((MulAut.conj g).subgroupMap L).trans
    (subgroupOfEquivOfLe hLH).symm
  have hgen : primeToResidual 3 D = ⊤ := by
    have hh := map_primeToResidual (p := 3) f
    rw [InvariantSubspaces.BlockSelection.chiZero_primeToResidual_eq_top hchi,
      map_top_of_surjective _ f.surjective] at hh
    exact hh.symm
  let _ := hn
  have hd : D ≤ X.subgroupOf H :=
    (le_primeToResidual_of_eq_top 3 D hgen).trans
      (primeToResidual_le _ (normal_six_index_coprime_three (X.subgroupOf H)
        ((subgroupOfEquivOfLe hXH).trans e) hr))
  intro x hx
  exact hd (show (⟨x, hLH hx⟩ : H) ∈ D from hx)

omit [Finite G] in
private theorem centralizerComponent_subgroupOf {U L H : Subgroup G} (hUH : U ≤ H)
    (hCH : centralizer (U : Set G) ≤ H) (hL : CentralizerComponent U L) :
    CentralizerComponent (U.subgroupOf H) (L.subgroupOf H) := by
  let P := U.subgroupOf H
  let C := centralizer (P : Set H)
  let D := centralizer (U : Set G)
  let e : C ≃* D :=
    { toFun := fun x => ⟨x.val.val, by
        intro u hu
        exact congrArg Subtype.val (x.property ⟨u, hUH hu⟩ hu)⟩
      invFun := fun x => ⟨⟨x.val, hCH x.property⟩, by
        intro u hu
        exact Subtype.ext (x.property u hu)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have he : (L.subgroupOf D).map e.symm.toMonoidHom = (L.subgroupOf H).subgroupOf C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
  refine ⟨?_, he ▸ hL.2.map_equiv e.symm⟩
  intro l hl p hp
  exact Subtype.ext (hL.1 hl p hp)

/-- Discharge the normal-component construction, with the universal earlier
I.3.1(3) input explicit. SQTK, the rank condition and strictness are proved
from the actual escape configuration. Normality is inside C_G(A ∩ Uᵍ). -/
theorem further_lift
    (hI31 : ∀ (H : Type u) [Group H] [Finite H],
      IsSQTK KnownSimple.IsKnownSimple H → ∀ P D : Subgroup H,
        IsPGroup 2 P → CentralizerComponent P D → primeRank 3 D = 2 →
          ∃ J : Subgroup H, D ≤ J ∧ J.Normal ∧ IsComponent H J)
    {T : Sylow 2 G} {M V : Subgroup G}
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) : FurtherLift M V := by
  intro U A L X g hc hne
  let _ := h.elementary
  let H := centralizer (intersection A U g : Set G)
  have hAV : A ≤ V := hc.subspace_mem.1
  have hH : IsSQTK KnownSimple.IsKnownSimple H :=
    subspaceCentralizer_sqtk h (inf_le_left.trans hAV) hne
  have hAH : A ≤ H := hAV.trans
    (V.le_centralizer.trans (Subgroup.centralizer_le (inf_le_left.trans hAV)))
  have hCH : centralizer (A : Set G) ≤ H := Subgroup.centralizer_le inf_le_left
  have hXH : X ≤ H := hc.six.component.1.trans hCH
  let P := A.subgroupOf H
  let D := X.subgroupOf H
  have hDP : CentralizerComponent P D :=
    centralizerComponent_subgroupOf hAH hCH hc.six.component
  obtain ⟨eX⟩ := hc.six.model
  let eD : D ≃* alternatingGroup (Fin 6) := (subgroupOfEquivOfLe hXH).trans eX
  have hP : IsPGroup 2 P := ((IsElementaryAbelian.isPGroup 2 V).to_le hAV).of_equiv
    (subgroupOfEquivOfLe hAH).symm
  have hrH : primeRank 3 H ≤ 2 := hH.stronglyQuasithin 3 (by decide) (by decide)
  have hrD : primeRank 3 D = 2 := by
    apply le_antisymm
      ((Theory.GroupTheory.primeRank_le_of_injective 3 D.subtype D.subtype_injective).trans hrH)
    rw [primeRank_congr 3 eD]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  obtain ⟨J, hDJ, hnJ, hJ⟩ := hI31 H hH P D hP hDP hrD
  let Y := J.map H.subtype
  have hYH : Y ≤ H := map_subtype_le J
  have hY : Y.subgroupOf H = J := by
    exact comap_map_eq_self (by simp)
  have hXY : X ≤ Y := by
    rw [← map_subgroupOf_eq_of_le hXH]
    exact map_mono hDJ
  have hLgH : L.map (MulAut.conj g).toMonoidHom ≤ H := by
    have hh := (map_mono (f := (MulAut.conj g).toMonoidHom) hc.block.1).trans
      (map_centralizer_le_centralizer_image (U : Set G) (MulAut.conj g).toMonoidHom)
    change L.map (MulAut.conj g).toMonoidHom ≤
      centralizer (U.map (MulAut.conj g).toMonoidHom : Set G) at hh
    exact hh.trans (Subgroup.centralizer_le inf_le_right)
  have hproper : X < Y := lt_of_le_of_ne hXY (by
    intro he
    have hnX : (X.subgroupOf H).Normal := by
      rw [he, hY]
      exact hnJ
    exact hc.conjugate_escapes
      (smallBlock_conjugate_le_normal_six hc.block g hLgH hXH hnX eX hrH))
  refine ⟨Y, hproper, ⟨hYH, ?_⟩, ?_⟩
  · change IsComponent H (Y.subgroupOf H)
    rwa [hY]
  · change (Y.subgroupOf H).Normal
    rwa [hY]

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.NormalLift
