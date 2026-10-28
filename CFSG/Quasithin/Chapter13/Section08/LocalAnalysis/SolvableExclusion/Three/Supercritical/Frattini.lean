module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Reduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Construction
public import Theory.GroupTheory.Commutator.CoprimeQuadratic
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Frattini irreducibility of the minimal moved odd image

Write P for the constructed image P*, K for (L₁T)*, and A for Vα*.
The K-normal closure B of A lies in the image of O₂(L₁T), so is a
two-group. The commutator [P,B] is normal in P K = H*. If it were
proper in P, minimality would make it centralize A. Coprime commutator
idempotence would then make A centralize P, contradicting movement.
Consequently [P,B] = P.

Every K-invariant subgroup N between Φ(P) and P is H*-normal, since
[P,P] ≤ Φ(P). If N is proper, minimality makes A, and hence B, centralize
N. The actual quotient by the embedded Φ(P) has abelian P-image and
full B-commutator. Coprime fixed/moved splitting therefore puts N in Φ(P).
This argument works for every finite p-group selected by the construction;
no extra small-group classification or irreducibility premise is needed.

This proves the conditional helper used in the proof of Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript (1 March
2004), Lemma 13.8.13, printed pp.950–951. The source-theorem assembly and
the restriction of the odd prime remain with their respective owners.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Supercritical
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

private theorem derived_le_frattini_image {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hp : IsPGroup p P) :
    ⁅P, P⁆ ≤ (frattini P).map P.subtype := by
  let _ : Fact (IsPGroup p P) := ⟨hp⟩
  have h := Subgroup.map_mono (f := P.subtype)
    (commutator_le_frattini_of_isPGroup (R := P) (p := p))
  simpa only [_root_.commutator, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] using h

private theorem normal_of_frattini_le {p : ℕ} [Fact p.Prime]
    (P K N : Subgroup G) (hp : IsPGroup p P) (hgen : P ⊔ K = ⊤)
    (hFN : (frattini P).map P.subtype ≤ N) (hNP : N ≤ P)
    (hKN : K ≤ normalizer (N : Set G)) : N.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  exact sup_le (le_normalizer_iff_commutator_le_right.mpr
    ((commutator_mono le_rfl hNP).trans ((derived_le_frattini_image P hp).trans hFN))) hKN

-- Coprime splitting on the actual abelian quotient by the embedded Frattini subgroup.
private theorem centralizer_le_frattini_of_full {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (P B : Subgroup G) [P.Normal]
    (hp : IsPGroup p P) (hb : IsPGroup 2 B) (hfull : ⁅P, B⁆ = P) :
    P ⊓ centralizer (B : Set G) ≤ (frattini P).map P.subtype := by
  let F := (frattini P).map P.subtype
  let _ : F.Normal := ConjAct.normal_of_characteristic_of_normal
  let π := QuotientGroup.mk' F
  let U := P.map π
  let V := B.map π
  let _ : U.Normal := (inferInstance : P.Normal).map π (QuotientGroup.mk'_surjective F)
  have hUU : ⁅U, U⁆ = ⊥ := by
    have h := Subgroup.map_mono (f := π) (derived_le_frattini_image P hp)
    rw [Subgroup.map_commutator, QuotientGroup.map_mk'_self] at h
    exact bot_unique h
  let _ : IsMulCommutative U := Subgroup.commutator_self_eq_bot_iff.mp hUU
  have hUV : ⁅U, V⁆ = U := by
    simpa only [Subgroup.map_commutator] using congrArg (Subgroup.map π) hfull
  have haction : commutatorAction V U = ⊤ := by
    apply Subgroup.map_injective U.subtype_injective
    rw [commutatorAction_subgroup_conj_map_eq_commutator U V le_normalizer_of_normal,
      hUV, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcop : Nat.Coprime (Nat.card V) (Nat.card U) :=
    IsPGroup.coprime_card_of_ne 2 p (by rintro rfl; norm_num at ho) V U (hb.map π) (hp.map π)
  have hcompl := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := U) (A := V) (Group.isSolvable_of_comm fun a b => mul_comm a b) hcop inferInstance
  have hfix : FixedPoints.subgroup V U = ⊥ := by
    have h := hcompl.disjoint
    rw [haction] at h
    exact disjoint_top.mp h
  intro x hx
  let xU : U := ⟨π x, mem_map_of_mem π hx.1⟩
  have hxfix : xU ∈ FixedPoints.subgroup V U := by
    intro t
    apply Subtype.ext
    change (t : G ⧸ F) * π x * (t : G ⧸ F)⁻¹ = π x
    obtain ⟨s, hs, hst⟩ := t.property
    rw [← hst, ← map_inv, ← map_mul, ← map_mul]
    apply congrArg π
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hx.2 s hs)
  have hxone : xU = 1 := by simpa only [hfix, mem_bot] using hxfix
  exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hxone)

/-- The minimal moved odd image has an irreducible Frattini quotient under L₁T. -/
theorem OddConstruction.starFrattiniIrreducible {p : ℕ}
    {H L₁ T M Vα : Subgroup G} (c : OddConstruction p H L₁ T M Vα)
    (hVα : Vα ≤ (L₁ ⊔ T).pCoreIn 2) : starFrattiniIrreducible H c.P L₁ T := by
  let _ : Fact p.Prime := ⟨c.prime⟩
  let P := Source.starImage H c.P
  let K := Source.starImage H (L₁ ⊔ T)
  let A := Source.starImage H Vα
  let B := conjugateSpanBy A K
  let _ : P.Normal := c.Pstar_normal
  have hp : IsPGroup p P := starImage_isPGroup H c.P c.P_isPGroup
  have hKH : L₁ ⊔ T ≤ H := by rw [c.generated]; exact le_sup_right
  have hgen : P ⊔ K = ⊤ := by
    change ((c.P.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) ⊔
      (((L₁ ⊔ T).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = ⊤
    rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup c.P_le hKH, ← c.generated,
      Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hAcore : A ≤ Source.starImage H ((L₁ ⊔ T).pCoreIn 2) := starImage_mono H hVα
  have hBcore : B ≤ Source.starImage H ((L₁ ⊔ T).pCoreIn 2) :=
    conjugateSpanBy_le hAcore (starImage_normalizes H (le_normalizer_pCoreIn 2 _))
  have hb : IsPGroup 2 B :=
    ((starImage_isPGroup H _ (isPGroup_pCoreIn 2 _)).to_subgroup
      (B.subgroupOf (Source.starImage H ((L₁ ⊔ T).pCoreIn 2)))).of_equiv
        (subgroupOfEquivOfLe hBcore)
  have hAB : A ≤ B := le_conjugateSpanBy A K
  have ha : IsPGroup 2 A := (hb.to_subgroup (A.subgroupOf B)).of_equiv
    (subgroupOfEquivOfLe hAB)
  have hfull : ⁅P, B⁆ = P := by
    have hn : (⁅P, B⁆).Normal := by
      apply normalizer_eq_top_iff.mp
      apply top_unique
      rw [← hgen]
      refine sup_le (normalizer_commutator_ge_left P B) ?_
      intro k hk
      rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
        mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (H := P) (show k ∈ K from hk)),
        mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy A K hk)]
    apply le_antisymm (commutator_le_left P B)
    by_contra hnot
    have hcent := c.proper_normal_centralizes ⁅P, B⁆ hn
      (lt_of_le_not_ge (commutator_le_left P B) hnot)
    apply c.moved
    apply commutator_eq_bot_of_coprime_quadratic P A le_normalizer_of_normal
      (by let _ := hp.isNilpotent; infer_instance)
      (IsPGroup.coprime_card_of_ne 2 p (by rintro rfl; have := c.odd; norm_num at this) A P ha hp)
    apply bot_unique
    exact (commutator_mono (commutator_mono le_rfl hAB) le_rfl).trans hcent.le
  intro N hFN hNP hKN
  by_cases he : N = P
  · exact Or.inr he
  · left
    let _ : N.Normal := normal_of_frattini_le P K N hp hgen hFN hNP hKN
    have hNA : ⁅N, A⁆ = ⊥ := c.proper_normal_centralizes N inferInstance (lt_of_le_of_ne hNP he)
    have hBN : B ≤ centralizer (N : Set (Source.Hstar H)) :=
      conjugateSpanBy_le (le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp hNA))
        (hKN.trans (normalizer_le_normalizer_centralizer N))
    apply le_antisymm _ hFN
    exact (le_inf hNP (le_centralizer_iff.mp hBN)).trans
      (centralizer_le_frattini_of_full c.odd P B hp hb hfull)

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Supercritical
end
