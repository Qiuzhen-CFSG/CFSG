module

public import Theory.GroupTheory.PStar.FixedPoints.CentralSylow
public import Theory.GroupTheory.PStar.SylowBound
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Simultaneous two-star balance and action refinement

Induct on the order of an actual ambient group, proving internal balance
and refinement for every normal two-star subgroup at the same time.
In the refinement step, the residual of an invariant Sylow centralizer is
two-star by the proved 5.4. If it is proper, adjoining the actor still gives
a proper subgroup: otherwise a two-group quotient would kill a nontrivial
two-perfect image. Normalizer chains inside a two-group then supply the
needed nested-centralizer comparison using balance in smaller overgroups.
The central-Sylow branch is proved in the imported supporting module.

For balance, choose a maximal counterexample actor P and put
L = Ostar(C_G(P)), K = Ostar,2(G). An invariant Sylow S of K gives
S₀ = N_S(P). The pair LS₀ is proper, so refinement gives a fixed-core factor
outside K. Its actual normality in C_G(S₀P) makes S₀P another counterexample.
Maximality and the two-group normalizer condition force S ≤ P, contradicting
the corrected Sylow-centralizer bound 5.9.

The only remaining source premise is the existing universal extension
criterion 5.3. The final module supplies its unconditional proof. The external
exports reuse RadicalActionReduction's literal semidirect-product maps.
Source: GLS II, Chapter B, 5.10--5.11 (`refs/KGroup/GLS2/ChapterB.tex`).
-/

open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement

namespace PStarFixedInduction
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- The actual strict decrease needed when adjoining the same two-group actor.
There is no disjointness or semidirect-product cardinality assumption. -/
private theorem smaller_pair (X Y P : Subgroup G) (hX : IsPPerfect 2 X)
    (hP : IsPGroup 2 P) (hYX : Y < X) (hPY : P ≤ normalizer (Y : Set G)) :
    Y ⊔ P < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro htop
  have hn : normalizer (Y : Set G) = ⊤ := by
    apply top_unique
    rw [← htop]
    exact sup_le Y.le_normalizer hPY
  let : Y.Normal := normalizer_eq_top_iff.mp hn
  have hq : IsPGroup 2 (G ⧸ Y) := isPGroup_quotient_of_sup_eq_top Y P hP htop
  have hle : X ≤ Y :=
    (le_pResidual_of_isPPerfect X hX).trans (sInf_le ⟨inferInstance, hq⟩)
  exact not_le_of_gt hYX hle

/-- The residual used for the smaller refinement pair, as a literal subgroup. -/
private def sylowCentralizerResidual (X : Type u) [Group X] (N : Subgroup X)
    (T : Sylow 2 N) : Subgroup X :=
  let C := centralizer ((T : Subgroup N).map N.subtype : Set X)
  (pResidual 2 C).map C.subtype

/-- If the smaller residual equals the original X, the central-Sylow branch
already proved in production applies directly to the original action. -/
private theorem refinement_terminal {X A : Type u} [Group X] [Finite X] [Group A]
    [MulDistribMulAction A X] (hX : IsPStar 2 X) (hA : IsPGroup 2 A)
    (T : Sylow 2 (commutatorAction A X))
    (he : sylowCentralizerResidual X (commutatorAction A X) T = ⊤) :
    commutatorAction A X ⊔ (pStarCore 2 (fixedPointSubgroup A X)).map
      (fixedPointSubgroup A X).subtype = ⊤ := by
  apply hX.commutator_sup_twoStarCore_fixed_of_central_sylow hA T
  apply centralizer_eq_top_iff_subset.mp
  apply top_unique
  rw [← he]
  exact map_subtype_le _

-- Supply the proved normal-product theorem to the corrected GLS 5.9 bound.
private theorem corrected_sylow_bound
    (hext : SylowBoundExtensionCriterion.{u} (p := 2))
    (S : Sylow 2 (pStarPCore 2 G)) :
    centralizer ((S : Subgroup (pStarPCore 2 G)).map (pStarPCore 2 G).subtype : Set G) ≤
      pStarPCore 2 G := by
  apply centralizer_sylow_twoStarPCore_le _ hext S
  intro Y _ _ N M hn hm hN hM
  let : N.Normal := hn
  let : M.Normal := hm
  exact IsPStar.normal_sup_of_centralizerResidual
    (fun Z _ _ hZ K _ P => hZ.isPStar_pResidual_centralizer K P) N M hN hM

/-- The two-group normalizer step in the maximal-counterexample argument. -/
private theorem sylow_actor_containment (S P : Subgroup G) (hS : IsPGroup 2 S)
    (hP : IsPGroup 2 P) (hPS : P ≤ normalizer (S : Set G))
    (hstep : S ⊓ normalizer (P : Set G) ≤ P) : S ≤ P := by
  let V := S ⊔ P
  let Q := P.subgroupOf V
  have hpV : IsPGroup 2 V := hS.to_sup_of_normal_left' hP hPS
  let : Group.IsNilpotent V := hpV.isNilpotent
  have hn : normalizer (Q : Set V) = Q := by
    apply le_antisymm _ Q.le_normalizer
    rw [← subgroupOf_normalizer_eq (show P ≤ V from le_sup_right)]
    intro x hx
    have hv : (x : G) ∈ (S : Set G) * (P : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left S P hPS]
      exact x.property
    obtain ⟨s, hs, p, hp, he⟩ := hv
    change s * p = (x : G) at he
    have hsN : s ∈ normalizer (P : Set G) := by
      have hh := (normalizer (P : Set G)).mul_mem hx
        ((normalizer (P : Set G)).inv_mem (P.le_normalizer hp))
      change (x : G) * p⁻¹ ∈ normalizer (P : Set G) at hh
      simpa only [← he, mul_inv_cancel_right] using hh
    have hp' : s * p ∈ P := P.mul_mem (hstep ⟨hs, hsN⟩) hp
    change (x : G) ∈ P
    rwa [he] at hp'
  have ht : Q = ⊤ := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := V)) Q hn
  exact (show S ≤ V from le_sup_left).trans (subgroupOf_eq_top.mp ht)

/-- A two-perfect subgroup cannot escape the star core while lying in its
star-two extension. This is the first reduction of the balance counterexample. -/
private theorem le_core_of_perfect_le_extension (L : Subgroup G) (hL : IsPPerfect 2 L)
    (hLK : L ≤ pStarPCore 2 G) : L ≤ pStarCore 2 G := by
  let K := pStarPCore 2 G
  let J := L.subgroupOf K
  have hJ : IsPPerfect 2 J := hL.of_surjective
    (subgroupOfEquivOfLe hLK).symm.toMonoidHom (subgroupOfEquivOfLe hLK).symm.surjective
  have hh := map_mono (f := K.subtype) (le_pResidual_of_isPPerfect J hJ)
  rw [map_subgroupOf_eq_of_le hLK, map_pResidual_pStarPCore] at hh
  exact hh

omit [Finite G] in
/-- The smaller pair in the balance step is proper; otherwise L would be
normal in G, forcing the containment excluded by the counterexample. -/
private theorem smaller_balance_pair (L S₀ : Subgroup G) (hL : IsPStar 2 L)
    (hS₀ : S₀ ≤ normalizer (L : Set G)) (hcounter : ¬ L ≤ pStarPCore 2 G) :
    L ⊔ S₀ < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro he
  have hn : normalizer (L : Set G) = ⊤ := by
    apply top_unique
    rw [← he]
    exact sup_le L.le_normalizer hS₀
  let : L.Normal := normalizer_eq_top_iff.mp hn
  exact hcounter ((le_pStarCore L hL).trans pStarCore_le_pStarPCore)


private abbrev coreIn (H : Subgroup G) : Subgroup G := (pStarCore 2 H).map H.subtype

private theorem coreIn_star (H : Subgroup G) : IsPStar 2 (coreIn H) :=
  isPStar_twoStarCore.of_equiv
    ((pStarCore 2 H).equivMapOfInjective H.subtype H.subtype_injective)

private theorem normalizer_coreIn (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer (coreIn H : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
  let a := H.normalizerMonoidHom ⟨g, hg⟩
  have he : (pStarCore 2 H).comap a.toMonoidHom = pStarCore 2 H :=
    (inferInstance : (pStarCore 2 H).Characteristic).fixed a
  have hay : a y ∈ pStarCore 2 H := by
    change y ∈ (pStarCore 2 H).comap a.toMonoidHom
    rw [he]
    exact hy
  exact mem_map.mpr ⟨a y, hay, rfl⟩

private theorem coreIn_le_of_normalized (H D : Subgroup G) (hHD : H ≤ D)
    (hDH : D ≤ normalizer (H : Set G)) : coreIn H ≤ coreIn D := by
  let L := coreIn H
  have hLD : L ≤ D := (map_subtype_le _).trans hHD
  let : (L.subgroupOf D).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLD).mpr (hDH.trans (normalizer_coreIn H))
  have hstar : IsPStar 2 (L.subgroupOf D) :=
    (coreIn_star H).of_equiv (subgroupOfEquivOfLe hLD).symm
  have hh := map_mono (f := D.subtype) (le_pStarCore (L.subgroupOf D) hstar)
  rwa [map_subgroupOf_eq_of_le hLD] at hh

omit [Finite G] in
private theorem normalizer_centralizer (P : Subgroup G) :
    normalizer (P : Set G) ≤ normalizer (centralizer (P : Set G) : Set G) :=
  (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (P : Set G))).mp
    inferInstance

/-- The internal-balance induction step. The refinement premise is only for
actual normalized pairs generating a proper subgroup of this very G; it is
precisely the simultaneous strong-induction hypothesis, not a final premise. -/
private theorem balance_step
    (hext : SylowBoundExtensionCriterion.{u} (p := 2))
    (href : ∀ (L Q : Subgroup G), IsPStar 2 L → IsPGroup 2 Q →
      Q ≤ normalizer (L : Set G) → L ⊔ Q < ⊤ →
      ⁅L, Q⁆ ⊔ coreIn (L ⊓ centralizer (Q : Set G)) = L)
    (P₀ : Subgroup G) (hP₀ : IsPGroup 2 P₀) :
    coreIn (centralizer (P₀ : Set G)) ≤ pStarCore 2 G := by
  classical
  let K := pStarPCore 2 G
  suffices hall : ∀ P : Subgroup G, IsPGroup 2 P → coreIn (centralizer (P : Set G)) ≤ K by
    exact le_core_of_perfect_le_extension _
      ((pResidual_eq_top_iff 2 _).mp (coreIn_star (centralizer (P₀ : Set G))).1)
      (hall P₀ hP₀)
  by_contra hall
  push Not at hall
  obtain ⟨P₀, hP₀, hb₀⟩ := hall
  obtain ⟨P, ⟨hP, hb⟩, hmax⟩ := exists_maximal_of_wellFoundedGT
    (fun P : Subgroup G => IsPGroup 2 P ∧ ¬ coreIn (centralizer (P : Set G)) ≤ K)
    ⟨P₀, hP₀, hb₀⟩
  let C := centralizer (P : Set G)
  let L := coreIn C
  have hL : IsPStar 2 L := coreIn_star C
  have hLC : L ≤ C := map_subtype_le _
  obtain ⟨T, hTI⟩ := PStarAction.exists_invariant_sylow_same_prime (G := K) hP
  let S := (T : Subgroup K).map K.subtype
  have hS : IsPGroup 2 S := T.isPGroup'.map K.subtype
  have hSK : S ≤ K := map_subtype_le _
  have hPS : P ≤ normalizer (S : Set G) := by
    apply le_normalizer_iff.mpr
    intro p hp s hs
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hs
    exact mem_map.mpr ⟨(⟨p, hp⟩ : P) • x,
      (hTI.invariant ⟨p, hp⟩ x).mp hx, rfl⟩
  let S₀ := S ⊓ normalizer (P : Set G)
  have hS₀ : IsPGroup 2 S₀ := hS.of_injective (inclusion inf_le_left)
    (inclusion_injective inf_le_left)
  have hS₀L : S₀ ≤ normalizer (L : Set G) :=
    inf_le_right.trans ((normalizer_centralizer P).trans (normalizer_coreIn C))
  have hproper : L ⊔ S₀ < ⊤ := smaller_balance_pair L S₀ hL hS₀L hb
  have hgen := href L S₀ hL hS₀ hS₀L hproper
  let L₁ := coreIn (L ⊓ centralizer (S₀ : Set G))
  have hcomm : ⁅L, S₀⁆ ≤ K :=
    (commutator_mono le_top (inf_le_left.trans hSK)).trans (commutator_le_right ⊤ K)
  have hb₁ : ¬ L₁ ≤ K := by
    intro hle
    apply hb
    change L ≤ K
    rw [← hgen]
    exact sup_le hcomm hle
  let Q := S₀ ⊔ P
  let D := centralizer (Q : Set G)
  have hDC : D ≤ C := centralizer_le (show P ≤ Q from le_sup_right)
  have hDS₀ : D ≤ centralizer (S₀ : Set G) :=
    centralizer_le (show S₀ ≤ Q from le_sup_left)
  have hHD : L ⊓ centralizer (S₀ : Set G) ≤ D := by
    apply le_centralizer_iff.mpr
    apply sup_le
    · exact le_centralizer_iff.mp inf_le_right
    · exact le_centralizer_iff.mp (inf_le_left.trans hLC)
  have hDH : D ≤ normalizer ((L ⊓ centralizer (S₀ : Set G) : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro d hd x hx
    exact ⟨(mem_normalizer_iff.mp
      ((normalizer_coreIn C) (C.le_normalizer (hDC hd))) x).mp hx.1,
      (mem_normalizer_iff.mp ((centralizer (S₀ : Set G)).le_normalizer (hDS₀ hd)) x).mp hx.2⟩
  have hL₁D : L₁ ≤ coreIn D := coreIn_le_of_normalized _ D hHD hDH
  have hbQ : ¬ coreIn D ≤ K := fun h => hb₁ (hL₁D.trans h)
  have hQ : IsPGroup 2 Q := hS₀.to_sup_of_normal_right' hP inf_le_right
  have hQP : Q ≤ P := hmax ⟨hQ, hbQ⟩ le_sup_right
  have hSP : S ≤ P := sylow_actor_containment S P hS hP hPS (le_sup_left.trans hQP)
  have hLK : L ≤ K := hLC.trans ((centralizer_le hSP).trans (corrected_sylow_bound hext T))
  exact hb hLK


private theorem coreIn_map {H : Type u} [Group H] [Finite H]
    (K : Subgroup G) (f : G →* H) (hf : Function.Injective f) :
    coreIn (K.map f) = (coreIn K).map f := by
  let e := K.equivMapOfInjective f hf
  have hh := congrArg (Subgroup.map (K.map f).subtype)
    (map_pStarCore (p := 2) e)
  rw [map_map] at hh
  rw [show (K.map f).subtype.comp e.toMonoidHom = f.comp K.subtype from rfl] at hh
  simpa only [map_map] using hh.symm

private theorem coreIn_subgroupOf (H Y : Subgroup G) (hHY : H ≤ Y) :
    (coreIn (H.subgroupOf Y)).map Y.subtype = coreIn H := by
  rw [← coreIn_map _ Y.subtype Y.subtype_injective,
    map_subgroupOf_eq_of_le hHY]

omit [Finite G] in
private theorem centralizer_subgroupOf_map (P Y : Subgroup G) (hPY : P ≤ Y) :
    (centralizer (P.subgroupOf Y : Set Y)).map Y.subtype = Y ⊓ centralizer (P : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, fun p hp => congrArg Subtype.val (hy ⟨p, hPY hp⟩ hp)⟩
  · intro hx
    exact mem_map.mpr ⟨⟨x, hx.1⟩, fun p hp => Subtype.ext (hx.2 p hp), rfl⟩

private theorem coreIn_sup_pgroup (D V : Subgroup G) (hV : IsPGroup 2 V)
    (hVD : V ≤ normalizer (D : Set G)) : coreIn (D ⊔ V) = coreIn D := by
  let Y := D ⊔ V
  let E := D.subgroupOf Y
  let W := V.subgroupOf Y
  have hDY : D ≤ Y := le_sup_left
  have hVY : V ≤ Y := le_sup_right
  let : E.Normal := (normal_subgroupOf_iff_le_normalizer hDY).mpr
    (sup_le D.le_normalizer hVD)
  have hW : IsPGroup 2 W := hV.of_equiv (subgroupOfEquivOfLe hVY).symm
  have hgen : E ⊔ W = ⊤ := by
    rw [← subgroupOf_sup hDY hVY, subgroupOf_self]
  have hquot := isPGroup_quotient_of_sup_eq_top E W hW hgen
  have hh := congrArg (Subgroup.map Y.subtype)
    (map_twoStarCore_subtype_eq_of_pgroup_quotient E hquot)
  change (coreIn E).map Y.subtype = coreIn Y at hh
  rw [coreIn_subgroupOf D Y hDY] at hh
  exact hh.symm

private theorem balance_below_in
    (hbal : ∀ Y : Subgroup G, Y < ⊤ → ∀ P : Subgroup Y, IsPGroup 2 P →
      coreIn (centralizer (P : Set Y)) ≤ pStarCore 2 Y)
    (Y P : Subgroup G) (hY : Y < ⊤) (hPY : P ≤ Y) (hP : IsPGroup 2 P) :
    coreIn (Y ⊓ centralizer (P : Set G)) ≤ coreIn Y := by
  have hp : IsPGroup 2 (P.subgroupOf Y) :=
    hP.of_equiv (subgroupOfEquivOfLe hPY).symm
  have hh := map_mono (f := Y.subtype) (hbal Y hY (P.subgroupOf Y) hp)
  rw [← coreIn_map _ Y.subtype Y.subtype_injective,
    centralizer_subgroupOf_map P Y hPY] at hh
  exact hh

private theorem nested_normal_step
    (hbal : ∀ Y : Subgroup G, Y < ⊤ → ∀ P : Subgroup Y, IsPGroup 2 P →
      coreIn (centralizer (P : Set Y)) ≤ pStarCore 2 Y)
    (X Q V : Subgroup G) [X.Normal] (hX : IsPPerfect 2 X)
    (hV : IsPGroup 2 V) (hQV : Q ≤ V) (hVQ : V ≤ normalizer (Q : Set G))
    (hproper : X ⊓ centralizer (Q : Set G) < X) :
    coreIn (X ⊓ centralizer (V : Set G)) ≤ coreIn (X ⊓ centralizer (Q : Set G)) := by
  let D := X ⊓ centralizer (Q : Set G)
  have hVD : V ≤ normalizer (D : Set G) := by
    apply le_normalizer_iff.mpr
    intro v hv d hd
    exact ⟨(inferInstance : X.Normal).conj_mem d hd.1 v,
      (mem_normalizer_iff.mp ((normalizer_centralizer Q) (hVQ hv)) d).mp hd.2⟩
  let Y := D ⊔ V
  have hY : Y < ⊤ := smaller_pair X D V hX hV hproper hVD
  let H := X ⊓ centralizer (V : Set G)
  let B := Y ⊓ centralizer (V : Set G)
  have hHD : H ≤ D := inf_le_inf_left X (centralizer_le hQV)
  have hHB : H ≤ B := le_inf (hHD.trans le_sup_left) inf_le_right
  have hBH : B ≤ normalizer (H : Set G) := by
    apply le_normalizer_iff.mpr
    intro b hb x hx
    exact ⟨(inferInstance : X.Normal).conj_mem x hx.1 b,
      (mem_normalizer_iff.mp ((centralizer (V : Set G)).le_normalizer hb.2) x).mp hx.2⟩
  exact (coreIn_le_of_normalized H B hHB hBH).trans
    ((balance_below_in hbal Y V hY le_sup_right hV).trans
      (coreIn_sup_pgroup D V hV hVD).le)

/-- Nested-centralizer balance needed in the proper refinement branch,
using balance only inside proper actual subgroups of G. -/
private theorem nested_balance_below
    (hbal : ∀ Y : Subgroup G, Y < ⊤ → ∀ P : Subgroup Y, IsPGroup 2 P →
      coreIn (centralizer (P : Set Y)) ≤ pStarCore 2 Y)
    (X R : Subgroup G) [X.Normal] (hX : IsPStar 2 X) (hR : IsPGroup 2 R)
    (P : Subgroup G) (hPR : P ≤ R) :
    coreIn (X ⊓ centralizer (R : Set G)) ≤ coreIn (X ⊓ centralizer (P : Set G)) := by
  let : Group.IsNilpotent R := hR.isNilpotent
  revert hPR
  induction P using WellFoundedGT.induction with
  | ind P ih =>
    intro hPR
    by_cases hc : X ≤ centralizer (P : Set G)
    · rw [inf_of_le_left hc]
      have he : coreIn X = X := by
        rw [coreIn, pStarCore_eq_top hX, ← MonoidHom.range_eq_map, range_subtype]
      rw [he]
      exact (map_subtype_le _).trans inf_le_left
    by_cases he : P = R
    · subst P
      exact le_rfl
    let U := P.subgroupOf R
    have hU : U < ⊤ := by
      apply lt_top_iff_ne_top.mpr
      intro ht
      exact he (le_antisymm hPR (subgroupOf_eq_top.mp ht))
    have hlt := Group.normalizerCondition_of_isNilpotent U hU
    let V := (normalizer (U : Set R)).map R.subtype
    have hPV : P < V := by
      have hh := (map_lt_map_iff_of_injective R.subtype_injective).mpr hlt
      rwa [map_subgroupOf_eq_of_le hPR] at hh
    have hVR : V ≤ R := map_subtype_le _
    have hVP : V ≤ normalizer (P : Set G) := by
      rw [map_le_iff_le_comap, ← subgroupOf_normalizer_eq hPR]
      exact le_rfl
    have hproper : X ⊓ centralizer (P : Set G) < X :=
      lt_of_le_of_ne inf_le_left (fun heq => hc (heq.symm ▸ inf_le_right))
    exact (ih V hPV hVR).trans (nested_normal_step hbal X P V
      ((pResidual_eq_top_iff 2 X).mp hX.1)
      (hR.of_injective (inclusion hVR) (inclusion_injective hVR)) hPV.le hVP hproper)


omit [Finite G] in
private theorem fixed_conj_map (X P : Subgroup G) [X.Normal] :
    (fixedPointSubgroup P X).map X.subtype = X ⊓ centralizer (P : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    intro p hp
    have hh := congrArg Subtype.val (hy ⟨p, hp⟩)
    exact mul_inv_eq_iff_eq_mul.mp hh
  · intro hx
    refine mem_map.mpr ⟨⟨x, hx.1⟩, ?_, rfl⟩
    intro p
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hx.2 p p.property)

private theorem internal_refinement_of_action (X P : Subgroup G) [X.Normal]
    (h : commutatorAction P X ⊔ coreIn (fixedPointSubgroup P X) = ⊤) :
    ⁅X, P⁆ ⊔ coreIn (X ⊓ centralizer (P : Set G)) = X := by
  have hh := congrArg (Subgroup.map X.subtype) h
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype,
    commutatorAction_subgroup_conj_map_eq_commutator X P le_normalizer_of_normal,
    ← coreIn_map _ X.subtype X.subtype_injective, fixed_conj_map] at hh
  exact hh

omit [Finite G] in
private theorem map_normalized_of_invariant (X P : Subgroup G) [X.Normal]
    (H : Subgroup X) [IsInvariant P X H] :
    P ≤ normalizer (H.map X.subtype : Set G) := by
  apply le_normalizer_iff.mpr
  intro p hp x hx
  obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
  exact mem_map.mpr ⟨(⟨p, hp⟩ : P) • y,
    (IsInvariant.invariant (A := P) (G := X) (H := H) ⟨p, hp⟩ y).mp hy, rfl⟩

omit [Finite G] in
private theorem normalizer_characteristic_image (H : Subgroup G) (J : Subgroup H)
    [J.Characteristic] : normalizer (H : Set G) ≤ normalizer (J.map H.subtype : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
  let a := H.normalizerMonoidHom ⟨g, hg⟩
  have he : J.comap a.toMonoidHom = J := (inferInstance : J.Characteristic).fixed a
  have hay : a y ∈ J := by
    change y ∈ J.comap a.toMonoidHom
    rw [he]
    exact hy
  exact mem_map.mpr ⟨a y, hay, rfl⟩

/-- The proper branch of refinement uses only balance in proper actual
subgroups and refinement for proper actual normalized pairs. -/
private theorem refinement_step
    (hbal : ∀ Y : Subgroup G, Y < ⊤ → ∀ P : Subgroup Y, IsPGroup 2 P →
      coreIn (centralizer (P : Set Y)) ≤ pStarCore 2 Y)
    (href : ∀ (L Q : Subgroup G), IsPStar 2 L → IsPGroup 2 Q →
      Q ≤ normalizer (L : Set G) → L ⊔ Q < ⊤ →
      ⁅L, Q⁆ ⊔ coreIn (L ⊓ centralizer (Q : Set G)) = L)
    (X P : Subgroup G) [X.Normal] (hX : IsPStar 2 X) (hP : IsPGroup 2 P) :
    ⁅X, P⁆ ⊔ coreIn (X ⊓ centralizer (P : Set G)) = X := by
  let N := commutatorAction P X
  let : N.Normal := commutatorAction_normal
  let : IsInvariant P X N := commutatorAction_isInvariant
  obtain ⟨T, hTI⟩ := PStarAction.exists_invariant_sylow_same_prime (G := N) hP
  let : IsInvariant P N (T : Subgroup N) := hTI
  let Sx := (T : Subgroup N).map N.subtype
  let : IsInvariant P X Sx := isInvariant_map_subtype N (T : Subgroup N)
  let Cx := centralizer (Sx : Set X)
  let : IsInvariant P X Cx := isInvariant_centralizer Sx
  let Rx := pResidual 2 Cx
  let : IsInvariant P Cx Rx := isInvariant_of_characteristic Rx
  let R := Rx.map Cx.subtype
  let : IsInvariant P X R := isInvariant_map_subtype Cx Rx
  by_cases hR : R = ⊤
  · apply internal_refinement_of_action X P
    exact refinement_terminal hX hP T hR
  let X₁ := R.map X.subtype
  let S := Sx.map X.subtype
  let C := Cx.map X.subtype
  have hS : IsPGroup 2 S := (T.isPGroup'.map N.subtype).map X.subtype
  have hPS : P ≤ normalizer (S : Set G) := map_normalized_of_invariant X P Sx
  have hPX₁ : P ≤ normalizer (X₁ : Set G) := map_normalized_of_invariant X P R
  have hX₁X : X₁ < X := by
    have hh := (map_lt_map_iff_of_injective X.subtype_injective).mpr (lt_top_iff_ne_top.mpr hR)
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hh
  have hproper : X₁ ⊔ P < ⊤ := smaller_pair X X₁ P
    ((pResidual_eq_top_iff 2 X).mp hX.1) hP hX₁X hPX₁
  have hRxstar : IsPStar 2 Rx := hX.isPStar_pResidual_centralizer N T
  have hX₁star : IsPStar 2 X₁ :=
    (hRxstar.of_equiv (Rx.equivMapOfInjective Cx.subtype Cx.subtype_injective)).of_equiv
      (R.equivMapOfInjective X.subtype X.subtype_injective)
  have hrec := href X₁ P hX₁star hP hPX₁ hproper
  have hNR : ⁅X, P⁆ ⊔ X₁ = X := by
    have hh := congrArg (Subgroup.map X.subtype) (hX.sup_pResidual_centralizer_eq_top N T)
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype,
      commutatorAction_subgroup_conj_map_eq_commutator X P le_normalizer_of_normal] at hh
    exact hh
  have hC : C = X ⊓ centralizer (S : Set G) := by
    have hh := centralizer_subgroupOf_map S X (map_subtype_le _)
    have hs : S.subgroupOf X = Sx := comap_map_eq_self_of_injective X.subtype_injective Sx
    rw [hs] at hh
    exact hh
  have hX₁C : X₁ ≤ C := map_mono (map_subtype_le _)
  have hX₁res : X₁ = (pResidual 2 C).map C.subtype :=
    map_embedded_pResidual 2 Cx X.subtype
  have hCX₁ : C ≤ normalizer (X₁ : Set G) := by
    rw [hX₁res]
    exact C.le_normalizer.trans (normalizer_characteristic_image C (pResidual 2 C))
  let D := X ⊓ centralizer ((S ⊔ P : Subgroup G) : Set G)
  let H := X₁ ⊓ centralizer (P : Set G)
  have hDC : D ≤ C := by
    rw [hC]
    exact inf_le_inf_left X (centralizer_le (show S ≤ S ⊔ P from le_sup_left))
  have hDP : D ≤ centralizer (P : Set G) :=
    inf_le_right.trans (centralizer_le (show P ≤ S ⊔ P from le_sup_right))
  have hHD : H ≤ D := by
    apply le_inf (inf_le_left.trans hX₁X.le)
    apply le_centralizer_iff.mpr
    apply sup_le
    · apply le_centralizer_iff.mp
      exact inf_le_left.trans (hX₁C.trans (hC.le.trans inf_le_right))
    · exact le_centralizer_iff.mp inf_le_right
  have hDH : D ≤ normalizer (H : Set G) := by
    apply le_normalizer_iff.mpr
    intro d hd x hx
    exact ⟨(mem_normalizer_iff.mp (hCX₁ (hDC hd)) x).mp hx.1,
      (mem_normalizer_iff.mp ((centralizer (P : Set G)).le_normalizer (hDP hd)) x).mp hx.2⟩
  have hcores : coreIn H ≤ coreIn (X ⊓ centralizer (P : Set G)) :=
    (coreIn_le_of_normalized H D hHD hDH).trans
      (nested_balance_below hbal X (S ⊔ P) hX (hS.to_sup_of_normal_left' hP hPS) P le_sup_right)
  apply le_antisymm
  · exact sup_le (commutator_le_left X P) ((map_subtype_le _).trans inf_le_left)
  · calc
      X = ⁅X, P⁆ ⊔ X₁ := hNR.symm
      _ ≤ ⁅X, P⁆ ⊔ coreIn (X ⊓ centralizer (P : Set G)) := by
        apply sup_le le_sup_left
        rw [← hrec]
        exact sup_le ((commutator_mono hX₁X.le le_rfl).trans le_sup_left)
          (hcores.trans le_sup_right)


omit [Finite G] in
private theorem relative_fixed_map (L Q Y : Subgroup G) (hLY : L ≤ Y) (hQY : Q ≤ Y) :
    ((L.subgroupOf Y) ⊓ centralizer (Q.subgroupOf Y : Set Y)).map Y.subtype =
      L ⊓ centralizer (Q : Set G) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hc⟩, rfl⟩
    exact ⟨hy, fun q hq => congrArg Subtype.val (hc ⟨q, hQY hq⟩ hq)⟩
  · intro hx
    exact mem_map.mpr ⟨⟨x, hLY hx.1⟩, ⟨hx.1, fun q hq => Subtype.ext (hx.2 q hq)⟩, rfl⟩

private theorem refinement_below_in
    (href : ∀ Y : Subgroup G, Y < ⊤ → ∀ (X P : Subgroup Y) [X.Normal],
      IsPStar 2 X → IsPGroup 2 P → ⁅X, P⁆ ⊔ coreIn (X ⊓ centralizer (P : Set Y)) = X)
    (L Q : Subgroup G) (hL : IsPStar 2 L) (hQ : IsPGroup 2 Q)
    (hQL : Q ≤ normalizer (L : Set G)) (hproper : L ⊔ Q < ⊤) :
    ⁅L, Q⁆ ⊔ coreIn (L ⊓ centralizer (Q : Set G)) = L := by
  let Y := L ⊔ Q
  let X := L.subgroupOf Y
  let P := Q.subgroupOf Y
  have hLY : L ≤ Y := le_sup_left
  have hQY : Q ≤ Y := le_sup_right
  let : X.Normal := (normal_subgroupOf_iff_le_normalizer hLY).mpr
    (sup_le L.le_normalizer hQL)
  have hx : IsPStar 2 X := hL.of_equiv (subgroupOfEquivOfLe hLY).symm
  have hp : IsPGroup 2 P := hQ.of_equiv (subgroupOfEquivOfLe hQY).symm
  have hh := congrArg (Subgroup.map Y.subtype) (href Y hproper X P hx hp)
  rw [Subgroup.map_sup, map_commutator, map_subgroupOf_eq_of_le hLY,
    map_subgroupOf_eq_of_le hQY, ← coreIn_map _ Y.subtype Y.subtype_injective,
    relative_fixed_map L Q Y hLY hQY] at hh
  exact hh

/-- Simultaneous induction, using only the existing universal 5.3 criterion. -/
private theorem internal_family_of_extension
    (hext : SylowBoundExtensionCriterion.{u} (p := 2)) :
    (∀ P : Subgroup G, IsPGroup 2 P → coreIn (centralizer (P : Set G)) ≤ pStarCore 2 G) ∧
    (∀ (X P : Subgroup G) [X.Normal], IsPStar 2 X → IsPGroup 2 P →
      ⁅X, P⁆ ⊔ coreIn (X ⊓ centralizer (P : Set G)) = X) := by
  suffices ∀ n (Y : Type u) [Group Y] [Finite Y], Nat.card Y = n →
      (∀ P : Subgroup Y, IsPGroup 2 P → coreIn (centralizer (P : Set Y)) ≤ pStarCore 2 Y) ∧
      (∀ (X P : Subgroup Y) [X.Normal], IsPStar 2 X → IsPGroup 2 P →
        ⁅X, P⁆ ⊔ coreIn (X ⊓ centralizer (P : Set Y)) = X) from this _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Y _ _ hcard
    have smaller (Z : Subgroup Y) (hz : Z < ⊤) : Nat.card Z < n := by
      rw [← hcard]
      exact lt_of_le_of_ne Z.card_le_card_group
        (fun he => hz.ne (Z.card_eq_iff_eq_top.mp he))
    have hb : ∀ Z : Subgroup Y, Z < ⊤ → ∀ P : Subgroup Z, IsPGroup 2 P →
        coreIn (centralizer (P : Set Z)) ≤ pStarCore 2 Z :=
      fun Z hz => (ih (Nat.card Z) (smaller Z hz) Z rfl).1
    have hr : ∀ Z : Subgroup Y, Z < ⊤ → ∀ (X P : Subgroup Z) [X.Normal],
        IsPStar 2 X → IsPGroup 2 P → ⁅X, P⁆ ⊔ coreIn (X ⊓ centralizer (P : Set Z)) = X :=
      fun Z hz => (ih (Nat.card Z) (smaller Z hz) Z rfl).2
    have hpairs := refinement_below_in hr
    exact ⟨balance_step hext hpairs, fun X P _ hX hP => refinement_step hb hpairs X P hX hP⟩

end PStarFixedInduction
namespace Subgroup
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Internal two-star balance, with only the universal GLS 5.3 criterion explicit. -/
public theorem map_twoStarCore_centralizer_le_of_extension
    (hext : Theory.GroupTheory.SylowBoundExtensionCriterion.{u} (p := 2))
    (P : Subgroup G) (hP : IsPGroup 2 P) :
    (pStarCore 2 (centralizer (P : Set G))).map (centralizer (P : Set G)).subtype ≤
      pStarCore 2 G :=
  (PStarFixedInduction.internal_family_of_extension hext).1 P hP
end Subgroup

namespace Theory.GroupTheory.PStarAction
universe u v
variable {G : Type u} {A : Type v} [Group G] [Finite G] [Group A] [Finite A]
  [MulDistribMulAction A G]

/-- GLS 5.11 for the original action, reduced through the literal semidirect product. -/
public theorem map_twoStarCore_fixedPoint_le_of_extension
    (hext : SylowBoundExtensionCriterion.{max u v} (p := 2)) (hA : IsPGroup 2 A) :
    (pStarCore 2 (fixedPointSubgroup A G)).map (fixedPointSubgroup A G).subtype ≤
      pStarCore 2 G := by
  let SD := G ⋊[MulDistribMulAction.toMulAut A G] A
  let : Finite SD := Finite.of_equiv (G × A) SemidirectProduct.equivProd.symm
  let actor := (SemidirectProduct.inr : A →* SD).range
  have hactor : IsPGroup 2 actor := hA.of_surjective
    (SemidirectProduct.inr : A →* SD).rangeRestrict
    (SemidirectProduct.inr : A →* SD).rangeRestrict_surjective
  apply (twoStarCore_balance_iff_semidirect hA).mpr
  exact map_twoStarCore_centralizer_le_of_extension hext actor hactor
end Theory.GroupTheory.PStarAction


namespace Theory.GroupTheory.PStarAction
universe u v
variable {G : Type u} {A : Type v} [Group G] [Finite G] [Group A] [Finite A]
  [MulDistribMulAction A G]

/-- GLS 5.10 for the original action, with the existing radical transport
identifying the fixed-core factor in the semidirect product. -/
public theorem commutator_sup_twoStarCore_fixed_of_extension
    (hext : SylowBoundExtensionCriterion.{max u v} (p := 2))
    (hG : IsPStar 2 G) (hA : IsPGroup 2 A) :
    commutatorAction A G ⊔ (pStarCore 2 (fixedPointSubgroup A G)).map
      (fixedPointSubgroup A G).subtype = ⊤ := by
  let φ := MulDistribMulAction.toMulAut A G
  let SD := G ⋊[φ] A
  let : Finite SD := Finite.of_equiv (G × A) SemidirectProduct.equivProd.symm
  let j : G →* SD := SemidirectProduct.inl
  let X := j.range
  let P := (SemidirectProduct.inr : A →* SD).range
  let C := centralizer (P : Set SD)
  let : X.Normal := by
    change (SemidirectProduct.inl : G →* SD).range.Normal
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hX : IsPStar 2 X := hG.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  have hP : IsPGroup 2 P := hA.of_surjective
    (SemidirectProduct.inr : A →* SD).rangeRestrict
    (SemidirectProduct.inr : A →* SD).rangeRestrict_surjective
  have hrec := (PStarFixedInduction.internal_family_of_extension hext (G := SD)).2 X P hX hP
  have hnorm : C ≤ normalizer ((X ⊓ C : Subgroup SD) : Set SD) := by
    apply le_normalizer_iff.mpr
    intro c hc x hx
    exact ⟨(inferInstance : X.Normal).conj_mem x hx.1 c,
      (mem_normalizer_iff.mp (C.le_normalizer hc) x).mp hx.2⟩
  have hcores : PStarFixedInduction.coreIn (X ⊓ C) ≤ PStarFixedInduction.coreIn C :=
    PStarFixedInduction.coreIn_le_of_normalized _ _ inf_le_right hnorm
  have hcomm : ⁅X, P⁆ ≤ (commutatorAction A G).map j := by
    apply commutator_le.mpr
    rintro _ ⟨g, rfl⟩ _ ⟨a, rfl⟩
    have he := semidirect_comm_inl_inv_inr φ a g⁻¹
    simp only [map_inv, inv_inv] at he
    change ⁅SemidirectProduct.inl g, SemidirectProduct.inr a⁆ ∈ _
    rw [he]
    exact mem_map.mpr ⟨g * (a • g⁻¹), subset_closure ⟨a, g⁻¹, mem_top _, by simp⟩, by
      change j (g * (a • g⁻¹)) = j (g * (a • g)⁻¹)
      rw [smul_inv']⟩
  have hh : X ≤ (commutatorAction A G ⊔
      (pStarCore 2 (fixedPointSubgroup A G)).map (fixedPointSubgroup A G).subtype).map j := by
    rw [Subgroup.map_sup]
    change X ≤ (commutatorAction A G).map j ⊔
      ((pStarCore 2 (fixedPointSubgroup A G)).map (fixedPointSubgroup A G).subtype).map
        (SemidirectProduct.inl : G →* SD)
    rw [map_twoStarCore_fixedPoint_semidirect hA]
    exact hrec.symm.le.trans (sup_le_sup hcomm hcores)
  apply top_unique
  apply (map_le_map_iff_of_injective (f := j) SemidirectProduct.inl_injective).mp
  rw [← MonoidHom.range_eq_map]
  exact hh
end Theory.GroupTheory.PStarAction
