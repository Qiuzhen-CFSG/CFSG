module
public import Theory.GroupTheory.FrattiniOddSection
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Factorization.KernelSelection
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Factorization.LocalObstruction
/-!
# The induction step for solvable Thompson factorization

Starting with a failed normalizer product, choose its maximal normal kernel,
then an odd prime line and an actor hyperplane. The Frattini normalizer has
the actual self-centralizing odd section supplied by FrattiniOddSection.
The elementary envelope obstruction now gives a contradiction. Thus only
the ordinary induction on proper Sylow overgroups is needed.

Source: GLS, Number 2, G.26.18(a), printed pp.152–153, at p = 2.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem omega_normalizer_le (J : Subgroup G) :
    normalizer (J : Set G) ≤ normalizer (omegaOneCenterAmbient J : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq] at hx ⊢
  change J.map (MulAut.conj x).toMonoidHom = J at hx
  change (omegaOneCenterAmbient J).map (MulAut.conj x).toMonoidHom = _
  rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj x).injective,hx]

private theorem thompson_normalizer_le (R : Subgroup G) (j : ℕ) :
    normalizer (R : Set G) ≤ normalizer (thompsonJ R j : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (thompsonJ R j).map (MulAut.conj g).toMonoidHom = thompsonJ R j
  have he : R.map (MulAut.conj g).toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp hg
  rw [←thompsonJ_map_equiv,he]

/-- The local obstruction closes the proper-overgroup induction step in
solvable three-prime Thompson factorization. -/
theorem thompson_factorization_of_proper [Group.IsSolvable G]
    (P : Sylow 2 G) (hr : 1 < twoRank (P : Subgroup G))
    (h3 : Nat.Coprime 3 (Nat.card G))
    (hself : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hproper : let U := normalizer (thompsonJ (P : Subgroup G) 0 : Set G)
      let V := normalizer (omegaOneCenterAmbient (thompsonJ (P : Subgroup G) 1) : Set G)
      ∀ D : Subgroup G, D.Normal → D ⊔ (P : Subgroup G) ≠ ⊤ →
        NormalizerProductOn (P : Subgroup G) U V D) :
    NormalizerProductOn (P : Subgroup G)
      (normalizer (thompsonJ (P : Subgroup G) 0 : Set G))
      (normalizer (omegaOneCenterAmbient (thompsonJ (P : Subgroup G) 1) : Set G)) ⊤ := by
  let U := normalizer (thompsonJ (P : Subgroup G) 0 : Set G)
  let V := normalizer (omegaOneCenterAmbient (thompsonJ (P : Subgroup G) 1) : Set G)
  have hPU : (P : Subgroup G) ≤ U :=
    (P : Subgroup G).le_normalizer.trans (thompson_normalizer_le _ 0)
  have hPV : (P : Subgroup G) ≤ V :=
    (P : Subgroup G).le_normalizer.trans ((thompson_normalizer_le _ 1).trans (omega_normalizer_le _))
  by_contra hfail
  obtain ⟨S,hS⟩ := exists_maximalProductKernel (P : Subgroup G) U V hPU hPV
  let := hS.normal
  obtain ⟨r,A,hrp,ho,hA,_,Bbar,D,hBbar,hcard,hAD,hm,hDB,hout⟩ :=
    maximalProductKernel_odd_line P U V S hS hPU hPV le_rfl hfail hproper
  let : Fact r.Prime := ⟨hrp⟩
  let : IsElementaryAbelian 2 A := hA.2.1
  obtain ⟨B,hB,hBA,hi,hker,hmap⟩ := thompson_hyperplane_preimage (P : Subgroup G) A hA
    (QuotientGroup.mk' S) Bbar hBbar
  have hASB : A ⊓ S ≤ B := by simpa only [QuotientGroup.ker_mk'] using hker
  have hDB' : D ≤ centralizer (B.map (QuotientGroup.mk' S) : Set (G ⧸ S)) := by rwa [hmap]
  let H := (D ⊔ A.map (QuotientGroup.mk' S)).comap (QuotientGroup.mk' S)
  let I := S ⊔ B
  let Q := ((P : Subgroup G) ⊓ S) ⊔ B
  let N := H ⊓ normalizer (Q : Set G)
  obtain ⟨_,_,hSyl,hQP,hQN,hAN,hAI,_⟩ :=
    hyperplane_local_normalizer P S A B hA.1 hBA hi hASB D hDB'
  obtain ⟨nn,Y,hYn,hYc,hCY,hmin,hcover⟩ := hyperplane_frattini_odd_section P S A B V
    hA.1 hBA hi hASB (hB.1.trans hPV) D ho hcard hAD hm hDB' hout
  let := nn
  let := hYn
  have hYp : IsPGroup r Y := IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hYc)
  have hYne : Y ≠ ⊥ := by
    intro he
    have hh := (eq_bot_iff_card Y).mp he
    have := hrp.one_lt
    omega
  have hmin' : ∀ Z : Subgroup (N ⧸ I.subgroupOf N), Z.Normal → Z ≤ Y → Z = ⊥ ∨ Z = Y :=
    fun Z _ hz => hmin Z hz
  have hcore : N.pCoreIn 2 = Q :=
    pCoreIn_eq_of_normalized_sylow_and_coreFree_quotient N I Q hSyl hQN inf_le_right
      (twoCore_eq_bot_of_odd_minimal_selfCentralizing Y hYp ho hYne hmin' hCY)
  have hFQ : pCore 2 G ≤ Q :=
    (le_inf (pCore_isPGroup.le_sylow_of_normal P) (hS.pCore_le P U V S)).trans le_sup_left
  have hCQ : N ⊓ centralizer (Q : Set G) ≤ Q :=
    inf_le_right.trans ((centralizer_le hFQ).trans (hself.trans hFQ))
  have hEA : omegaOneCenterAmbient (thompsonJ (P : Subgroup G) 1) ≤ A := by
    have hh := (lemma_B_2_3_2 (P : Subgroup G) (show 0 ≤ 1 by omega) hr).1
    rw [(lemma_B_2_3_2 (P : Subgroup G) (show 0 ≤ 1 by omega) hr).2,thompsonJ_zero] at hh
    apply hh.trans
    change thompsonAlpha (P : Subgroup G) ≤ A
    rw [(lemma_B_2_3_7 (P : Subgroup G)).2]
    exact sInf_le (by rwa [thompsonFamily_zero])
  exact factorization_local_obstruction (P : Subgroup G) Q N B A I hr hB le_sup_right
    hQP (P.isPGroup'.to_le hQP) hQN inf_le_right hCQ hcore (hEA.trans hAN)
    hBA hA.2.1 hAN hAI (h3.of_dvd_right N.card_subgroup_dvd_card)
    Y hYp ho hYne hmin' hCY hcover
end CFSG.Quasithin.ChapterB
