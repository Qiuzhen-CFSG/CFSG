module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Residual
public import Theory.GroupTheory.SylowThreeNormalizerSection
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# Cubic splitting and the Frattini choice in the natural-layer cases

Coprime action of an actual Sylow three-subgroup gives the decomposition
Q = [Q,Y_L] C_Q(P_L). After Y_C fixes Q, the same argument for a Sylow
subgroup P of Y gives Q ≤ O₂(Y_L) C_S(P).

The Frattini factorization writes an outside element of T as t r, with
t normalizing P and r in O₂(Y) ≤ S. This preserves both the outside coset
and residual exchange. Since S has index two, t also preserves C_S(P).
The S-part of the section-action kernel is normal in LS and is a two-group;
this proves the final bound Qᵗ ≤ O₂(LS) once the natural-layer action gives
Y_C ≤ C_G(Q) and C_S(P) ≤ C_G(L/O₂(L)). Those two model facts are explicit
premises here, not assertions of the source theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
last paragraph of the proof of 15.3.23, printed p.1129 (PDF p.1146).
-/

@[expose] public section
open Subgroup
open scoped commutatorElement Pointwise

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions
variable {G : Type*} [Group G] [Finite G]

/-- Ambient realization of a Sylow three-subgroup of the actual Y. -/
noncomputable abbrev sylowThree (d : LocalData G) (P : Sylow 3 d.Y) : Subgroup G :=
  (P : Subgroup d.Y).map d.Y.subtype

/-- Core displacement and a cubic fixed subgroup generate Q. This uses
coprime action only for the actual three-subgroup P, not for Y_L or Y_C. -/
theorem core_decomposition_of_three_subgroup (L A P : Subgroup G)
    (hAL : A ≤ L) (hPA : P ≤ A) (hP : IsPGroup 3 P) :
    commutatorCore L = ⁅commutatorCore L, A⁆ ⊔
      (commutatorCore L ⊓ centralizer (P : Set G)) := by
  have hQ := (L.isPGroup_pCoreIn 2).to_le (commutatorCore_le L)
  let _ : Group.IsNilpotent (commutatorCore L) := hQ.isNilpotent
  have hAQ := hAL.trans (normalizer_commutator_ge_right (L.pCoreIn 2) L)
  have hd := eq_commutator_sup_centralizer_of_solvable_coprime
    (commutatorCore L) P (hPA.trans hAQ) inferInstance
    (IsPGroup.coprime_card_of_ne 3 2 (by decide) P (commutatorCore L) hP hQ)
  apply le_antisymm
  · exact hd.le.trans (sup_le_sup_right (commutator_mono le_rfl hPA) _)
  · exact sup_le (le_normalizer_iff_commutator_le_left.mp hAQ) inf_le_left

/-- The literal product form with a Sylow three-subgroup of Y_L. -/
theorem core_YL_decomposition (d : LocalData G) (L : Subgroup G)
    (P : Sylow 3 (YL d L)) :
    (commutatorCore L : Set G) = ((⁅commutatorCore L, YL d L⁆ : Subgroup G) : Set G) *
      (commutatorCore L ⊓ centralizer ((P : Subgroup (YL d L)).map (YL d L).subtype : Set G) : Set G) := by
  have hYL : YL d L ≤ L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have he := core_decomposition_of_three_subgroup L (YL d L)
    ((P : Subgroup (YL d L)).map (YL d L).subtype) hYL (map_subtype_le _)
    (P.isPGroup'.map _)
  calc
    (commutatorCore L : Set G) =
        ↑(⁅commutatorCore L, YL d L⁆ ⊔ (commutatorCore L ⊓
          centralizer ((P : Subgroup (YL d L)).map (YL d L).subtype : Set G))) :=
      congrArg (fun H : Subgroup G => (H : Set G)) he
    _ = _ := coe_mul_of_right_le_normalizer_left _ _
      (inf_le_left.trans (normalizer_commutator_ge_left _ _))

/-- Once Y_C fixes L, cubic splitting for a Sylow subgroup of Y gives the
source bound Q ≤ O₂(Y_L) C_S(P). -/
theorem core_le_YL_core_sup_sylow_centralizer (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (hY : d.Y = YL d c.L ⊔ YC d c.L)
    (hSQ : commutatorCore c.L ≤ d.S)
    (hSYL : d.S ≤ normalizer (YL d c.L : Set G))
    (hfix : YC d c.L ≤ centralizer (commutatorCore c.L : Set G))
    (P : Sylow 3 d.Y) :
    commutatorCore c.L ≤ (YL d c.L).pCoreIn 2 ⊔
      (d.S ⊓ centralizer (sylowThree d P : Set G)) := by
  have hCL := YC_centralizes_of_core_fixed d c hfix
  have hYL : YL d c.L ≤ c.L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hYN : d.Y ≤ normalizer (c.L : Set G) := by
    rw [hY]
    exact sup_le (hYL.trans c.L.le_normalizer) (YC_section_action d c.L).1
  have hQN := hYN.trans (normalizer_le_normalizer_commutatorCore c.L)
  have hQ := (c.L.isPGroup_pCoreIn 2).to_le (commutatorCore_le c.L)
  let _ : Group.IsNilpotent (commutatorCore c.L) := hQ.isNilpotent
  have hd := eq_commutator_sup_centralizer_of_solvable_coprime
    (commutatorCore c.L) (sylowThree d P) ((map_subtype_le _).trans hQN) inferInstance
    (IsPGroup.coprime_card_of_ne 3 2 (by decide) (sylowThree d P) (commutatorCore c.L)
      (P.isPGroup'.map _) hQ)
  have hPY : sylowThree d P ≤ YL d c.L ⊔ YC d c.L := (map_subtype_le _).trans hY.le
  have hprod : ((YL d c.L ⊔ YC d c.L : Subgroup G) : Set G) =
      (YL d c.L : Set G) * (YC d c.L : Set G) :=
    coe_mul_of_right_le_normalizer_left _ _
      (hCL.trans ((centralizer_le hYL).trans (Subgroup.centralizer_le_normalizer _)))
  have hc : ⁅commutatorCore c.L, sylowThree d P⁆ ≤ ⁅commutatorCore c.L, YL d c.L⁆ := by
    apply commutator_le.mpr
    intro q hq p hp
    have hp' : p ∈ (YL d c.L : Set G) * (YC d c.L : Set G) := by
      rw [← hprod]
      exact hPY hp
    obtain ⟨a, ha, b, hb, rfl⟩ := hp'
    have hqb : ⁅q, b⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr ((hfix hb q hq))
    rw [commutatorElement_mul_right_eq_mul_conj, hqb, mul_one, mul_inv_cancel_right]
    exact commutator_mem_commutator hq ha
  exact hd.le.trans (sup_le
    (hc.trans (core_YL_commutator_le d c.L hSQ hSYL) |>.trans le_sup_left)
    ((inf_le_inf hSQ le_rfl).trans le_sup_right))

/-- Both intrinsic residual cores lie in R and hence in S. -/
theorem residual_cores_le_S (d : LocalData G) (L : Subgroup G)
    (hplus : d.Yplus ≤ normalizer (L : Set G))
    (hSY : d.S ≤ normalizer (d.Yplus : Set G))
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    (YL d L).pCoreIn 2 ⊔ (YC d L).pCoreIn 2 ≤ d.S := by
  have hYS : d.Yplus ⊔ d.S ≤ normalizer (d.Yplus : Set G) :=
    sup_le d.Yplus.le_normalizer hSY
  have hcore : d.Yplus.pCoreIn 2 ≤ d.R :=
    le_pCoreIn_of_normalizes (d.Yplus.isPGroup_pCoreIn 2)
      ((d.Yplus.pCoreIn_le 2).trans le_sup_left)
      (hYS.trans (normalizer_le_normalizer_characteristic_image d.Yplus (pCore 2 d.Yplus)))
  have hbound (A : Subgroup G) (hAY : A ≤ d.Yplus)
      (hYA : d.Yplus ≤ normalizer (A : Set G)) : A.pCoreIn 2 ≤ d.S := by
    have h := le_pCoreIn_of_normalizes (A.isPGroup_pCoreIn 2)
      ((A.pCoreIn_le 2).trans hAY)
      (hYA.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
    exact h.trans (hcore.trans (R_le_S d hR))
  exact sup_le
    (hbound _ ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_left)
      (ComponentIntersection.normalizes_intersectionResidual hplus))
    (hbound _ ((ComponentIntersection.centralizerResidual_le _ _).trans inf_le_left)
      (ComponentIntersection.normalizes_centralizerResidual hplus))

omit [Finite G] in
/-- The S-part of the genuine section kernel is a normal two-subgroup of LS. -/
theorem S_sectionCentralizer_le_core (d : LocalData G) (L : Subgroup G)
    (hSL : d.S ≤ normalizer (L : Set G)) (hcore : L.pCoreIn 2 ≤ d.S) :
    d.S ⊓ Chapter4.sectionCentralizer L ≤ (L ⊔ d.S).pCoreIn 2 := by
  let K := d.S ⊓ Chapter4.sectionCentralizer L
  have hNR : normalizer (L : Set G) ≤ normalizer (L.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  have hSK : d.S ≤ normalizer (K : Set G) := by
    apply (le_inf d.S.le_normalizer ?_).trans inf_normalizer_le_normalizer_inf
    exact commutatorPreimage_normalized _ _ _ _ hNR
      (hSL.trans (normalizer (L : Set G)).le_normalizer) hSL (hSL.trans hNR)
  have hRK : L.pCoreIn 2 ≤ K := le_inf hcore
    ((Chapter4.le_sectionCentralizer_iff _ L).mpr
      ⟨(L.pCoreIn_le 2).trans L.le_normalizer,
        le_normalizer_iff_commutator_le_left.mp (L.le_normalizer.trans hNR)⟩)
  have hLK : L ≤ normalizer (K : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((Chapter4.le_sectionCentralizer_iff K L).mp inf_le_right).2.trans hRK)
  exact le_pCoreIn_of_normalizes
    (d.T.isPGroup'.to_le (inf_le_left.trans (show d.S ≤ (d.T : Subgroup G) from inf_le_left)))
    (inf_le_left.trans le_sup_right) (sup_le hLK hSK)

/-- A cubic Sylow subgroup and the two-core generate Y whenever the actual
two-core quotient is a three-group. -/
theorem sylowThree_sup_core (d : LocalData G) (P : Sylow 3 d.Y)
    (hquot : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y)) :
    sylowThree d P ⊔ d.Y.pCoreIn 2 = d.Y := by
  have h := congrArg (map d.Y.subtype) (P.sup_eq_top_of_quotient_isPGroup (pCore 2 d.Y) hquot)
  simpa only [sylowThree, pCoreIn, Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] using h

/-- Frattini adjustment inside T preserves the outside coset and residual
exchange, while making its representative normalize any chosen Sylow three-group. -/
theorem exists_exchange_normalizing_sylow (d : LocalData G) (L : Subgroup G)
    (hY : d.Y = d.Yplus)
    (hTY : (d.T : Subgroup G) ≤ normalizer (d.Y : Set G))
    (hSYL : d.S ≤ normalizer (YL d L : Set G))
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (P : Sylow 3 d.Y) (hquot : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y))
    (t₀ : G) (ht₀ : t₀ ∈ (d.T : Subgroup G)) (ht₀S : t₀ ∉ d.S)
    (hexchange : (YL d L).conjBy t₀ = YC d L) :
    ∃ t : G, t ∈ (d.T : Subgroup G) ∧ t ∉ d.S ∧
      (YL d L).conjBy t = YC d L ∧ t ∈ normalizer (sylowThree d P : Set G) := by
  have hSY : d.S ≤ normalizer (d.Y : Set G) := inf_le_left.trans hTY
  have hYR : d.Y ≤ normalizer (d.Y.pCoreIn 2 : Set G) :=
    d.Y.le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 d.Y))
  have hTR : (d.T : Subgroup G) ≤ normalizer (d.Y.pCoreIn 2 : Set G) :=
    hTY.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 d.Y))
  have hcore : d.Y.pCoreIn 2 ≤ d.R := by
    rw [show d.R = (d.Y ⊔ d.S).pCoreIn 2 by rw [hY]]
    exact le_pCoreIn_of_normalizes (d.Y.isPGroup_pCoreIn 2)
      ((d.Y.pCoreIn_le 2).trans le_sup_left)
      ((sup_le d.Y.le_normalizer hSY).trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 d.Y)))
  have hRS := hcore.trans (R_le_S d hR)
  obtain ⟨t, ht, r, hr, htr⟩ := SylowThreeNormalizer.normalizer_factorization
    d.Y (d.Y.pCoreIn 2) (d.T : Subgroup G) P (sylowThree_sup_core d P hquot)
    (hRS.trans inf_le_left) hYR hTR hTY ⟨t₀, ht₀⟩
  refine ⟨t, ht.1, ?_, ?_, ht.2⟩
  · intro htS
    have he : t * r = t₀ := htr
    exact ht₀S (he ▸ d.S.mul_mem htS (hRS hr))
  · have he : (YL d L).conjBy r = YL d L :=
      mem_normalizer_iff_map_conj_eq.mp (hSYL (hRS hr))
    have ht0 : t * r = t₀ := htr
    rw [← ht0, conjBy_mul, he] at hexchange
    exact hexchange

omit [Finite G] in
/-- A normalizing outside element also preserves C_S(P), since S has index two in T. -/
theorem normalizes_sylow_centralizer (d : LocalData G) (P : Sylow 3 d.Y)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (t : G) (ht : t ∈ (d.T : Subgroup G))
    (htP : t ∈ normalizer (sylowThree d P : Set G)) :
    t ∈ normalizer ((d.S ⊓ centralizer (sylowThree d P : Set G) : Subgroup G) : Set G) := by
  have hTS : (d.T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hindex)
  exact inf_normalizer_le_normalizer_inf
    ⟨hTS ht, normalizer_le_normalizer_centralizer _ htP⟩

/-- The one- and two-natural-layer branches reduce to two actual action
facts: Y_C fixes Q and C_S(P) fixes L/O₂(L). The Frattini representative,
its exchange, and its conjugate-core bound are constructed here. -/
theorem exists_conjugate_core_le_of_actions (d : LocalData G)
    {I : Subgroup G} (c : ComponentWitness d I)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hSL : d.S ≤ normalizer (c.L : Set G))
    (hYplus : d.Y = d.Yplus) (hY : d.Y = YL d c.L ⊔ YC d c.L)
    (hTY : (d.T : Subgroup G) ≤ normalizer (d.Y : Set G))
    (hquot : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y))
    (hfix : YC d c.L ≤ centralizer (commutatorCore c.L : Set G))
    (P : Sylow 3 d.Y)
    (hCP : d.S ⊓ centralizer (sylowThree d P : Set G) ≤ Chapter4.sectionCentralizer c.L)
    (t₀ : G) (ht₀ : t₀ ∈ (d.T : Subgroup G)) (ht₀S : t₀ ∉ d.S)
    (hexchange : (YL d c.L).conjBy t₀ = YC d c.L) :
    ∃ t : G, t ∈ (d.T : Subgroup G) ∧ t ∉ d.S ∧
      (YL d c.L).conjBy t = YC d c.L ∧
      t ∈ normalizer (sylowThree d P : Set G) ∧
      (commutatorCore c.L).conjBy t ≤ (c.L ⊔ d.S).pCoreIn 2 := by
  have hSY : d.S ≤ normalizer (d.Yplus : Set G) :=
    hYplus ▸ (inf_le_left.trans hTY)
  have hSYL := S_normalizes_YL d c.L hSY hSL
  obtain ⟨t, ht, htS, he, htP⟩ := exists_exchange_normalizing_sylow
    d c.L hYplus hTY hSYL hR P hquot t₀ ht₀ ht₀S hexchange
  refine ⟨t, ht, htS, he, htP, ?_⟩
  have hQ := core_le_YL_core_sup_sylow_centralizer d c hY
    (commutatorCore_le_S d c.L hcore hR) hSYL hfix P
  have hmap := map_mono (f := (MulAut.conj t).toMonoidHom) hQ
  have hfixC := mem_normalizer_iff_map_conj_eq.mp (normalizes_sylow_centralizer d P hindex t ht htP)
  change (d.S ⊓ centralizer (sylowThree d P : Set G)).map (MulAut.conj t).toMonoidHom = _ at hfixC
  rw [Subgroup.map_sup, hfixC] at hmap
  change (commutatorCore c.L).conjBy t ≤ ((YL d c.L).pCoreIn 2).conjBy t ⊔ _ at hmap
  rw [conjugate_YL_core d c.L t he] at hmap
  have hkernel := S_sectionCentralizer_le_core d c.L hSL (hcore.trans (R_le_S d hR))
  have hplus : d.Yplus ≤ normalizer (c.L : Set G) := by
    rw [← hYplus, hY]
    exact sup_le
      (((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right).trans c.L.le_normalizer)
      (YC_section_action d c.L).1
  have hCS : (YC d c.L).pCoreIn 2 ≤ d.S :=
    le_sup_right.trans (residual_cores_le_S d c.L hplus hSY hR)
  have hCkernel : (YC d c.L).pCoreIn 2 ≤ Chapter4.sectionCentralizer c.L :=
    ((YC d c.L).pCoreIn_le 2).trans
      ((ComponentIntersection.centralizerResidual_le _ _).trans inf_le_right)
  exact hmap.trans (sup_le ((le_inf hCS hCkernel).trans hkernel)
    ((le_inf inf_le_left hCP).trans hkernel))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions

end
