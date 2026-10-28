module

public import Stellmacher.SectionTwo.OmegaCentralizerFactor
public import Stellmacher.SectionTwo.ThompsonNormalClosure
public import Theory.GroupTheory.AbelianSupplementIntersection

/-!
# The core bound from opposite Thompson conjugates

In the noncentralizing case of Stellmacher (2.3), let E be the normal
closure of J(S) and Z = Ω₁Z(J(S)). Suppose a conjugate J(S)ˣ, with x in E,
together with J(S) generates E modulo C_E(V), and their fixed subgroups
span V. Then O₂(E) is contained in the Baumann subgroup C_S(Z).

The elementary normal supplement W=ZV has C_W(J(S))=Z. Conjugation and the
fixed-space spanning assumption give Z=(Z∩Zˣ)(Z∩V), using the abelian
supplement-intersection theorem. Put Y=Z∩Zˣ. The core normalizes Z and Zˣ;
J(S) and its conjugate centralize Y. The proved centralizer factorization
therefore makes Y normal in E. Its centralizer in E is normal and contains
J(S), whose internal normal closure is E, so E centralizes Y. The core
already centralizes V and hence centralizes Z, proving the claim.

This is the final core-bound argument of (2.3), Stellmacher, Journal of
Algebra 190 (1997), p. 20. The two-conjugate existence is an explicit input
here and is proved separately from the selected quotient factor modules.
-/

namespace Stellmacher.SectionTwo

private theorem map_fixed_subgroup
    {G : Type*} [Group G] (W J : Subgroup G) (e : G ≃* G) :
    (W ⊓ Subgroup.centralizer (J : Set G)).map e.toMonoidHom =
      W.map e.toMonoidHom ⊓ Subgroup.centralizer (J.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    refine ⟨⟨w, hw.1, rfl⟩, ?_⟩
    change e w ∈ Subgroup.centralizer (J.map e.toMonoidHom : Set G)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨j,hj,rfl⟩
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      congrArg e (Subgroup.mem_centralizer_iff.mp hw.2 j hj)
  · rintro _ ⟨⟨w,hw,rfl⟩,hc⟩
    refine ⟨w,⟨hw,?_⟩,rfl⟩
    change w ∈ Subgroup.centralizer (J : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    apply e.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      Subgroup.mem_centralizer_iff.mp hc (e j) ⟨j,hj,rfl⟩

/-- Opposite Thompson conjugates force the normal-closure core into the Baumann subgroup. -/
public theorem two_three_core_le_baumann_of_opposite
    {G : Type*} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    (hcore : pCore 2 G = (S : Subgroup G) ⊓ Subgroup.centralizer (vSubgroup S : Set G))
    (hnot : ¬ vSubgroup S ≤ Subgroup.centralizer
      (elementaryAbelianMaxJ (S : Subgroup G) : Set G)) :
    let J := elementaryAbelianMaxJ (S : Subgroup G)
    let E := Subgroup.normalClosure (J : Set G)
    let V := vSubgroup S
    let Z := omegaOneCenterAmbient J
    ∀ x ∈ E, E = (J ⊔ J.conjBy x) ⊔ (E ⊓ Subgroup.centralizer (V : Set G)) →
      V ≤ (V ⊓ Subgroup.centralizer (J : Set G)) ⊔
        (V ⊓ Subgroup.centralizer (J.conjBy x : Set G)) →
      twoCoreAmbient E ≤ (S : Subgroup G) ⊓ Subgroup.centralizer (Z : Set G) := by
  let J := elementaryAbelianMaxJ (S : Subgroup G)
  let E := Subgroup.normalClosure (J : Set G)
  let V := vSubgroup S
  let Z := omegaOneCenterAmbient J
  let W := Z ⊔ V
  let Q := twoCoreAmbient E
  change ∀ x ∈ E, E = (J ⊔ J.conjBy x) ⊔ (E ⊓ Subgroup.centralizer (V : Set G)) →
    V ≤ (V ⊓ Subgroup.centralizer (J : Set G)) ⊔
      (V ⊓ Subgroup.centralizer (J.conjBy x : Set G)) →
    Q ≤ (S : Subgroup G) ⊓ Subgroup.centralizer (Z : Set G)
  intro x hx hgen hspan
  let e := MulAut.conj x
  let Zx := Z.map e.toMonoidHom
  let Y := Z ⊓ Zx
  let _ : E.Normal := Subgroup.normalClosure_normal
  let _ : V.Normal := Subgroup.normalClosure_normal
  let _ : Q.Normal := ConjAct.normal_of_characteristic_of_normal
  obtain ⟨hWe,hWE,hNW,_hcomm,hWJ⟩ := two_three_omega_normal_supplement h S hcore hnot
  change W ⊓ Subgroup.centralizer (J : Set G) = Z at hWJ
  let _ : IsElementaryAbelian 2 W := hWe
  have hWmap : W.map e.toMonoidHom = W :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNW hx)
  have hVmap : V.map e.toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (show x ∈ Subgroup.normalizer (V : Set G) by rw [Subgroup.normalizer_eq_top]; trivial)
  have hZxW : Zx ≤ W := hWmap ▸ Subgroup.map_mono (show Z ≤ W from le_sup_left)
  have hWZx : W = Zx ⊔ V := by
    rw [← hWmap, Subgroup.map_sup, hVmap]
  have hWJx : W ⊓ Subgroup.centralizer (J.conjBy x : Set G) = Zx := by
    change W ⊓ Subgroup.centralizer (J.map e.toMonoidHom : Set G) = _
    rw [← hWmap, ← map_fixed_subgroup, hWJ]
  have hVspan : V ≤ (V ⊓ Z) ⊔ (V ⊓ Zx) := by
    apply hspan.trans
    apply sup_le_sup
    · exact le_inf inf_le_left (by
        rw [← hWJ]
        exact inf_le_inf_right _ (show V ≤ W from le_sup_right))
    · exact le_inf inf_le_left (by
        rw [← hWJx]
        exact inf_le_inf_right _ (show V ≤ W from le_sup_right))
  have hZsplit : Z = Y ⊔ (Z ⊓ V) :=
    Subgroup.eq_inf_sup_inf_of_abelian_supplement W Z Zx V le_sup_left hZxW
      le_sup_right (hWZx ▸ (show Z ≤ W from le_sup_left)) hVspan
  have hQcore : Q ≤ pCore 2 G := le_sSup ⟨inferInstance,
    (pCore_isPGroup (p := 2) (G := E)).map E.subtype⟩
  have hQS : Q ≤ (S : Subgroup G) := hQcore.trans (fitting_pCore_le_sylow S)
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) := by
    rw [hcore] at hQcore
    exact hQcore.trans inf_le_right
  have hSNZ : (S : Subgroup G) ≤ Subgroup.normalizer (Z : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change Z.map (MulAut.conj s).toMonoidHom = Z
    rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj s).injective,
      ← elementaryAbelianMaxJ_map_equiv]
    have hSmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((S : Subgroup G).le_normalizer hs)
    change (S : Subgroup G).map (MulAut.conj s).toMonoidHom = (S : Subgroup G) at hSmap
    rw [hSmap]
  have hQNZ : Q ≤ Subgroup.normalizer (Z : Set G) := hQS.trans hSNZ
  have hQNZX : Q ≤ Subgroup.normalizer (Zx : Set G) := by
    have hQmap : Q.map e.toMonoidHom = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (show x ∈ Subgroup.normalizer (Q : Set G) by rw [Subgroup.normalizer_eq_top]; trivial)
    rw [show Zx = Z.map e.toMonoidHom from rfl, ← Subgroup.map_equiv_normalizer_eq]
    exact hQmap ▸ Subgroup.map_mono hQNZ
  have hQNY : Q ≤ Subgroup.normalizer (Y : Set G) :=
    (le_inf hQNZ hQNZX).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hZJ : Z ≤ Subgroup.centralizer (J : Set G) := by
    intro z hz
    exact Subgroup.mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff J z).mp hz).2.2
  have hJY : J ≤ Subgroup.centralizer (Y : Set G) :=
    Subgroup.le_centralizer_iff.mp (inf_le_left.trans hZJ)
  have hJxY : J.conjBy x ≤ Subgroup.centralizer (Y : Set G) := by
    have hz : ⁅Zx, J.conjBy x⁆ = ⊥ := by
      change ⁅Z.map e.toMonoidHom, J.map e.toMonoidHom⁆ = ⊥
      rw [← Subgroup.map_commutator,
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZJ, Subgroup.map_bot]
    exact Subgroup.le_centralizer_iff.mp (inf_le_right.trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hz))
  have hCY : E ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (Y : Set G) := by
    apply (two_three_omega_centralizer_factor h S hcore hnot).trans
    apply sup_le
    · exact (Subgroup.centralizer_le (show Y ≤ W from inf_le_left.trans le_sup_left)).trans
        (Subgroup.centralizer_le_normalizer _)
    · exact hQNY
  have hENY : E ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hgen]
    exact sup_le (sup_le
      (hJY.trans (Subgroup.centralizer_le_normalizer _))
      (hJxY.trans (Subgroup.centralizer_le_normalizer _))) hCY
  have hYE : Y ≤ E := (show Y ≤ W from inf_le_left.trans le_sup_left).trans hWE
  let Ye := Y.subgroupOf E
  let _ : Ye.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYE).mpr hENY
  have hJYe : J.subgroupOf E ≤ Subgroup.centralizer (Ye : Set E) := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hJY hj)) y hy)
  have hEY : (⊤ : Subgroup E) ≤ Subgroup.centralizer (Ye : Set E) := by
    rw [← thompson_normalClosure_generates S]
    exact Subgroup.normalClosure_le_normal hJYe
  have hQY : Q ≤ Subgroup.centralizer (Y : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val
      ((Subgroup.mem_centralizer_iff.mp (hEY (Subgroup.mem_top (⟨q,Subgroup.map_subtype_le _ hq⟩ : E))))
        ⟨y,hYE hy⟩ hy)
  refine le_inf hQS ?_
  apply Subgroup.le_centralizer_iff.mp
  rw [hZsplit]
  exact sup_le (Subgroup.le_centralizer_iff.mp hQY)
    (inf_le_right.trans (Subgroup.le_centralizer_iff.mp hQV))

end Stellmacher.SectionTwo
