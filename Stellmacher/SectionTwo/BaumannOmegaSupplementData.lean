module
public import Stellmacher.SectionTwo.TwoFourLocalFactor
public import Stellmacher.SectionTwo.NormalSupplementV
public import Stellmacher.CharacteristicTwoNormal
public import Stellmacher.BaumannIntermediate
public import Stellmacher.BaumannMap

/-!
# The Baumann omega module on a normal supplement

Under the local hypotheses used in (2.4), the normal closure L of the
Baumann subgroup B supplements the Sylow subgroup S. The Sylow subgroup PB
of L maps exactly onto B and is its own Baumann subgroup. Its native module
maps onto the ambient normal closure of Ω₁(Z(B)); this module contains the
original module of S, lies in B, and acts nontrivially on the Thompson subgroup
of PB. These facts supply the actual modules Zi in the proof of (6.3).

The proof combines (2.3), the local factor from (2.4), characteristic-two
inheritance to normal subgroups, and normal-supplement closure transport.
If the new module centralized the Thompson subgroup, elementary abelian
centralizer control and the self-Baumann identity would force B to centralize
it, contradicting the original noncentral Thompson action.

Source: Stellmacher, Journal of Algebra 190 (1997), (2.3), (2.4), and the
opening construction in the proof of (6.3), p31.
-/

namespace Stellmacher.SectionTwo
universe u

public theorem baumann_omega_supplement_data
    {G : Type u} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    (hcore : pCore 2 G = (S : Subgroup G) ⊓ Subgroup.centralizer (vSubgroup S : Set G))
    (hnot : ¬ vSubgroup S ≤ Subgroup.centralizer
      (elementaryAbelianMaxJ (S : Subgroup G) : Set G))
    (hunique : IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G)) :
    let B := (S : Subgroup G) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G)
    let L := Subgroup.normalClosure (B : Set G)
    ∃ PB : Sylow 2 L,
      (PB : Subgroup L).map L.subtype = B ∧ Hypotheses L ∧
      L ⊔ (S : Subgroup G) = ⊤ ∧
      Subgroup.normalClosure ((PB : Subgroup L) : Set L) = ⊤ ∧
      (PB : Subgroup L) ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ (PB : Subgroup L)) : Set L) =
        (PB : Subgroup L) ∧
      (vSubgroup PB).map L.subtype = Subgroup.normalClosure (omegaOneCenterAmbient B : Set G) ∧
      vSubgroup S ≤ (vSubgroup PB).map L.subtype ∧
      (vSubgroup PB).map L.subtype ≤ B ∧
      ¬ vSubgroup PB ≤ Subgroup.centralizer
        (elementaryAbelianMaxJ (PB : Subgroup L) : Set L) := by
  classical
  let B := (S : Subgroup G) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G)
  let L := Subgroup.normalClosure (B : Set G)
  have hBS : B ≤ (S : Subgroup G) := inf_le_left
  have hSB : (S : Subgroup G) ≤ Subgroup.normalizer (B : Set G) :=
    (S : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann (S : Subgroup G))
  have hZB : zSubgroup S ≤ B := by
    intro z hz
    obtain ⟨hzS, _, hzcent⟩ := (mem_omegaOneCenterAmbient_iff (S : Subgroup G) z).mp hz
    refine ⟨hzS, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro w hw
    have hwJ := (mem_omegaOneCenterAmbient_iff _ w).mp hw |>.1
    exact hzcent w ((show elementaryAbelianMaxJ (S : Subgroup G) ≤ (S : Subgroup G) from
      sSup_le fun _ hA => hA.1) hwJ)
  obtain ⟨PB, hPB⟩ := lemma_two_three h S hcore B L rfl rfl
  obtain ⟨K, _PK, _hBK, hKL, _hPK, _hA, hgen⟩ :=
    two_four_exists_local_sl2Frattini_factor h S hcore hnot hunique
  change K ≤ L at hKL
  have hLgen : L ⊔ (S : Subgroup G) = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact sup_le_sup_right hKL _
  let _ : L.Normal := Subgroup.normalClosure_normal
  have hBne : B ≠ ⊥ := by
    intro hb
    apply hnot
    have hJB : elementaryAbelianMaxJ (S : Subgroup G) ≤ B := by
      refine le_inf (sSup_le fun _ hA => hA.1) ?_
      intro j hj
      apply Subgroup.mem_centralizer_iff.mpr
      intro z hz
      exact ((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 j hj |>.symm
    have hJbot := le_bot_iff.mp (hJB.trans_eq hb)
    rw [hJbot]
    intro v _hv
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    have hz1 : z = 1 := hz
    simp [hz1]
  have hPBne : (PB : Subgroup L) ≠ ⊥ := by
    intro hbot
    apply hBne
    rw [← hPB, hbot, Subgroup.map_bot]
  have hdvd : 2 ∣ Nat.card PB := PB.isPGroup'.card_eq_or_dvd.resolve_left
    (fun hc => hPBne (Subgroup.card_eq_one.mp hc))
  have hevenL : Even (Nat.card L) := even_iff_two_dvd.mpr
    (hdvd.trans (Subgroup.card_subgroup_dvd_card (PB : Subgroup L)))
  have hsolvL : Group.IsSolvable L := by
    let _ := h.solvable
    infer_instance
  have hsecL : Hypotheses L := ⟨hsolvL, hevenL,
    characteristicTwo_normal_subgroup h.solvable h.centralizer_twoCore_le L⟩
  have hBL : B ≤ L := Subgroup.le_normalClosure
  have hBsub : B.subgroupOf L = (PB : Subgroup L) := by
    rw [← hPB, subgroupOf_map_subtype_eq]
  have hNgen : Subgroup.normalClosure ((PB : Subgroup L) : Set L) = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [← hBsub, ← Subgroup.normalClosure_eq_map_of_normal_supplement
      L (S : Subgroup G) B hLgen hBL hSB,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hBself : B ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ B) : Set G) = B :=
    baumann_eq_of_intermediate (S : Subgroup G) B le_rfl hBS
  have hPBself : (PB : Subgroup L) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (PB : Subgroup L)) : Set L) =
      (PB : Subgroup L) := by
    apply Subgroup.map_injective L.subtype_injective
    rw [baumann_map_injective L.subtype L.subtype_injective, hPB, hBself]
  let A := omegaOneCenterAmbient B
  have hSA : (S : Subgroup G) ≤ Subgroup.normalizer (A : Set G) := by
    intro s hs
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change A.map (MulAut.conj s).toMonoidHom = A
    have hBm : B.map (MulAut.conj s).toMonoidHom = B :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hSB hs)
    rw [show A = omegaOneCenterAmbient B from rfl,
      ← omegaOneCenterAmbient_map_injective _ (MulAut.conj s).injective, hBm]
  have hAL : A ≤ L := (Subgroup.map_subtype_le _).trans hBL
  have hAmap : (zSubgroup PB).map L.subtype = A := by
    change (omegaOneCenterAmbient (PB : Subgroup L)).map L.subtype = A
    rw [← omegaOneCenterAmbient_map_injective L.subtype L.subtype_injective, hPB]
  have hAsub : A.subgroupOf L = zSubgroup PB := by
    rw [← hAmap, subgroupOf_map_subtype_eq]
  have hZeq : (vSubgroup PB).map L.subtype = Subgroup.normalClosure (A : Set G) := by
    rw [Subgroup.normalClosure_eq_map_of_normal_supplement
      L (S : Subgroup G) A hLgen hAL hSA, hAsub]
    rfl
  have hVZ := vSubgroup_le_map_of_normal_supplement L S PB hLgen
    (hPB ▸ hBS) (hPB ▸ hZB) (hPB ▸ hSB)
  have hZB' : (vSubgroup PB).map L.subtype ≤ B := by
    rw [← hPB]
    exact Subgroup.map_mono ((vSubgroup_le_twoCore_and_elementaryAbelian hsecL PB).1.trans
      ((pCore_isPGroup (p := 2) (G := L)).le_sylow_of_normal PB))
  have hnotL : ¬ vSubgroup PB ≤ Subgroup.centralizer
      (elementaryAbelianMaxJ (PB : Subgroup L) : Set L) := by
    intro hcent
    let _ : IsElementaryAbelian 2 (vSubgroup PB) :=
      (vSubgroup_le_twoCore_and_elementaryAbelian hsecL PB).2
    have hZPB : vSubgroup PB ≤ (PB : Subgroup L) :=
      (vSubgroup_le_twoCore_and_elementaryAbelian hsecL PB).1.trans
        ((pCore_isPGroup (p := 2) (G := L)).le_sylow_of_normal PB)
    have hZomega := elementary_centralizer_maxJ_le_omegaCenter
      (PB : Subgroup L) (vSubgroup PB) hZPB hcent
    have hPBC : (PB : Subgroup L) ≤ Subgroup.centralizer (vSubgroup PB : Set L) :=
      ((show (PB : Subgroup L) ≤ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ (PB : Subgroup L)) : Set L) from
          hPBself.symm.le.trans inf_le_right)).trans (Subgroup.centralizer_le hZomega)
    have hBZ : B ≤ Subgroup.centralizer ((vSubgroup PB).map L.subtype : Set G) := by
      rw [← hPB]
      rintro _ ⟨b, hb, rfl⟩
      apply Subgroup.mem_centralizer_iff.mpr
      rintro _ ⟨z, hz, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hPBC hb) z hz)
    have hJB : elementaryAbelianMaxJ (S : Subgroup G) ≤ B := by
      refine le_inf (sSup_le fun _ hA => hA.1) ?_
      intro j hj
      apply Subgroup.mem_centralizer_iff.mpr
      intro z hz
      exact ((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 j hj |>.symm
    exact hnot (hVZ.trans ((Subgroup.le_centralizer_iff.mp hBZ).trans
      (Subgroup.centralizer_le hJB)))
  exact ⟨PB, hPB, hsecL, hLgen, hNgen, hPBself, hZeq, hVZ, hZB', hnotL⟩

end Stellmacher.SectionTwo
