module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.RankTwoBorelLocalSource
public import Theory.SpecificGroups.SymplecticFour.BorelLocalCover
public import Theory.GroupTheory.PCorePreimageCentralizer
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.AvailableCovers
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.BenderSource

/-!
# The original symplectic Borel intersection and parabolic interchange

Characteristic two passes from H∩M to its subnormal component intersection.
The two standard parabolics, their automorphic images and that intersection
are covered by the proved local fixed-space geometry. Source 2.5.1 then
forces an interchange and identifies the intersection as the Borel.

For the original central-quotient model, the actual marked involution is
inner and the proved universal-kernel calculation eliminates the component
center, including q=4. Sylow conjugacy aligns the resulting literal matrix
equivalence. No cover, Borel or diagram-action premise remains.

Source: Aschbacher--Smith 2.5.2(2), printed p.551, using 1.1.5 and 2.5.1.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Chapter1.QuasisimpleInvolutions
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

private theorem component_intersection_characteristicTwo
    (hc : HasCharacteristicTwo (M.subgroupOf H))
    (D : Subgroup H) (hD : IsComponent H D) :
    HasCharacteristicTwo ((M.subgroupOf H).subgroupOf D) := by
  let J := D.subgroupOf (M.subgroupOf H)
  have hJ : J.IsSubnormal := hD.1.comap (M.subgroupOf H).subtype
  have hh := subnormal_core_selfCentralizing hc J hJ
  let eIJ : ((M.subgroupOf H).subgroupOf D) ≃* J := {
    toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
    invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 eIJ).mpr hh

theorem symplectic_aligned_borel_source
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hMc : HasCharacteristicTwo (M.subgroupOf H))
    (S : Sylow 2 H) (hSM : (S : Subgroup H).map H.subtype ≤ M)
    (D : Subgroup H) (hD : IsComponent H D) (hout : ¬ D.map H.subtype ≤ M)
    (F : Type*) [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : D ≃* Sp F)
    (hU : ((S : Subgroup H).subgroupOf D).map e.toMonoidHom = unipotent) :
    ((M.subgroupOf H).subgroupOf D) = borel.comap e.toMonoidHom ∧
      ∃ s : normalizer (D : Set H), (s : H) ∈ S ∧
        (pointParabolic.comap e.toMonoidHom).map (D.normalizerMonoidHom s).toMonoidHom =
          planeParabolic.comap e.toMonoidHom ∧
        (planeParabolic.comap e.toMonoidHom).map (D.normalizerMonoidHom s).toMonoidHom =
          pointParabolic.comap e.toMonoidHom := by
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  let f := e.toMonoidHom
  let : f.range.Normal := by rw [f.range_eq_top_of_surjective e.surjective]; infer_instance
  have hk : IsPGroup 2 f.ker := by rw [show f.ker = ⊥ from f.ker_eq_bot e.injective]; exact IsPGroup.of_bot
  let B := borel.comap f
  let P := pointParabolic.comap f
  let Q := planeParabolic.comap f
  have hpre : unipotent.comap f = (S : Subgroup H).subgroupOf D := by
    rw [← hU, Subgroup.comap_map_eq_self_of_injective e.injective]
  have hB : B = normalizer ((S : Subgroup H).subgroupOf D : Set D) := by
    rw [show B = borel.comap f from rfl, borel_eq_normalizer_unipotent,
      comap_normalizer_eq_of_surjective _ e.surjective, hpre]
  have hBc := f.centralizer_pCore_comap_of_normal_range hk _ (borel_selfCentralizing_core hF (by omega))
  have hPc := f.centralizer_pCore_comap_of_normal_range hk _ (pointParabolic_selfCentralizing_core hF (by omega))
  have hQc := f.centralizer_pCore_comap_of_normal_range hk _ (planeParabolic_selfCentralizing_core hF (by omega))
  have hP : IsCoatom P := isCoatom_comap_of_surjective e.surjective BorelActionGeometry.pointParabolic_isCoatom
  have hQ : IsCoatom Q := isCoatom_comap_of_surjective e.surjective BorelActionGeometry.planeParabolic_isCoatom
  have hPQ : P ≠ Q := fun he => pointParabolic_ne_planeParabolic ((comap_injective e.surjective) he)
  have hinf : P ⊓ Q = B := rfl
  have hsup : P ⊔ Q = ⊤ := by
    apply (map_injective (f := f) e.injective)
    rw [Subgroup.map_sup, map_comap_eq_self_of_surjective e.surjective,
      map_comap_eq_self_of_surjective e.surjective, parabolics_sup_eq_top,
      map_top_of_surjective f e.surjective]
  have hcover (J : Subgroup D) (hBJ : B ≤ J)
      (hc : centralizer (pCore 2 J : Set J) ≤ pCore 2 J) (_hne : J ≠ ⊤) : J ≤ P ∨ J ≤ Q := by
    have hBJ' : Theory.SpecificGroups.SymplecticFour.borel ≤ J.map f := by
      have hh := map_mono (f := f) hBJ
      rwa [map_comap_eq_self_of_surjective e.surjective] at hh
    have hc' := (Theory.Quasithin.centralizer_pCore_map_le_iff 2 e J).mpr hc
    exact (borel_overgroup_parabolic_of_characteristicTwo (J.map f) hBJ' hc').imp
      map_le_iff_le_comap.mp map_le_iff_le_comap.mp
  exact rank_two_intersection_eq_borel_of_local_cover hH hempty S hSM D hD hout B P Q
    hB hBc hPc hQc (component_intersection_characteristicTwo hMc D hD)
    hP hQ hPQ hinf hsup hcover

theorem exists_symplectic_borel_source
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hMc : HasCharacteristicTwo (M.subgroupOf H))
    (S : Sylow 2 H) (hSM : (S : Subgroup H).map H.subtype ≤ M)
    (D : Subgroup H) (hD : IsComponent H D) (hout : ¬ D.map H.subtype ≤ M)
    (F : Type*) [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e₀ : D ≃* Sp F) :
    ∃ e : D ≃* Sp F, ((S : Subgroup H).subgroupOf D).map e.toMonoidHom = unipotent ∧
      ((M.subgroupOf H).subgroupOf D) = borel.comap e.toMonoidHom ∧
      ∃ s : normalizer (D : Set H), (s : H) ∈ S ∧
        (pointParabolic.comap e.toMonoidHom).map (D.normalizerMonoidHom s).toMonoidHom =
          planeParabolic.comap e.toMonoidHom ∧
        (planeParabolic.comap e.toMonoidHom).map (D.normalizerMonoidHom s).toMonoidHom =
          pointParabolic.comap e.toMonoidHom := by
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_subnormal D hD.1
  let P := R.mapSurjective (f := e₀.toMonoidHom) e₀.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp F) P (unipotentSylow hF (by omega))
  let e := e₀.trans (MulAut.conj g)
  have hU : ((S : Subgroup H).subgroupOf D).map e.toMonoidHom = unipotent := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((R : Subgroup D).map e₀.toMonoidHom).map (MulAut.conj g).toMonoidHom = unipotent at hh
    rw [map_map,hR] at hh
    exact hh
  obtain ⟨hB,hs⟩ := symplectic_aligned_borel_source hH hempty hMc S hSM D hD hout F hn hF e hU
  exact ⟨e,hU,hB,hs⟩
/-- The original mark discharges the entire symplectic central cover, including
field four, before using the actual matrix Borel. -/
theorem symplectic_equiv_of_source_marking
    {S : Sylow 2 H} {z : G} (h : Chapter1.Lemma115Hypotheses H S M z)
    (D : Subgroup H) (hD : IsComponent H D)
    (F : Type) [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : D ⧸ center D ≃* ClassicalGroup.PSp 2 F) :
    center D = ⊥ ∧ Nonempty (D ≃* Sp F) := by
  let : IsQuasisimple D := hD.2
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  obtain ⟨_hout,α,P,_ha,d,_hc⟩ := h.component_inputs D hD
  have hi := d.symplecticFour_inner hn ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩
  have hpow : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  have hz : center D = ⊥ := d.center_eq_bot_of_odd_universal_kernel hi
    (e.trans EvenProjective.equiv.symm)
    (CentralCovers.TwoPrimary.not_two_dvd_universal_kernel (by omega))
  let j : D ⧸ center D ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  exact ⟨hz,⟨(j.symm.trans e).trans EvenProjective.equiv.symm⟩⟩

/-- Source 2.5.2(2) for every nonbinary symplectic component: the marking
proves centerlessness and characteristic two of the literal intersection. -/
theorem symplectic_borel_of_source_marking
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    {S : Sylow 2 H} {z : G} (h : Chapter1.Lemma115Hypotheses H S M z)
    (D : Subgroup H) (hD : IsComponent H D)
    (F : Type) [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e₀ : D ⧸ center D ≃* ClassicalGroup.PSp 2 F) :
    ∃ e : D ≃* Sp F, ((S : Subgroup H).subgroupOf D).map e.toMonoidHom = unipotent ∧
      ((M.subgroupOf H).subgroupOf D) = borel.comap e.toMonoidHom ∧
      ∃ s : normalizer (D : Set H), (s : H) ∈ S ∧
        (pointParabolic.comap e.toMonoidHom).map (D.normalizerMonoidHom s).toMonoidHom =
          planeParabolic.comap e.toMonoidHom ∧
        (planeParabolic.comap e.toMonoidHom).map (D.normalizerMonoidHom s).toMonoidHom =
          pointParabolic.comap e.toMonoidHom := by
  obtain ⟨_hz,⟨e⟩⟩ := symplectic_equiv_of_source_marking h D hD F hn hF e₀
  obtain ⟨hout,_α,_P,_ha,_d,_hc⟩ := h.component_inputs D hD
  exact exists_symplectic_borel_source hH hempty h.intersection_characteristicTwo S
    h.mem_HeOver.2.2 D hD hout F hn hF e

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
