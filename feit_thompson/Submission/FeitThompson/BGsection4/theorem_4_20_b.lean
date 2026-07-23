module
public import Submission.FeitThompson.BGsection3.Defs

public import Submission.FeitThompson.GeneratorRank
public import Submission.FeitThompson.BGsection4.theorem_4_20_a
/-! # Theorem 4.20(b) from BG Section 4 -/

universe u

section Main

open scoped FixedPoints

public theorem theorem_4_20_b {G : Type*} [Group G] [Finite G]
    (hsolv : IsSolvable G) (hodd : Odd (Nat.card G))
    (hrank : groupRank G ≤ 2 ∨ groupRank (fittingSubgroup G) ≤ 2)
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) (T : Subgroup ↥(S : Subgroup G)) [T.Characteristic]
    (hT : T ≤ derivedSubgroup ↥(S : Subgroup G)) :
    (T.map (S : Subgroup G).subtype).Normal := by
  classical
  let F : Subgroup G := fittingSubgroup G
  let D : Subgroup G := derivedSubgroup G
  let TG : Subgroup G := T.map (S : Subgroup G).subtype
  have hder_nil : Group.IsNilpotent D :=
    theorem_4_20_a (G := G) hsolv hodd hrank
  have hD_le_F : D ≤ F := by
    exact le_sSup ⟨inferInstance, hder_nil⟩
  have hT_p : IsPGroup p T := S.isPGroup'.to_subgroup T
  have hTG_p : IsPGroup p TG := by
    simpa [TG] using IsPGroup.map (p := p) (H := T) hT_p (S : Subgroup G).subtype
  have hcomm_le_der : ⁅(S : Subgroup G), (S : Subgroup G)⁆ ≤ derivedSubgroup G := by
    simpa [derivedSubgroup, derivedSeries_one] using
      (Subgroup.commutator_mono (show (S : Subgroup G) ≤ ⊤ by exact le_top)
        (show (S : Subgroup G) ≤ ⊤ by exact le_top))
  have hTG_le_der : TG ≤ derivedSubgroup G := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hy_comm : ((y : S) : G) ∈ ⁅(S : Subgroup G), (S : Subgroup G)⁆ := by
      have hy' : y ∈ derivedSubgroup ↥(S : Subgroup G) := hT hy
      have hy_map : ((y : S) : G) ∈ (derivedSubgroup ↥(S : Subgroup G)).map (S : Subgroup G).subtype :=
        Subgroup.mem_map_of_mem (S : Subgroup G).subtype hy'
      simpa [derivedSubgroup, derivedSeries_one] using
        (show ((y : S) : G) ∈ ⁅(S : Subgroup G), (S : Subgroup G)⁆ by
          rw [← Subgroup.map_subtype_commutator]
          exact hy_map)
    exact hcomm_le_der hy_comm
  have hTG_le_D : TG ≤ D := hTG_le_der
  have hTG_le_F : TG ≤ F := hTG_le_D.trans hD_le_F
  have hQcomm : IsMulCommutative (G ⧸ F) := by
    exact ⟨(Subgroup.Normal.quotient_commutative_iff_commutator_le (N := F)).2 hD_le_F⟩
  letI : IsMulCommutative (G ⧸ F) := hQcomm
  letI : CommGroup (G ⧸ F) := CommGroup.ofIsMulCommutative
  let q : G →* (G ⧸ F) := QuotientGroup.mk' F
  have hFS_normal : (F ⊔ (S : Subgroup G)).Normal := by
    have hEq : ((S : Subgroup G).map q).comap q = F ⊔ (S : Subgroup G) := by
      calc
        ((S : Subgroup G).map q).comap q = (S : Subgroup G) ⊔ q.ker := by
          simpa using (Subgroup.comap_map_eq (f := q) (H := (S : Subgroup G)))
        _ = (S : Subgroup G) ⊔ F := by rw [QuotientGroup.ker_mk']
        _ = F ⊔ (S : Subgroup G) := by rw [sup_comm]
    rw [← hEq]
    exact (inferInstance : ((S : Subgroup G).map q).Normal).comap q
  have hnormS_FS_top :
      Subgroup.normalizer ((S : Subgroup G) : Set G) ⊔ (F ⊔ (S : Subgroup G)) = ⊤ := by
    letI : (F ⊔ (S : Subgroup G)).Normal := hFS_normal
    simpa using
      (S.normalizer_sup_eq_top' (N := F ⊔ (S : Subgroup G)) (hP := le_sup_right))
  have hnormS_F_top :
      Subgroup.normalizer ((S : Subgroup G) : Set G) ⊔ F = ⊤ := by
    calc
      Subgroup.normalizer ((S : Subgroup G) : Set G) ⊔ F
          = (Subgroup.normalizer ((S : Subgroup G) : Set G) ⊔ F) ⊔ (S : Subgroup G) := by
              symm
              rw [sup_eq_left.mpr]
              exact le_trans (Subgroup.le_normalizer : (S : Subgroup G) ≤ _) le_sup_left
      _ = Subgroup.normalizer ((S : Subgroup G) : Set G) ⊔ (F ⊔ (S : Subgroup G)) := by
            rw [sup_assoc]
      _ = ⊤ := hnormS_FS_top
  have hconj_mem_TG :
      ∀ g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), ∀ y ∈ TG, g * y * g⁻¹ ∈ TG := by
    intro g hg y hy
    rcases Subgroup.mem_map.mp hy with ⟨yS, hyT, rfl⟩
    let gN : Subgroup.normalizer ((S : Subgroup G) : Set G) := ⟨g, hg⟩
    have hfix :
        Subgroup.comap (Subgroup.normalizerMonoidHom (S : Subgroup G) gN).toMonoidHom T = T :=
      (inferInstance : T.Characteristic).fixed (Subgroup.normalizerMonoidHom (S : Subgroup G) gN)
    have hyComap :
        yS ∈ Subgroup.comap (Subgroup.normalizerMonoidHom (S : Subgroup G) gN).toMonoidHom T := by
      rw [hfix]
      exact hyT
    have hyImage : (Subgroup.normalizerMonoidHom (S : Subgroup G) gN) yS ∈ T := hyComap
    have hyMap : (((Subgroup.normalizerMonoidHom (S : Subgroup G) gN) yS : S) : G) ∈ TG := by
      exact Subgroup.mem_map_of_mem (S : Subgroup G).subtype hyImage
    simpa [TG, gN, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe] using hyMap
  have hnormS_le_normTG :
      Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ Subgroup.normalizer (TG : Set G) := by
    refine subgroup_le_normalizer_of_conj_mem TG
      (Subgroup.normalizer ((S : Subgroup G) : Set G)) ?_
    intro g y hy
    exact hconj_mem_TG g g.property y hy
  let TGD : Subgroup D := TG.subgroupOf D
  have hTGD_p : IsPGroup p TGD := by
    let e : TGD ≃* TG := Subgroup.subgroupOfEquivOfLe (H := TG) (K := D) hTG_le_D
    exact hTG_p.of_equiv e.symm
  obtain ⟨P, hTGD_le_P⟩ := IsPGroup.exists_le_sylow hTGD_p
  have hP_normal : (P : Subgroup D).Normal :=
    Group.IsNilpotent.sylow_normal hder_nil p P
  have hP_char : (P : Subgroup D).Characteristic := Sylow.characteristic_of_normal P hP_normal
  let Pmap : Subgroup G := P.map D.subtype
  have hPmap_char : Pmap.Characteristic := by
    letI : D.Characteristic := by infer_instance
    letI : (P : Subgroup D).Characteristic := hP_char
    simpa [Pmap] using characteristic_map_subtype_of_characteristic (G := G) D (P : Subgroup D)
  have hPmap_normal : Pmap.Normal := by
    letI : Pmap.Characteristic := hPmap_char
    infer_instance
  letI : Pmap.Normal := hPmap_normal
  have hPmap_p : IsPGroup p Pmap := by
    simpa [Pmap] using IsPGroup.map (p := p) (H := (P : Subgroup D)) P.isPGroup' D.subtype
  have hTG_le_Pmap : TG ≤ Pmap := by
    calc
      TG = TGD.map D.subtype := (Subgroup.map_subgroupOf_eq_of_le hTG_le_D).symm
      _ ≤ P.map D.subtype := Subgroup.map_mono hTGD_le_P
  have hPmap_le_S : Pmap ≤ (S : Subgroup G) := by
    have hsup_p : IsPGroup p (((S : Subgroup G) ⊔ Pmap : Subgroup G)) := by
      exact IsPGroup.to_sup_of_normal_right (p := p) (H := (S : Subgroup G)) (K := Pmap)
        S.isPGroup' hPmap_p
    have hEq : (((S : Subgroup G) ⊔ Pmap : Subgroup G)) = (S : Subgroup G) := S.3 hsup_p le_sup_left
    exact sup_eq_left.mp hEq
  have hS_le_normTG : (S : Subgroup G) ≤ Subgroup.normalizer (TG : Set G) := by
    exact le_trans Subgroup.le_normalizer hnormS_le_normTG
  have hPmap_le_normTG : Pmap ≤ Subgroup.normalizer (TG : Set G) := hPmap_le_S.trans hS_le_normTG
  have hpCoreG_le_S : pCore p G ≤ (S : Subgroup G) := by
    have hsup_p : IsPGroup p (((S : Subgroup G) ⊔ pCore p G : Subgroup G)) := by
      exact IsPGroup.to_sup_of_normal_right (p := p) (H := (S : Subgroup G)) (K := pCore p G)
        S.isPGroup' (pCore_isPGroup (G := G) (p := p))
    have hEq : (((S : Subgroup G) ⊔ pCore p G : Subgroup G)) = (S : Subgroup G) := S.3 hsup_p le_sup_left
    exact sup_eq_left.mp hEq
  have hpCoreG_le_normTG : pCore p G ≤ Subgroup.normalizer (TG : Set G) := by
    exact hpCoreG_le_S.trans hS_le_normTG
  have hpPrimeCoreG_le_normTG : pPrimeCore p G ≤ Subgroup.normalizer (TG : Set G) := by
    have hcentPmap : pPrimeCore p G ≤ Subgroup.centralizer (Pmap : Set G) :=
      pPrimeCore_le_centralizer_of_normal_pgroup (G := G) (p := p) Pmap hPmap_p
    have hcentTG : pPrimeCore p G ≤ Subgroup.centralizer (TG : Set G) := by
      exact hcentPmap.trans
        (Subgroup.centralizer_le (show (TG : Set G) ⊆ (Pmap : Set G) from hTG_le_Pmap))
    exact hcentTG.trans (centralizer_le_normalizer TG)
  have hF_le_sup :
      F ≤ pCore p G ⊔ pPrimeCore p G := by
    have hnilF : Group.IsNilpotent ↥F := by infer_instance
    have hF_le_iSup :
        F ≤ ⨆ q : (Nat.card G).primeFactors.attach, pCore q.1 G :=
      normal_nilpotent_le_sup_pCore (G := G) (N := F) (hN := inferInstance) hnilF
    refine hF_le_iSup.trans ?_
    refine iSup_le ?_
    intro q
    by_cases hqp : q.1 = p
    · subst hqp
      exact le_sup_left
    · have hqprime : Nat.Prime q.1 := Nat.prime_of_mem_primeFactors q.1.2
      letI : Fact (Nat.Prime q.1) := ⟨hqprime⟩
      obtain ⟨n, hn⟩ := (pCore_isPGroup (G := G) (p := q.1)).exists_card_eq
      have hcop : Nat.Coprime p (Nat.card (pCore q.1 G)) := by
        rw [hn]
        have hpq : p ≠ q.1 := by
          intro hpq'
          exact hqp hpq'.symm
        exact ((Nat.coprime_primes (Fact.out : Nat.Prime p) hqprime).2 hpq).pow_right n
      exact
        (le_sSup (show pCore q.1 G ∈ {K : Subgroup G | K.Normal ∧ Nat.Coprime p (Nat.card K)} from
          ⟨inferInstance, hcop⟩)).trans le_sup_right
  have hF_le_normTG : F ≤ Subgroup.normalizer (TG : Set G) := by
    exact hF_le_sup.trans (sup_le hpCoreG_le_normTG hpPrimeCoreG_le_normTG)
  have hnormTG_top : Subgroup.normalizer (TG : Set G) = ⊤ := by
    apply top_unique
    rw [← hnormS_F_top]
    exact sup_le hnormS_le_normTG hF_le_normTG
  exact Subgroup.normalizer_eq_top_iff.mp hnormTG_top

end Main
