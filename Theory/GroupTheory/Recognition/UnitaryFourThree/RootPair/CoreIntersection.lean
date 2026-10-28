module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.WeakClosure
public import Theory.GroupAction.InvolutionDisplacementCard

/-!
# The actual plane meets the original core in an elementary eight

Every source plane contains E. An original core reflection has square one
on the plane. If the core intersection were just E, its fixed subgroup
would be a proper subgroup of E, of order at most two. Binary rank-nullity
forces at least four fixed points, a contradiction. The noncommutative
left factor excludes an intersection of order sixteen.

Source: Aschbacher, *Sporadic Groups* (1994), 45.3–45.6, pp.243–244.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z:G}
namespace RootPair
variable (P:RootPair z)

theorem E_le_plane (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16) : P.E≤V := by
  obtain ⟨d⟩:=P.exists_planePair h
  rcases (d.exhaustive V).mp hV with rfl | rfl
  · exact d.inf_eq ▸ inf_le_left
  · exact d.inf_eq ▸ inf_le_right

theorem plane_inf_core_eq_left (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16) :
    V⊓core z=V⊓P.leftCore := by
  have hVR : V≤P.R := by let := hV.2.1; exact P.large_elementary_le_R h V hV.1 hV.2.2.ge
  rw [←inf_eq_left.mpr hVR,inf_assoc,P.R_inf_core h]
  rw [inf_eq_left.mpr hVR]

theorem plane_inf_core_card (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16) :
    Nat.card (V⊓core z:Subgroup G)=8 := by
  let := hV.2.1
  have hVR := P.large_elementary_le_R h V hV.1 hV.2.2.ge
  have hEV := P.E_le_plane h V hV
  let D := V⊓P.leftCore
  have hED : P.E≤D := le_inf hEV (P.E_le_leftCore h)
  have hDne : D≠P.leftCore := by
    intro he
    have hAV : P.leftCore≤V := he ▸ (show D≤V from inf_le_left)
    let : IsElementaryAbelian 2 P.leftCore := IsElementaryAbelian.of_injective
      (inclusion hAV) (inclusion_injective hAV)
    exact P.leftCore_not_commutative h inferInstance
  have hDdvd : Nat.card D∣16 := by
    simpa only [P.leftCore_card h] using card_dvd_of_le (show D≤P.leftCore from inf_le_right)
  have hD4 : 4≤Nat.card D := by
    simpa only [P.E_card h] using card_le_of_le hED
  have hD16 : Nat.card D≠16 := by
    intro hc
    exact hDne (eq_of_le_of_card_ge inf_le_right (by rw [hc,P.leftCore_card h]))
  have hDle : Nat.card D≤16 := Nat.le_of_dvd (by decide) hDdvd
  have hDcases : Nat.card D=4 ∨ Nat.card D=8 := by
    interval_cases Nat.card D <;> omega
  have hD8 : Nat.card D=8 := by
    rcases hDcases with hc | hc
    · have hDE : D=P.E := (eq_of_le_of_card_ge hED (by rw [hc,P.E_card h])).symm
      obtain ⟨a,ha,_,_,haz,hau,_,_⟩:=P.exists_center_transpositions h
      have haN := P.core_le_N h ha
      have haV := P.plane_normalized_by_N h V hV haN
      have haR : a∉P.R := by
        intro har
        have hcomm := (P.R_eq_centralizer_E h).le har P.u P.u_mem_E
        have he : P.u=z*P.u := by rw [←hau,←hcomm,mul_inv_cancel_right]
        have hz1 : z=1 := mul_right_cancel (by simpa only [one_mul] using he.symm)
        have hh:=h.involution
        simp [hz1] at hh
      let α := V.normalizerMonoidHom ⟨a,haV⟩
      have ha2 : a^2∈P.E := by
        have hh := h.toCentralizerHypothesis.coreData.square_mem_center (⟨a,ha⟩:core z)
        have hm := mem_map_of_mem (core z).subtype hh
        rw [h.toCentralizerHypothesis.core_center] at hm
        exact (le_sup_left : zpowers z≤P.E) hm
      have hα2 : α^2=1 := by
        have hker : (⟨a,haV⟩:normalizer (V:Set G))^2∈V.normalizerMonoidHom.ker := by
          rw [normalizerMonoidHom_ker]
          exact fun x hx=>(P.centralizer_R_eq_E h).ge ha2 x (hVR hx)
        change V.normalizerMonoidHom ((⟨a,haV⟩:normalizer (V:Set G))^2)=1 at hker
        simpa only [map_pow] using hker
      let F := FixedPoints.subgroup (zpowers α) V
      let F₀ := F.map V.subtype
      have hFE : F₀≤P.E := by
        rintro x ⟨v,hv,rfl⟩
        have hvfix : α v=v := hv ⟨α,mem_zpowers α⟩
        have he : a*(v:G)*a⁻¹=v := congrArg Subtype.val hvfix
        have hvC : (v:G)∈centralizer a := mem_centralizer_singleton_iff.mpr
          ((mul_inv_eq_iff_eq_mul.mp he).symm)
        have hvA := P.centralizer_in_R_le_leftCore h a (mem_sup_right ha) haR ⟨hVR v.property,hvC⟩
        exact hDE ▸ (show (v:G)∈D from ⟨v.property,hvA⟩)
      have hFne : F₀≠P.E := by
        intro he
        have huF : P.u∈F₀ := he ▸ P.u_mem_E
        obtain ⟨v,hv,hvu⟩:=huF
        change (v:G)=P.u at hvu
        have hvfix : α v=v := hv ⟨α,mem_zpowers α⟩
        have heq : a*P.u*a⁻¹=P.u := by
          have he : a*(v:G)*a⁻¹=v := congrArg Subtype.val hvfix
          simpa only [hvu] using he
        rw [hau] at heq
        have hz1 : z=1 := mul_right_cancel (by simpa only [one_mul] using heq)
        have hh:=h.involution
        simp [hz1] at hh
      have hFc : Nat.card F≤2 := by
        have hd : Nat.card F₀∣4 := by simpa only [P.E_card h] using card_dvd_of_le hFE
        have hn : Nat.card F₀≠4 := fun hc=>hFne (eq_of_le_of_card_ge hFE (by rw [hc,P.E_card h]))
        have hl := Nat.le_of_dvd (by decide : 0<4) hd
        have hn3 : Nat.card F₀≠3 := by intro hc; rw [hc] at hd; norm_num at hd
        have hc : Nat.card F₀≤2 := by omega
        simpa only [F₀,card_map_of_injective V.subtype_injective] using hc
      obtain ⟨hcount,hle⟩:=MulAut.involution_fixed_displacement_card_data α hα2
      have hh:=card_le_of_le hle
      change Nat.card V=Nat.card F * _ at hcount
      change _≤Nat.card F at hh
      rw [hV.2.2] at hcount
      nlinarith
    · exact hc
  rw [P.plane_inf_core_eq_left h V hV]
  exact hD8
end RootPair
end Theory.GroupTheory.Recognition.UnitaryFourThree
