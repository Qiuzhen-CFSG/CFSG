module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Intersection
public import Theory.GroupTheory.TwoFixedLinesIrreducible
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# Local cyclic Sylows force freeness on the two-core

Let `u` be the marked involution outside `O₂(M)` and let `a ∈ C_M(u)`
centralize no distinguished involution. If `C_{O₂(M)}(a)` is nontrivial,
the two-group fixed-point theorem for `⟨u⟩` gives an involution `v` in
that centralizer which also commutes with `u`.

The four-group `⟨u,v⟩` must meet `Z`, since otherwise the local hypothesis
would make its Sylow two-subgroup cyclic. Distinguished elements of `M`
lie in `O₂(M)`, while `u` and `uv` do not, so `v` is distinguished. This
contradicts the choice of `a` and proves its centralizer in the core trivial.

This is a local replacement for the global two-class fusion step in GLS,
Volume 4, Chapter 2, Proposition 17.6. It uses precisely the cyclic-Sylow
conclusion of Corollary 16.6(e), the square degree and the original odd
inverter, with all normality relative to `M`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem core_involution_mem_of_commute_u
    (d : TwoCoreCountingData Z M) (h : IsProductDisconnected Z M)
    (ha : ResidualAction Z M)
    (hlocal : ∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (hu : (d.u : M) ∉ pCore 2 M)
    (v : pCore 2 M) (hv : orderOf v = 2) (hcomm : Commute (d.u : M) (v : M)) :
    ((v : M) : G) ∈ Z := by
  classical
  by_contra hvZ
  obtain ⟨n, hdegree⟩ := d.binary_degree
  have hcore (w : M) (hw : (w : G) ∈ Z) : w ∈ pCore 2 M :=
    distinguished_mem_twoCore_of_binary_degree h ha hdegree hw w.property
  have huG : orderOf ((d.u : M) : G) = 2 := by simpa using d.u_order
  have hvG : orderOf ((v : M) : G) = 2 := by simpa using hv
  have hne : ((d.u : M) : G) ≠ ((v : M) : G) := fun he => hu (Subtype.ext he ▸ v.property)
  have hcG : Commute ((d.u : M) : G) ((v : M) : G) := hcomm.map M.subtype
  let V : Subgroup G := Subgroup.closure ({((d.u : M) : G), ((v : M) : G)} : Set G)
  let : IsKleinFour V := Subgroup.isKleinFour_closure_pair_of_orderOf _ _ huG hvG hne hcG
  have hVM : V ≤ M := by
    apply (Subgroup.closure_le _).mpr
    intro w hw
    rcases hw with rfl | hw
    · exact (d.u : M).property
    · exact (Set.mem_singleton_iff.mp hw) ▸ (v : M).property
  have hbot : Subgroup.closure (V.subtype ⁻¹' Z) = ⊥ := by
    apply le_antisymm ?_ bot_le
    rw [Subgroup.closure_le]
    intro w hw
    exfalso
    have hwQ := hcore ⟨w, hVM w.property⟩ hw
    have hu2 : ((d.u : M) : G) * ((d.u : M) : G) = 1 := by
      simpa [pow_two, huG] using pow_orderOf_eq_one ((d.u : M) : G)
    have hv2 : ((v : M) : G) * ((v : M) : G) = 1 := by
      simpa [pow_two, hvG] using pow_orderOf_eq_one ((v : M) : G)
    rcases (Subgroup.mem_closure_pair_iff _ _ hu2 hv2 hcG (w : G)).mp w.property with
      hw1 | hwu | hwv | hwuv
    · exact (h.involutions w hw).ne_one hw1
    · have he : (⟨(w : G), hVM w.property⟩ : M) = (d.u : M) := Subtype.ext hwu
      exact hu (he ▸ hwQ)
    · exact hvZ (hwv ▸ hw)
    · have he : (⟨(w : G), hVM w.property⟩ : M) = (d.u : M) * (v : M) := Subtype.ext hwuv
      exact hu ((Subgroup.mul_mem_cancel_right (pCore 2 M) v.property).mp (he ▸ hwQ))
  have hV : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by simp)
  obtain ⟨S, hS⟩ := (hV.to_subgroup (⊤ : Subgroup V)).exists_le_sylow
  let : IsCyclic S := (hlocal V hbot).2 S
  exact IsKleinFour.not_isCyclic (G := V)
    (isCyclic_of_surjective (S : Subgroup V).subtype (fun w => ⟨⟨w, hS (Subgroup.mem_top w)⟩, rfl⟩))

/-- A centralizer of the original `u` which is free on distinguished
involutions is free on every nonidentity element of the two-core. -/
public theorem TwoCoreCountingData.core_commute_eq_one_of_local_cyclicSylow
    (d : TwoCoreCountingData Z M) (h : IsProductDisconnected Z M)
    (ha : ResidualAction Z M)
    (hlocal : ∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (a : M) (hau : Commute a (d.u : M))
    (hfree : ∀ z : M, (z : G) ∈ Z → ¬ Commute a z)
    (v : pCore 2 M) (hav : Commute a (v : M)) : v = 1 := by
  classical
  by_contra hvne
  have hu : (d.u : M) ∉ pCore 2 M := by
    intro hu
    have he := Subgroup.disjoint_def.mp (d.disjoint_twoCore h hlocal) d.u.property hu
    have he' : d.u = 1 := Subtype.ext he
    have ho := d.u_order
    rw [he', orderOf_one] at ho
    omega
  let N : Subgroup M := pCore 2 M ⊓ Subgroup.centralizer ({a} : Set M)
  have hvN : (v : M) ∈ N := ⟨v.property, Subgroup.mem_centralizer_singleton_iff.mpr hav.symm.eq⟩
  have hNne : N ≠ ⊥ := by
    intro he
    have hv1 : (v : M) = 1 := by simpa [he] using hvN
    exact hvne (Subtype.ext hv1)
  have hN : IsPGroup 2 N := IsPGroup.to_le pCore_isPGroup inf_le_left
  have huNorm : (d.u : M) ∈ Subgroup.normalizer (N : Set M) := by
    apply Subgroup.inf_normalizer_le_normalizer_inf
    refine ⟨?_, (Subgroup.centralizer ({a} : Set M)).le_normalizer ?_⟩
    · change (d.u : M) ∈ Subgroup.normalizer (pCore 2 M : Set M)
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hau.symm.eq
  have hU : IsPGroup 2 (Subgroup.zpowers (d.u : M)) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one, Subgroup.orderOf_coe] using d.u_order)
  let E : Subgroup M := N ⊓ Subgroup.centralizer (Subgroup.zpowers (d.u : M) : Set M)
  have hEne : E ≠ ⊥ := Subgroup.inf_centralizer_ne_bot_of_pGroups _ N hU hN
    (Subgroup.zpowers_le.mpr huNorm) hNne
  let : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).mpr hEne
  have hE : IsPGroup 2 E := hN.to_le inf_le_left
  obtain ⟨k, hk, hcard⟩ := hE.nontrivial_iff_card.mp inferInstance
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := E) 2
    (hcard ▸ dvd_pow_self 2 (by omega))
  let wQ : pCore 2 M := ⟨w, w.property.1.1⟩
  have hwQ : orderOf wQ = 2 := by simpa [wQ] using hw
  have huw : Commute (d.u : M) (w : M) :=
    Subgroup.mem_centralizer_iff.mp w.property.2 _ (Subgroup.mem_zpowers _)
  have hwZ := core_involution_mem_of_commute_u d h ha hlocal hu wQ hwQ huw
  exact hfree w hwZ (Subgroup.mem_centralizer_singleton_iff.mp w.property.1.2).symm

end BenderSuzuki.ZD
