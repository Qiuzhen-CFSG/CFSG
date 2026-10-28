module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.Borel
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic

/-!
# The linear field restriction for 15.3.40

Conjugating an arbitrary Sylow subgroup into the standard upper root group
transports the actual conjugation action. A subgroup of order four invariant
under its whole Borel is that root group, so the field has order four. The
centralizer calculation with one transvection also proves that the Borel is
of characteristic two; this discharges the model premise of 15.3.33(1) in
the linear case. No field bound or alternating-group identification is assumed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
15.3.40, printed p.1138. The root-invariance calculation reuses
`Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic`.
-/

public section

open Subgroup Matrix.SpecialLinearGroup
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane

/-- Transport the concrete linear Sylow normalizer facts to the component. -/
theorem linear_borel_facts {G : Type*} [Group G] [Finite G]
    {L S : Subgroup G} {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL L 2 (2 ^ n))
    (P : Sylow 2 L) (hP : (P : Subgroup L).map L.subtype = S ⊓ L) :
    RankOneBorelFacts L S := by
  apply rankOneBorelFacts_of_sylow L S P hP
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hm
  apply rankOneSylowFacts_of_equiv P e
  exact rankOneSylowFacts_psl2 F n hn hcard _

private theorem sylow_coordinates {H K : Type*} [Group H] [Group K] [Finite K]
    (e : H ≃* K) (P : Sylow 2 H) (Q : Sylow 2 K) :
    ∃ f : H ≃* K, (P : Subgroup H).map f.toMonoidHom = Q := by
  let : Finite H := Finite.of_equiv K e.toEquiv.symm
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P' Q
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  change (P : Subgroup H).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
  rw [← Subgroup.map_map]
  exact congrArg Sylow.toSubgroup hg

/-- The order of an arbitrary Sylow two-subgroup in the actual linear model. -/
theorem linear_sylow_card {H F : Type*} [Group H]
    [Field F] [Finite F] [CharP F 2]
    (e : H ≃* Matrix.SpecialLinearGroup (Fin 2) F) (P : Sylow 2 H) :
    Nat.card P = Nat.card F := by
  obtain ⟨f, hf⟩ := sylow_coordinates e P (upperUnipotentSylow F 2)
  have hf' : (P : Subgroup H).map f.toMonoidHom = upperUnipotent F := hf
  rw [← Subgroup.card_map_of_injective (K := (P : Subgroup H))
      (f := f.toMonoidHom) f.injective,
    hf', card_upperUnipotent]

open BenderSuzuki.Converse Matrix

private theorem root_centralizer_le {F : Type*} [Field F] [CharP F 2] :
    centralizer (upperUnipotent F : Set (SL2 F)) ≤ upperUnipotent F := by
  intro g hg
  have h1 : uni (1 : F) ∈ upperUnipotent F := by
    rw [← CFSG.Quasithin.ChapterF.Source.Linear.unip_eq_upper]
    exact (mem_Unip_iff _).mpr ⟨1, rfl⟩
  have hh := hg (uni (1 : F)) h1
  have h00 := congrArg (fun A : SL2 F => A.val 0 0) hh
  have h01 := congrArg (fun A : SL2 F => A.val 0 1) hh
  simp [mul_apply, Fin.sum_univ_two] at h00 h01
  have hdiag : g.val 0 0 = g.val 1 1 := by linear_combination -h01
  have hd := g.property
  simp only [det_fin_two, h00, mul_zero, sub_zero] at hd
  have he : g.val 1 1 = 1 := by
    have heq : g.val 1 1 ^ 2 = (1 : F) ^ 2 := by
      simpa only [pow_two, hdiag, mul_one] using hd
    exact frobenius_inj F 2 heq
  rw [← CFSG.Quasithin.ChapterF.Source.Linear.unip_eq_upper]
  apply (mem_Unip_iff _).mpr
  refine ⟨g.val 0 1, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

/-- A nontrivial root subgroup normalized by the whole Borel is the whole root.
The Sylow and Borel may be in arbitrary coordinates in an isomorphic group. -/
theorem linear_sylow_plane_field_card {H F : Type*} [Group H]
    [Field F] [Finite F] [CharP F 2]
    (e : H ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (P : Sylow 2 H) (W : Subgroup H)
    (hWP : W ≤ P) (hW : Nat.card W = 4)
    (hn : normalizer (P : Set H) ≤ normalizer (W : Set H)) :
    Nat.card F = 4 := by
  obtain ⟨f, hf⟩ := sylow_coordinates e P (upperUnipotentSylow F 2)
  have hf' : (P : Subgroup H).map f.toMonoidHom = upperUnipotent F := hf
  let W' := W.map f.toMonoidHom
  have hle : W' ≤ upperUnipotent F := hf' ▸ Subgroup.map_mono hWP
  have hcard : Nat.card W' = 4 := by
    change Nat.card (W.map f.toMonoidHom) = 4
    rw [Subgroup.card_map_of_injective f.injective, hW]
  have hne : W' ≠ ⊥ := by intro h; rw [h] at hcard; simp at hcard
  have hnorm : rankOneBorel F ≤ normalizer (W' : Set _) := by
    have hh := Subgroup.map_mono (f := f.toMonoidHom) hn
    change (normalizer ((P : Subgroup H) : Set H)).map f.toMonoidHom ≤
      (normalizer (W : Set H)).map f.toMonoidHom at hh
    rw [Subgroup.map_equiv_normalizer_eq, Subgroup.map_equiv_normalizer_eq, hf'] at hh
    exact hh
  have he := eq_upperUnipotent_of_normalized W' hle hne hnorm
  rwa [he, card_upperUnipotent] at hcard

/-- The exact field restriction in the linear branch of 15.3.40, before
any identification of the residual actor with A₄. -/
theorem linear_plane_degree_eq_two {G : Type*} [Group G] [Finite G]
    {L S W : Subgroup G} {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL L 2 (2 ^ n))
    (P : Sylow 2 L) (hP : (P : Subgroup L).map L.subtype = S ⊓ L)
    (hWS : W ≤ S) (hWL : W ≤ L) (hW : Nat.card W = 4)
    (hn : borel L S ≤ normalizer (W : Set G)) : n = 2 := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let f := e.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩).symm
  have hPi : (S ⊓ L).subgroupOf L = (P : Subgroup L) := by
    rw [← hP]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hWP : W.subgroupOf L ≤ (P : Subgroup L) := by
    rw [← hPi]
    exact Subgroup.subgroupOf_mono L (le_inf hWS hWL)
  have hWi : Nat.card (W.subgroupOf L) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWL).toEquiv).trans hW
  have hNi : normalizer (P : Set L) ≤ normalizer (W.subgroupOf L : Set L) := by
    change normalizer ((P : Subgroup L) : Set L) ≤ _
    rw [← hPi, ← Subgroup.subgroupOf_normalizer_eq inf_le_right,
      ← Subgroup.subgroupOf_normalizer_eq hWL]
    intro x hx
    exact hn ⟨x.property, hx⟩
  have h4 := linear_sylow_plane_field_card f P (W.subgroupOf L) hWP hWi hNi
  have hp : 2 ^ n = 2 ^ 2 := by omega
  exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ))) hp
/-- The actual Sylow subgroup is self-centralizing in every characteristic-two
PSL₂ model, independently of the chosen Sylow coordinates. -/
theorem linear_sylow_selfCentralizing {H F : Type*} [Group H]
    [Field F] [Finite F] [CharP F 2]
    (e : H ≃* Matrix.SpecialLinearGroup (Fin 2) F) (P : Sylow 2 H) :
    centralizer (P : Set H) ≤ (P : Subgroup H) := by
  obtain ⟨f, hf⟩ := sylow_coordinates e P (upperUnipotentSylow F 2)
  have hf' : (P : Subgroup H).map f.toMonoidHom = upperUnipotent F := hf
  intro x hx
  have hxf : f x ∈ upperUnipotent F := by
    apply root_centralizer_le
    intro y hy
    obtain ⟨z, hz, he⟩ := hf'.symm ▸ hy
    subst y
    exact (map_mul f z x).symm.trans ((congrArg f (hx z hz)).trans (map_mul f x z))
  obtain ⟨y, hy, he⟩ := hf'.symm ▸ hxf
  exact f.injective he ▸ hy

/-- The linear Borel satisfies the characteristic-two hypothesis of 15.3.33(1). -/
theorem linear_borel_characteristic {G : Type*} [Group G] [Finite G]
    {L S : Subgroup G} {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL L 2 (2 ^ n))
    (P : Sylow 2 L) (hP : (P : Subgroup L).map L.subtype = S ⊓ L) :
    Theory.GroupTheory.generalizedFitting (borel L S) = pCore 2 (borel L S) := by
  apply borel_characteristic_of_centralizer (linear_borel_facts hn hm P hP)
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let f := e.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩).symm
  intro x hx
  have hxi : (⟨x, hx.1⟩ : L) ∈ (P : Subgroup L) := by
    apply linear_sylow_selfCentralizing f P
    intro y hy
    apply Subtype.ext
    exact hx.2 y (hP ▸ mem_map_of_mem L.subtype hy)
  exact hP ▸ mem_map_of_mem L.subtype hxi

/-- The linear branch of the source argument: 15.3.33(1) identifies the
intersection, and its actual action on the four-group forces n = 2. -/
theorem linear_restriction_of_source {G : Type*} [Group G] [Finite G]
    {L S M I Yplus W : Subgroup G} {n : ℕ}
    (hn : 0 < n) (hm : ClassicalGroup.IsPSL L 2 (2 ^ n))
    (hLI : L ≤ I) [(L.subgroupOf I).Normal]
    (hSM : S ≤ M) (hYS : Yplus ⊔ S ≤ M ⊓ I) (hLM : ¬ L ≤ M)
    (P : Sylow 2 L) (hP : (P : Subgroup L).map L.subtype = S ⊓ L)
    (h33 : ∀ K : Subgroup G, K ≤ L → Yplus ⊔ S ≤ normalizer (K : Set G) →
      Theory.GroupTheory.generalizedFitting K = pCore 2 K → K ≤ M ⊓ I)
    (hWS : W ≤ S) (hWL : W ≤ L) (hW : Nat.card W = 4)
    (hWN : M ⊓ I ≤ normalizer (W : Set G)) :
    M ⊓ L = borel L S ∧ n = 2 := by
  have hf := linear_borel_facts hn hm P hP
  have hB := intersection_eq_borel hLI hSM hYS hLM P hP hf h33
    (linear_borel_characteristic hn hm P hP)
  refine ⟨hB, linear_plane_degree_eq_two hm P hP hWS hWL hW ?_⟩
  rw [← hB]
  exact (le_inf inf_le_left (inf_le_right.trans hLI)).trans hWN

end CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane
