module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DeltaTransitiveSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.SylowCentralizerSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CoreCenterSource
public import Theory.GroupTheory.PairFactorSpan
/-!
# Centrality and fusion separation of the distinguished two-coordinate orbit

A nontrivial central Sylow element in Z(R) cannot lie on either Z-axis,
since the Sylows of a nonidentity Z-centralizer have the smaller order
of S. The original Hall torus carries this element through Δ. Uniqueness
of M therefore puts every Δ-centralizer in M and separates Δ from Z
under ambient fusion. Characteristic two places the orbit in Z(O₂(M));
the two-factor generation lemma places all of Z(R) there.

Source: Aschbacher–Smith, 2.4.20(2) and the core-center step of (4), p.535.
All earlier inputs are constructed in the actual source setup.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_distinguished_outside_conjugate_eq
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (x y : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (hyT : y ∈ T) (hyS : y ∉ (d.S : Subgroup d.H).map d.H.subtype) :
    (distinguishedZ d).map (MulAut.conj x⁻¹).toMonoidHom =
      (distinguishedZ d).map (MulAut.conj y⁻¹).toMonoidHom := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let Z := distinguishedZ d
  have ht := d.lemma_2_4_8_1 hG T hST hsingle
    (hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective))
  have hyx : y*x⁻¹ ∈ S :=
    ((S.subgroupOf (T : Subgroup G)).mul_mem_iff_of_index_two ht.1
      (a := ⟨y,hyT⟩) (b := ⟨x⁻¹,T.inv_mem hxT⟩)).mpr
      ⟨fun hy => False.elim (hyS hy),fun hx => False.elim (hxS (by
        change x⁻¹ ∈ S at hx
        simpa only [inv_inv] using S.inv_mem hx))⟩
  have hh : Z.map (MulAut.conj (y*x⁻¹)).toMonoidHom=Z :=
    mem_normalizer_iff_map_conj_eq.mp
      ((source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique).2.2.2 hyx)
  have hm := congrArg (map (MulAut.conj y⁻¹).toMonoidHom) hh
  have he : (Z.map (MulAut.conj (y*x⁻¹)).toMonoidHom).map (MulAut.conj y⁻¹).toMonoidHom =
      Z.map (MulAut.conj x⁻¹).toMonoidHom := by
    have hh' := (conjBy_mul Z y⁻¹ (y*x⁻¹)).symm
    simpa only [Subgroup.conjBy,inv_mul_cancel_left] using hh'
  exact he.symm.trans hm

/-- A central Sylow involution in Z(R) lies off both axes, and its B-orbit
is all of Δ. This is the centrality and ambient-centralizer part of 2.4.20(2). -/
theorem source_distinguished_delta_central
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (u : G) (hu : u ∈ distinguishedDelta d x) :
    (∃ g ∈ M, g*u*g⁻¹ ∈ (T : Subgroup G) ⊓ centralizer (T : Set G)) ∧
      u ∈ twoCore M ⊓ centralizer (twoCore M : Set G) ∧
      centralizer ({u} : Set G) ≤ M ∧
      ∀ z ∈ distinguishedZ d, ¬ IsConj u z := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let A := R ⊓ centralizer (R : Set G)
  let P := twoCore M
  let C := P ⊓ centralizer (P : Set G)
  let Z := distinguishedZ d
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hb := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  have hRT : R ≤ (T : Subgroup G) := (sSup_le fun _ h => h.1).trans hST.le
  have hAT : A ≤ (T : Subgroup G) := inf_le_left.trans hRT
  have hTR := (d.lemma_2_4_8_1 hG T hST hsingle hK).2.2
  have hTA : (T : Subgroup G) ≤ normalizer (A : Set G) :=
    (le_inf hTR (hTR.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hAn : A ≠ ⊥ := by
    intro he
    have hh := eq_bot_iff.mpr (hb.2.2.1.trans he.le)
    have hc := hb.2.1
    rw [hh,card_bot] at hc
    have hp : 1<2^n := Nat.one_lt_pow (by have hn:=hL.1;omega) (by decide)
    omega
  let AT := A.subgroupOf (T : Subgroup G)
  let : AT.Normal := normal_subgroupOf_of_le_normalizer hTA
  have hATn : AT ≠ ⊥ := by
    intro he
    have hm := congrArg (map (T : Subgroup G).subtype) he
    rw [map_subgroupOf_eq_of_le hAT,Subgroup.map_bot] at hm
    exact hAn hm
  obtain ⟨v,hv1⟩ := ne_bot_iff_exists_ne_one.mp (center_inf_ne_bot_of_normal T.isPGroup' AT hATn)
  let z₀ : G := ((v : (T : Subgroup G)) : G)
  have hzA : z₀ ∈ A := v.property.2
  have hzT : z₀ ∈ T := (v : (T : Subgroup G)).property
  have hz1 : z₀ ≠ 1 := fun he => hv1 (Subtype.ext (Subtype.ext he))
  have hzCT : z₀ ∈ centralizer (T : Set G) := by
    intro t ht
    exact congrArg Subtype.val (mem_center_iff.mp v.property.1 (⟨t,ht⟩ : (T : Subgroup G)))
  have hTz : (T : Subgroup G) ≤ centralizer ({z₀} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzCT t ht)
  have hznot (w : G) (hw : w ∈ Z) (hg : IsConj w z₀) : False := by
    have hw1 : w ≠ 1 := fun he => hz1 (isConj_one_right.mp (he ▸ hg))
    obtain ⟨g,hg⟩ := isConj_iff.mp hg
    exact source_distinguished_not_two_central d hG T hST hsingle hL hM hTM hunique hz
      w hw hw1 g (by simpa only [hg] using hTz)
  have hzDelta : z₀ ∈ distinguishedDelta d x := by
    refine ⟨hzA,fun h => hznot z₀ h (IsConj.refl z₀),?_⟩
    rintro ⟨w,hw,he⟩
    exact hznot w hw (isConj_iff.mpr ⟨x⁻¹,he⟩)
  obtain ⟨c⟩ := source_cyclic_torus_setup d hG T hST hsingle hL hM hTM hunique
  obtain ⟨y,hyT,hyS,hyB⟩ := c.outside
  have hd : distinguishedDelta d x = distinguishedDelta d y := by
    unfold distinguishedDelta
    rw [source_distinguished_outside_conjugate_eq d hG T hST hsingle hL hM hTM hunique x y hxT hxS hyT hyS]
  obtain ⟨b,hbB,he⟩ := source_distinguished_delta_transitive d hG T hST hsingle hL hM hTM hunique
    c hz y hyT hyS hyB z₀ (hd ▸ hzDelta) u (hd ▸ hu)
  have hBM : c.hall ≤ M := by
    rw [c.conjugate_pair y hyT hyS hyB]
    exact sup_le (c.torus_le.trans inf_le_left)
      ((map_mono (c.torus_le.trans inf_le_left)).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer (hTM (T.inv_mem hyT)))))
  have hbM : b ∈ M := hBM hbB
  have hPT : P ≤ (T : Subgroup G) := by
    change twoCore M ≤ (T : Subgroup G)
    simpa only [twoCore_eq_pCoreIn,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]
      using pCoreIn_le_sylow M (T.subtype hTM)
  have hzCP : z₀ ∈ centralizer (P : Set G) := centralizer_le hPT hzCT
  have hMe : M ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)
  have hzC : z₀ ∈ C := ⟨hMe ⟨hTM hzT,hzCP⟩,hzCP⟩
  let U := ChapterC.Section05.ConjugateSource.sourceModule (d.block.map d.H.subtype)
  have hAU : A ≤ U := (source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS).ge.trans inf_le_left
  let : IsElementaryAbelian 2 U := by
    let := hK.2.1.elementary
    exact IsElementaryAbelian.map (d.block.map d.H.subtype).subtype
  have hzord : orderOf z₀=2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z₀ (hAU hzA)) hz1
  have hCz : centralizer ({z₀} : Set G) ≤ M := by
    apply centralizer_le_of_M_central_involution T hTM hunique hzord (T.subtype hTM)
    intro t ht
    have htT : t ∈ (T : Subgroup G) := by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM] using ht
    exact mem_centralizer_iff.mp hzCT t htT
  have hMC : M ≤ normalizer (C : Set G) :=
    (le_inf (le_normalizer_twoCore M)
      ((le_normalizer_twoCore M).trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hcentral : b⁻¹*u*(b⁻¹)⁻¹=z₀ := by rw [←he];group
  refine ⟨⟨b⁻¹,M.inv_mem hbM,hcentral ▸ ⟨hzT,hzCT⟩⟩,?_,?_,?_⟩
  · exact he ▸ (mem_normalizer_iff.mp (hMC hbM) z₀).mp hzC
  · have hc : (centralizer ({z₀} : Set G)).map (MulAut.conj b).toMonoidHom = centralizer ({u} : Set G) := by
      rw [Theory.GroupTheory.map_centralizer_equiv,Set.image_singleton]
      exact congrArg (fun v : G => centralizer ({v} : Set G)) he
    rw [←hc]
    exact (map_mono hCz).trans_eq (mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer hbM))
  · intro z hzZ hconj
    have hzu : IsConj z₀ u := isConj_iff.mpr ⟨b,he⟩
    exact hznot z hzZ (hconj.symm.trans hzu.symm)

/-- The full center of R lies in the center of the maximal-local two-core. -/
theorem source_distinguished_center_le_core_center
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    R ⊓ centralizer (R : Set G) ≤ twoCore M ⊓ centralizer (twoCore M : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := distinguishedZ d
  obtain ⟨x,hxT,hxS⟩ := SetLike.exists_of_lt hST
  let W := Z.map (MulAut.conj x⁻¹).toMonoidHom
  have hp := source_distinguished_center_pair d hG T hST hsingle hL hM hTM hunique hz x hxT hxS
  have hb := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  have hq : 2<2^n := by
    have hn := hL.1
    have hh : 2^1<2^n := Nat.pow_lt_pow_right (by decide) (by omega)
    simpa only [pow_one] using hh
  have hZ : 2<Nat.card Z := by rwa [hb.2.1]
  have hW : 2<Nat.card W := by
    dsimp only [W]
    rw [card_map_of_injective (MulAut.conj x⁻¹).injective]
    exact hZ
  have hWZ : W ≤ centralizer (Z : Set G) :=
    ((le_sup_right.trans hp.2.le).trans inf_le_right).trans
      (centralizer_le ((le_sup_left.trans hp.2.le).trans inf_le_left))
  change R ⊓ centralizer (R : Set G) ≤ _
  rw [←hp.2]
  apply sup_le_of_complement_of_axes_le Z W _ hp.1 hWZ hZ hW
  intro u hu huZ huW
  exact (source_distinguished_delta_central d hG T hST hsingle hL hM hTM hunique hz
    x hxT hxS u ⟨hp.2.le hu,huZ,huW⟩).2.1
end CFSG.Quasithin.Chapter2.LinearShadows.Single
