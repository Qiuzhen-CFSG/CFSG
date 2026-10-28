module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.NoncenterlessTorusIntervalSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.IntersectionCoreSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DeltaCentralSource
/-!
# Normality of the original Thompson subgroup in the maximal two-local

If R lies in O₂(M), Thompson heredity makes it characteristic there.
Otherwise the torus interval makes both elementary factors intersect
O₂(M) in Z(R). Weak closure then makes Z(R) normal in M. The TI property
and Δ's fusion exclusion force M to permute the two distinguished central
factors. Their normalizer preserves R=O₂(M∩L), and the outside Sylow
representative preserves R as well. Thus M normalizes R in either case.
All core-center and Δ premises are discharged in the final source wrapper.

Source: Aschbacher–Smith, Lemma 2.4.20(4), printed p.535. The last theorem
also records normality of the whole R in C_G(u) for every u∈Δ.
-/
public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_noncenterless_thompson_normal_of_center_core_and_delta
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)

    (hAP : (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)) ≤ twoCore M)
    (hdelta : ∀ x ∈ T, x ∉ (d.S : Subgroup d.H).map d.H.subtype →
      ∀ u ∈ (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
        centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)),
      u ∉ distinguishedZ d → u ∉ (distinguishedZ d).map (MulAut.conj x⁻¹).toMonoidHom →
      ∀ z ∈ distinguishedZ d, ¬IsConj u z) :
    M ≤ normalizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let A := R ⊓ centralizer (R:Set G)
  let Z := distinguishedZ d
  let P := twoCore M
  let U := sourceModule L
  change M≤normalizer (R:Set G)
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hRT : R≤(T:Subgroup G) := (show R≤S from sSup_le fun _ h=>h.1).trans hST.le
  have hTR := (d.lemma_2_4_8_1 hG T hST hsingle hK).2.2
  have hPT : P≤(T:Subgroup G) := by
    change twoCore M≤(T:Subgroup G)
    simpa only [twoCore_eq_pCoreIn,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]
      using pCoreIn_le_sylow M (T.subtype hTM)
  have hMP : M≤normalizer (P:Set G) := le_normalizer_twoCore M
  by_cases hRP : R≤P
  · have hJT : Stellmacher.elementaryAbelianMaxJ (T:Subgroup G)=R :=
      (d.single_natural_global_source hG T hST hsingle hK).2.1.symm
    have hJP : Stellmacher.elementaryAbelianMaxJ P=R :=
      (Stellmacher.elementaryAbelianMaxJ_eq_of_intermediate (T:Subgroup G) P
        (hJT ▸ hRP) hPT).trans hJT
    exact hJP ▸ (hMP.trans (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ P))
  obtain ⟨x,hxT,hxS⟩ := SetLike.exists_of_lt hST
  let e := MulAut.conj x⁻¹
  let V := U.map e.toMonoidHom
  have hpair := (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).2.2.2 x hxT hxS
  have hPe : P.map e.toMonoidHom=P := mem_normalizer_iff_map_conj_eq.mp
    (hMP (hTM (T.inv_mem hxT)))
  have hAe : A.map e.toMonoidHom=A := mem_normalizer_iff_map_conj_eq.mp
    (inf_normalizer_le_normalizer_inf ⟨hTR (T.inv_mem hxT),
      normalizer_le_normalizer_centralizer R (hTR (T.inv_mem hxT))⟩)
  have hUP : ¬U≤P := by
    intro hUP
    apply hRP
    have hgen : R=U⊔V := hpair.1
    rw [hgen]
    exact sup_le hUP ((map_mono hUP).trans_eq hPe)
  have hAU : A≤U :=
    (source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS).ge.trans inf_le_left
  obtain ⟨D,B,hDM,hDB,_,hcard,_,hodd,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩ :=
    source_fixed_free_torus d hG T hST hsingle hL hM hTM hunique
  have hDU : D≤normalizer (U:Set G) := (hDM.trans inf_le_right).trans
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L)))
  have hDN : D≤normalizer (U⊓P:Set G) :=
    (le_inf hDU ((hDM.trans inf_le_left).trans hMP)).trans inf_normalizer_le_normalizer_inf
  have hUPeq : U⊓P=A := by
    rcases source_noncenterless_torus_invariant_interval d hG T hST hsingle hL hM hTM hunique hz
      D (U⊓P) (hDM.trans inf_le_right) (hodd.of_dvd_nat (card_dvd_of_le hDB)) hcard
      hDN (le_inf hAU hAP) inf_le_left with he | he
    · exact he
    · exact False.elim (hUP (he.symm.le.trans inf_le_right))
  have hVPeq : V⊓P=A := by
    have hh := congrArg (map e.toMonoidHom) hUPeq
    rwa [map_inf _ _ _ e.injective,hPe,hAe] at hh
  have hb := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  let _ : IsElementaryAbelian 2 Z := hb.1
  let W := conjugateSubgroupClosure Z P
  have hWA : W≤A := by
    apply conjugateSubgroupClosure_le
    intro g hg
    have hgR := source_distinguished_conjugate_le d hG T hST hsingle hL hM hTM hunique g (hg.trans hPT)
    let E := Z.map (MulAut.conj g).toMonoidHom
    let _ : IsElementaryAbelian 2 E := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
    rcases (source_elementary_subgroup_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS).2
      E hgR inferInstance with hu | hv
    · exact (le_inf hu hg).trans_eq hUPeq
    · exact (le_inf hv hg).trans_eq hVPeq
  have hAW : A≤W := by
    have hp := (source_distinguished_center_pair d hG T hST hsingle hL hM hTM hunique hz x hxT hxS).2
    have hZA : Z≤A := hb.2.2.1
    have hZXA : Z.map e.toMonoidHom≤A := (map_mono hZA).trans_eq hAe
    have hZW : Z≤W := by
      have hOne : Z.map (MulAut.conj 1).toMonoidHom=Z := conjBy_one Z
      have hh := map_conj_le_conjugateSubgroupClosure Z 1 (P:=P) (hOne.le.trans (hZA.trans hAP))
      rwa [hOne] at hh
    have hZXW : Z.map e.toMonoidHom≤W := map_conj_le_conjugateSubgroupClosure Z x⁻¹ (hZXA.trans hAP)
    have hp' : Z⊔Z.map e.toMonoidHom=A := hp
    rw [←hp']
    exact sup_le hZW hZXW
  have hMA : M≤normalizer (A:Set G) := by
    have hW : W=A := le_antisymm hWA hAW
    rw [←hW]
    exact hMP.trans (normalizer_le_normalizer_conjugateSubgroupClosure Z P)
  have hTI := (source_distinguished_TI_of_center_ne_bot d hG T hST hsingle hL hM hTM hunique hz).1
  have hNR := source_distinguished_normalizer_normalizes_thompson d hG T hST hsingle hL hM hTM hunique hz
  have hZn : Z≠⊥ := by
    intro he
    have hc : Nat.card Z=2^n := hb.2.1
    rw [he,card_bot] at hc
    have hn := hL.1
    have hp : 1<2^n := Nat.one_lt_pow (by omega) (by decide)
    omega
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp hZn
  have hz1' : (z:G)≠1 := fun he=>hz1 (Subtype.ext he)
  intro g hg
  have hwA : g*(z:G)*g⁻¹∈A := (mem_normalizer_iff.mp (hMA hg) z).mp (hb.2.2.1 z.property)
  by_cases hwZ : g*(z:G)*g⁻¹∈Z
  · exact hNR ⟨hg,hTI.mem_normalizer_of_conj_mem z.property hz1' hwZ⟩
  have hwZX : g*(z:G)*g⁻¹∈Z.map e.toMonoidHom := by
    by_contra hw
    apply hdelta x hxT hxS _ hwA hwZ hw z z.property
    exact (isConj_iff.mpr ⟨g,rfl⟩).symm
  have hconj : (x*g)*(z:G)*(x*g)⁻¹∈Z := by
    obtain ⟨v,hv,he⟩ := hwZX
    have he' : x⁻¹*v*(x⁻¹)⁻¹=g*(z:G)*g⁻¹ := he
    have hv' : (x*g)*(z:G)*(x*g)⁻¹=v := by
      rw [mul_inv_rev]
      calc (x*g)*(z:G)*(g⁻¹*x⁻¹)=x*(g*(z:G)*g⁻¹)*x⁻¹ := by group
           _=v := by rw [←he'];group
    exact hv'.symm ▸ hv
  have hxg : x*g∈normalizer (R:Set G) := hNR
    ⟨M.mul_mem (hTM hxT) hg,hTI.mem_normalizer_of_conj_mem z.property hz1' hconj⟩
  have hh := (normalizer (R:Set G)).mul_mem ((normalizer (R:Set G)).inv_mem (hTR hxT)) hxg
  simpa only [inv_mul_cancel_left] using hh
/-- Original 2.4.20(4), with the core-center and fusion inputs discharged. -/
theorem source_noncenterless_thompson_normal
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)

 :
    M ≤ normalizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G) := by
  apply source_noncenterless_thompson_normal_of_center_core_and_delta d hG T hST hsingle hL hM hTM hunique hz
  · exact (source_distinguished_center_le_core_center d hG T hST hsingle hL hM hTM hunique hz).trans inf_le_left
  · intro x hxT hxS u hu huZ huZX
    exact (source_distinguished_delta_central d hG T hST hsingle hL hM hTM hunique hz
      x hxT hxS u ⟨hu,huZ,huZX⟩).2.2.2

/-- For u in Δ, the whole R is normal in its ambient centralizer. -/
theorem source_noncenterless_thompson_normal_in_delta_centralizer
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)


    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (u : G) (hu : u ∈ distinguishedDelta d x) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    R ≤ centralizer ({u}:Set G) ∧ (R.subgroupOf (centralizer ({u}:Set G))).Normal := by
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  have hMR := source_noncenterless_thompson_normal d hG T hST hsingle hL hM hTM hunique hz
  have hCM := (source_distinguished_delta_central d hG T hST hsingle hL hM hTM hunique hz
    x hxT hxS u hu).2.2.1
  refine ⟨?_,normal_subgroupOf_of_le_normalizer (hCM.trans hMR)⟩
  intro r hr
  rw [mem_centralizer_singleton_iff]
  exact mem_centralizer_iff.mp hu.1.2 r hr

end CFSG.Quasithin.Chapter2.LinearShadows.Single
