module
public import Theory.GroupTheory.NormalizerSylowCommutator
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DeltaGeometrySource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CyclicSource
public import CFSG.Quasithin.ChapterI.Section06To08.TICommutatorFusion
public import Theory.GroupAction.SubgroupFixedPrimeElement

/-!
# Noncenterless distinguished-class fusion exclusion

The cyclic H/L quotient places the derived subgroup of S in R. Since S
is Sylow in N(Z), conjugacy inside that normalizer forces the derived
subgroup of any two-subgroup fixing a point of a conjugate of Z to
centralize the whole conjugate. The inside fixed-derived alternative
then excludes a distinguished-class involution in S outside R: either a
nonzero fixed part of Z invokes the TI-pair theorem, or a derived element
of the two-coordinate orbit invokes the generated-centralizer theorem.

The local fixed-derived alternative is the preceding model calculation;
its source producer and final discharge belong to the assembly proof.
Source: Aschbacher–Smith, original 2.4.21, printed p.536.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open Theory.GroupTheory ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The original S has its derived subgroup in R, by the cyclic H/L quotient. -/
theorem source_single_sylow_derived_le
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    ⁅S,S⁆≤Stellmacher.elementaryAbelianMaxJ S := by
  intro S
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let : IsCyclic (d.H ⧸ d.block) :=
    source_single_quotient_cyclic d hG T hST hsingle hL hM hTM hunique
  let : CommGroup (d.H ⧸ d.block) := IsCyclic.commGroup
  have hderived : _root_.commutator d.H ≤ d.block := by
    simpa only [QuotientGroup.ker_mk'] using
      Abelianization.commutator_subset_ker (QuotientGroup.mk' d.block)
  rw [(source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).1]
  apply le_inf (le_normalizer_iff_commutator_le_left.mp S.le_normalizer) ?_
  change ⁅(d.S : Subgroup d.H).map d.H.subtype,(d.S : Subgroup d.H).map d.H.subtype⁆≤_
  rw [←map_commutator]
  exact map_mono ((commutator_mono le_top le_top).trans hderived)

/-- In the noncenterless branch, a two-subgroup centralizing a nonidentity
point of a distinguished conjugate has derived subgroup centralizing the
whole distinguished conjugate. -/
theorem source_noncenterless_conjugate_fixed_derived_centralizes
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (I : Subgroup G) (hI : IsPGroup 2 I) (a g : G)
    (ha : a∈(distinguishedZ d).map (MulAut.conj g).toMonoidHom) (ha1 : a≠1)
    (hIc : I≤centralizer ({a} : Set G)) :
    ⁅I,I⁆≤centralizer ((distinguishedZ d).map (MulAut.conj g).toMonoidHom : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let Z := distinguishedZ d
  let N := normalizer (Z : Set G)
  have hTI := source_distinguished_TI_of_center_ne_bot d hG T hST hsingle hL hM hTM hunique hz
  have hMe : M ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)
  have hbase := lemma_2_4_3_1 hG.evenCharacteristic hMe d.mem_gammaEvenZero d.full_pair d.S le_rfl
  obtain ⟨P,hP⟩ : ∃ P : Sylow 2 N, (P : Subgroup N).map N.subtype=S := by
    change ∃ P : Sylow 2 (normalizer (distinguishedZ d : Set G)),
      (P : Subgroup (normalizer (distinguishedZ d : Set G))).map
        (normalizer (distinguishedZ d : Set G)).subtype=S
    rw [hTI.2]
    exact hbase.2.2
  have hSC : ⁅S,S⁆≤centralizer (Z : Set G) := by
    have hd := source_single_sylow_derived_le d hG T hST hsingle hL hM hTM hunique
    have hCS := source_distinguished_sylow_centralizer_eq d hG T hST hsingle hL hM hTM hunique
    exact hd.trans (hCS.symm ▸ inf_le_right)
  let e := MulAut.conj g
  have haZ : e.symm a∈Z := by
    obtain ⟨z,hz,rfl⟩ := ha
    change e.symm (e z)∈Z
    rwa [MulEquiv.symm_apply_apply]
  have haZ1 : e.symm a≠1 := by
    intro he
    exact ha1 (e.injective (by simpa using congrArg e he))
  have hIC : I.map e.symm.toMonoidHom ≤ centralizer ({e.symm a} : Set G) := by
    have hh := (map_mono (f := e.symm.toMonoidHom) hIc).trans
      (map_centralizer_le_centralizer_image ({a} : Set G) e.symm.toMonoidHom)
    simpa only [Set.image_singleton,MulEquiv.coe_toMonoidHom] using hh
  have hd := normalizer_commutator_le_of_sylow_derived Z S P hP hSC
    (I.map e.symm.toMonoidHom) (hI.map e.symm.toMonoidHom)
    (hIC.trans (hTI.1.centralizer_le_normalizer haZ haZ1))
  have hback : (I.map e.symm.toMonoidHom).map e.toMonoidHom=I := by
    rw [map_map]
    have he : e.toMonoidHom.comp e.symm.toMonoidHom=MonoidHom.id G := by ext x; exact e.apply_symm_apply x
    rw [he,map_id]
  have hh := (map_mono (f := e.toMonoidHom) hd).trans
    (map_centralizer_le_centralizer_image (Z : Set G) e.toMonoidHom)
  rwa [map_commutator,hback] at hh

/-- The original noncenterless z-class is excluded by the fixed-derived
alternative from the inside field-involution calculation. -/
theorem source_noncenterless_z_conjugate_exclusion_of_fixed_derived
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (x : G) (hxT : x∈T) (hxS : x∉(d.S : Subgroup d.H).map d.H.subtype)
    (a g : G) (haS : a∈(d.S : Subgroup d.H).map d.H.subtype)
    (haR : a∉Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (ha2 : a^2=1) (ha : a∈(distinguishedZ d).map (MulAut.conj g).toMonoidHom)
    (hcase : let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
      let I := R⊓centralizer ({a} : Set G)
      distinguishedZ d⊓centralizer ({a} : Set G) ≤ ⁅I,I⁆ ∨
      ∃ u : G, u∈distinguishedDelta d x ∧ u∈⁅I,I⁆) : False := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := distinguishedZ d
  let I := R⊓centralizer ({a} : Set G)
  let E := Z.map (MulAut.conj g).toMonoidHom
  have hI : IsPGroup 2 I := (d.S.isPGroup'.map d.H.subtype).to_le
    (inf_le_left.trans (sSup_le fun _ h => h.1))
  have ha1 : a≠1 := fun he => haR (he ▸ R.one_mem)
  have hd : ⁅I,I⁆≤centralizer (E : Set G) :=
    source_noncenterless_conjugate_fixed_derived_centralizes d hG T hST hsingle hL hM hTM hunique
      hz I hI a g ha ha1 inf_le_right
  have hdata := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  let : IsElementaryAbelian 2 Z := hdata.1
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  rcases hcase with hfix | ⟨u,hu,huI⟩
  · have hdiv : 2∣Nat.card Z := by
      rw [hdata.2.1]
      exact dvd_pow_self _ (by have := hL.1; omega)
    obtain ⟨z,hzZ,hz2,hza⟩ := Z.exists_order_prime_in_centralizer_of_normalizes ha2
      (hdata.2.2.2 haS) hdiv
    have hfixed : Z⊓centralizer ({a} : Set G) ≠ ⊥ := by
      intro he
      have hz1 : z=1 := by
        have hm : z∈Z⊓centralizer ({a} : Set G) := ⟨hzZ,hza⟩
        rw [he] at hm
        exact hm
      simp only [hz1,orderOf_one] at hz2
      omega
    have haC := (source_distinguished_TI d hG T hST hsingle hL hM hTM hunique).mem_centralizer_of_derived_fixed
      Z I g a ha hfixed hfix hd
    exact haR ((source_distinguished_sylow_centralizer_eq d hG T hST hsingle hL hM hTM hunique) ▸
      (show a∈S⊓centralizer (Z : Set G) from ⟨haS,haC⟩))
  · have hEC : E≤centralizer ({u} : Set G) := by
      intro e he
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hd huI) e he)
    have hgen : conjugateSubgroupClosure Z E=E := le_antisymm
      (conjugateSubgroupClosure_le_self Z E) (map_conj_le_conjugateSubgroupClosure Z g le_rfl)
    have hER := source_distinguished_delta_generated_le d hG T hST hsingle hL hM hTM hunique
      hz x hxT hxS u hu E (IsElementaryAbelian.isPGroup 2 E) hEC hgen
    exact haR (hER ha)
end CFSG.Quasithin.Chapter2.LinearShadows.Single
