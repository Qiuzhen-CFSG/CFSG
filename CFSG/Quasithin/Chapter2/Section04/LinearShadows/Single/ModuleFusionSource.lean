module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterPairSource
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2ModuleFusion

/-!
# The original single-block involution fusion

Fuse each element of U into the actual center of R using its Sylow in L.
The original elementary pair U,Uˣ covers every involution of R, so the same
holds throughout R. In the nontrivial-center branch the two central factors
then give the distinguished-Z or mixed-center alternative. The centerless
branch also retains literal L-conjugators for the natural module.

Source: Aschbacher–Smith, 2.4.20(3) and the proof of 2.4.21,
printed pp.535–536.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
/-- The original L is transitive on the nonidentity elements of U in the centerless branch. -/
theorem source_centerless_module_transitive
    (d : MinimalBlockSetup M) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hz : center (d.block.map d.H.subtype) = ⊥) :
    let L := d.block.map d.H.subtype
    ∀ u ∈ sourceModule L, u≠1 → ∀ v ∈ sourceModule L, v≠1 →
      ∃ l ∈ L, l*u*l⁻¹=v := by
  let L := d.block.map d.H.subtype
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  change ∀ u ∈ sourceModule L, u≠1 → ∀ v ∈ sourceModule L, v≠1 → ∃ l ∈ L, l*u*l⁻¹=v
  rintro u ⟨a,ha,rfl⟩ hu v ⟨b,hb,rfl⟩ hv
  have ha1 : (⟨a,ha⟩ : ChapterC.blockU L) ≠ 1 :=
    fun he => hu (congrArg (fun z : ChapterC.blockU L => ((z : L) : G)) he)
  have hb1 : (⟨b,hb⟩ : ChapterC.blockU L) ≠ 1 :=
    fun he => hv (congrArg (fun z : ChapterC.blockU L => ((z : L) : G)) he)
  obtain ⟨l,hl⟩ := hK.module_transitive_of_centerless hz ⟨a,ha⟩ ⟨b,hb⟩ ha1 hb1
  exact ⟨l,l.property,congrArg (fun z : ChapterC.blockU L => ((z : L) : G)) hl⟩

theorem source_module_fused_into_sylow_center
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    let L := d.block.map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    ∀ r ∈ sourceModule L, ∃ l ∈ L, l*r*l⁻¹ ∈ R ⊓ centralizer (R : Set G) := by
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  obtain ⟨P,hP⟩ := (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).2.2.1
  change (P : Subgroup L).map L.subtype = R at hP
  have hcore := source_block_core_eq_module d hG T hST hsingle
  have hUP : ChapterC.blockU L ≤ (P : Subgroup L) := by
    rw [←hcore]
    exact (pCore_isPGroup (p := 2) (G := L)).le_sylow_of_normal P
  change ∀ r ∈ sourceModule L, ∃ l ∈ L, l*r*l⁻¹ ∈ R ⊓ centralizer (R : Set G)
  intro r hr
  obtain ⟨a,ha,rfl⟩ := hr
  obtain ⟨l,hl⟩ := hK.module_conjugate_centralizes_sylow P ⟨a,ha⟩
  let w := ChapterC.blockConjugate L l ⟨a,ha⟩
  refine ⟨l,l.property,?_⟩
  change ((w : L) : G) ∈ R ⊓ centralizer (R : Set G)
  refine ⟨?_,mem_centralizer_iff.mpr ?_⟩
  · rw [←hP]
    exact mem_map_of_mem L.subtype (hUP w.property)
  · intro b hb
    rw [←hP] at hb
    obtain ⟨b,hb,rfl⟩ := hb
    exact congrArg Subtype.val ((mem_centralizer_iff.mp hl) b hb)

/-- Every involution of the original R is fused into its actual center. -/
theorem source_involution_fused_into_sylow_center
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    ∀ r ∈ R, r^2=1 → ∃ z ∈ R ⊓ centralizer (R : Set G), IsConj r z := by
  let L := d.block.map d.H.subtype
  let U := sourceModule L
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  have hf (v : G) (hv : v ∈ U) : ∃ z ∈ R ⊓ centralizer (R : Set G), IsConj v z := by
    obtain ⟨l,_,hl⟩ := source_module_fused_into_sylow_center d hG T hST hsingle hL hM hTM hunique v hv
    exact ⟨l*v*l⁻¹,hl,isConj_iff.mpr ⟨l,rfl⟩⟩
  obtain ⟨x,hxT,hxS⟩ := SetLike.exists_of_lt hST
  change ∀ r ∈ R, r^2=1 → ∃ z ∈ R ⊓ centralizer (R : Set G), IsConj r z
  intro r hr hr2
  rcases (source_elementary_subgroup_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS).1
    r hr hr2 with hu | hv
  · exact hf r hu
  · obtain ⟨v,hv,rfl⟩ := hv
    obtain ⟨z,hz,hvz⟩ := hf v hv
    exact ⟨z,hz,(isConj_iff.mpr ⟨x⁻¹,rfl⟩).symm.trans hvz⟩

/-- The centerless branch used in the original 2.4.21 fusion argument. -/
theorem source_involution_fused_into_distinguished_of_centerless
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) = ⊥) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    ∀ r ∈ R, r^2=1 → r≠1 → ∃ z ∈ distinguishedZ d, z≠1 ∧ IsConj r z := by
  dsimp only
  intro r hr hr2 hr1
  obtain ⟨z,hzR,hconj⟩ := source_involution_fused_into_sylow_center d hG T hST hsingle hL hM hTM hunique r hr hr2
  refine ⟨z,?_,?_,hconj⟩
  · rwa [distinguishedZ_of_centerless d hz]
  · intro he
    exact hr1 (isConj_one_left.mp (he ▸ hconj))

/-- Original 2.4.20(3), with the original two central factors and their complement. -/
theorem lemma_2_4_20_3
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := distinguishedZ d
    let Zx := Z.map (MulAut.conj x⁻¹).toMonoidHom
    ∀ r ∈ R, r^2=1 → r≠1 →
      (∃ z ∈ Z, z≠1 ∧ IsConj r z) ∨
      ∃ u ∈ R ⊓ centralizer (R : Set G), u∉Z ∧ u∉Zx ∧ IsConj r u := by
  dsimp only
  intro r hr hr2 hr1
  obtain ⟨z,hzR,hconj⟩ := source_involution_fused_into_sylow_center d hG T hST hsingle hL hM hTM hunique r hr hr2
  have hpair := source_distinguished_center_pair d hG T hST hsingle hL hM hTM hunique hz x hxT hxS
  have hzpair : z ∈ distinguishedZ d ⊔ (distinguishedZ d).map (MulAut.conj x⁻¹).toMonoidHom :=
    hpair.2.symm ▸ hzR
  have hz1 : z≠1 := fun he => hr1 (isConj_one_left.mp (he ▸ hconj))
  by_cases hzZ : z ∈ distinguishedZ d
  · exact Or.inl ⟨z,hzZ,hz1,hconj⟩
  · by_cases hzZx : z ∈ (distinguishedZ d).map (MulAut.conj x⁻¹).toMonoidHom
    · obtain ⟨w,hw,he⟩ := hzZx
      have hwz : IsConj w z := isConj_iff.mpr ⟨x⁻¹,he⟩
      refine Or.inl ⟨w,hw,?_,hconj.trans hwz.symm⟩
      intro hw1
      exact hz1 (isConj_one_right.mp (hw1 ▸ hwz))
    · exact Or.inr ⟨z,hpair.2 ▸ hzpair,hzZ,hzZx,hconj⟩

end CFSG.Quasithin.Chapter2.LinearShadows.Single
