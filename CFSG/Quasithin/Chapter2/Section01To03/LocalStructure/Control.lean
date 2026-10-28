module

public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.Normalizers
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Blocks

/-!
# Local C(H,S) control and the block-theorem application

Source: Aschbacher–Smith 2.3.8(4), printed pp.523–524, and the paragraph
on generated local overgroups in the proof of 2.3.9(7), printed p.526.
The characteristic-normalizer argument proves the literal intrinsic
C(H,S) containment. The remaining input is the universal Local C(G,T)
theorem C.1.29 for SQTK groups, owned by qt-c-01; it is explicitly quantified
over arbitrary local subgroups and has no Γ or unique-maximal hypothesis.
The application discharges SQTK and C(H,S) control and constructs the block
input consumed by ComponentRefinement. It does not assert C.1.29 itself.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2
open Subgroup
variable {G : Type*} [Group G] [Finite G] {M H U L : Subgroup G}

private theorem characteristic_map_equivalence {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (D : Subgroup A) [D.Characteristic] :
    (D.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  rintro a x ⟨y, hy, rfl⟩
  refine ⟨(MulAut.congr e.symm a) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy, ?_⟩
  exact e.apply_symm_apply _

/-- The containment assertion in 2.3.8(4), using C(H,S) inside H. -/
theorem lemma_2_3_8_4_control (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M) (he : H ∈ Chapter1.He G)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype) :
    (S : Subgroup H).characteristicNormalizerClosure ≤ M.subgroupOf H := by
  apply (characteristicNormalizerClosure_le_iff _ _).mpr
  intro D hD hDne
  let := hD
  let A := (S : Subgroup H).map H.subtype
  let e := (S : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
  let R := D.map e.toMonoidHom
  let : R.Characteristic := characteristic_map_equivalence e D
  have hR : R ≠ ⊥ := fun hr => hDne ((map_eq_bot_iff_of_injective D e.injective).mp hr)
  have hmap : (D.map (S : Subgroup H).subtype).map H.subtype = R.map A.subtype := by
    rw [map_map, map_map]
    rfl
  have hb := gammaZero_relative_normalizer_le T hTM hunique hH he hpair S hUS
    (fun hr => hR ((map_eq_bot_iff_of_injective R A.subtype_injective).mp hr))
    (map_subtype_le R) (normalizer_le_normalizer_characteristic_image A R)
  intro x hx
  apply hb
  refine ⟨x.property, ?_⟩
  rw [← hmap]
  exact (D.map (S : Subgroup H).subtype).le_normalizer_map H.subtype
    (mem_map_of_mem H.subtype hx)

/-- The portion of the universal Local C(G,T) theorem C.1.29 consumed here.
The block predicate includes actual modules and relative subnormality;
the product is an ordered elementwise factorization. The Borel refinement
of C.1.29 is not needed for this application. -/
def LocalC129Input (C : GroupClass) (G : Type*) [Group G] : Prop :=
  ∀ (H M : Subgroup G) (S : Sylow 2 H),
    IsSQTK C H → H ∈ Chapter1.He G →
    (S : Subgroup H).characteristicNormalizerClosure ≤ M.subgroupOf H →
    Nonempty (ComponentRefinement.BlockDecomposition M ((S : Subgroup H).map H.subtype) H)

/-- Lemma 2.3.8(4), conditional only on the earlier universal C.1.29 input. -/
theorem lemma_2_3_8_4_of_localC129 {C : GroupClass} (hG : IsSimpleQTKE C G)
    (source : LocalC129Input C G)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M) (he : H ∈ Chapter1.He G)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype) :
    Nonempty (ComponentRefinement.BlockDecomposition M ((S : Subgroup H).map H.subtype) H) := by
  have hgam : H ∈ gamma (Chapter1.He G) M := hH.elim (fun h => h.1.1) (fun h => h.1)
  have hn : IsTwoLocal (normalizer (twoCore H : Set G)) :=
    ⟨twoCore H, hgam.1, isPGroup_pCoreIn 2 H, rfl⟩
  have hsq := (hG.twoLocal_sqtk hn).subgroup (H.subgroupOf (normalizer (twoCore H : Set G)))
  have hs : IsSQTK C H := (IsSQTK.equiv (subgroupOfEquivOfLe (le_normalizer_twoCore H))).mp hsq
  exact source H M S hs he (lemma_2_3_8_4_control T hTM hunique hH he hpair S hUS)

/-- The actual block-generation input used by the independent 2.3.9(7) owner.
The candidate local group need not contain H or lie in Γ₀ initially. -/
theorem localBlockGeneration_of_localC129 {C : GroupClass} (hG : IsSimpleQTKE C G)
    (source : LocalC129Input C G)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (B : Subgroup G) :
    ComponentRefinement.LocalBlockGeneration B M ((S : Subgroup H).map H.subtype) := by
  intro K _ he hout
  have hp : ((S : Subgroup H).map H.subtype, K) ∈ localPairs (Chapter1.He G) M :=
    ⟨beta_mono hpair.1.1 hUS (S.isPGroup'.map H.subtype), he.1, he.2.1, he.2.2, hout⟩
  have hg := localPair_snd_mem_gamma hp
  obtain ⟨hK, P, hP⟩ := gammaZero_sylow_transport_of_full_base hH S hg ⟨K, hp, le_rfl⟩
  have hd := lemma_2_3_8_4_of_localC129 hG source T hTM hunique hK he.1
    ⟨hp, le_rfl⟩ P hP.ge
  rwa [hP] at hd

end CFSG.Quasithin.Chapter2
