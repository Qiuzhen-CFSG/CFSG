module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.TerminalOvercomponent.RankLower
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.TerminalOvercomponent.TorusSource.Oriented
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.BlockRecovery.Original
public import CFSG.Quasithin.Chapter10.SourceA5MovedNormalizer.Completion
/-!
# The original oriented natural-block pair is impossible

The original block commutes with its prescribed conjugate, so its moved layer
has the crossed action required by the proved moved-normalizer theorem. That
normalizer lies in M. An escaping block consequently has a different layer.
The shared Sylow then makes the terminal component's two-core disjoint from
the original block, and the rank lower bound applies to its literal quotient.

The final consumer retains the original orientation record, constructs the
full Sylow of the actual opposite-Borel normalizer, and contradicts the
already proved cubic rank upper bound. No overcomponent model or rank premise
is added. Source: Aschbacher--Smith 10.2.3(4), p.747, using the independent
moved-normalizer argument of 10.2.6, pp.748--749.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterB ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem source_original_block_layer_normalizer_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hb : IsBlock (L.subgroupOf (localJoin T L))) :
    normalizer ((blockU L).map L.subtype : Set G) ≤ D.maximalLocal := by
  have he := source_original_blockU_eq_full_moved D hb
  have hUL : ⁅D.fullModule,L⁆ ≤ L := he ▸ map_subtype_le _
  have hJL : L.map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
    le_centralizer_iff.mp (source_original_block_commutes_prescribed_conjugate D hb ht htn)
  rw [he]
  exact source_a5_moved_normalizer_le D e ht htn ((map_mono hUL).trans hJL)

theorem source_original_escaping_block_layers_ne
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (K : Subgroup G) (hout : ¬ K ≤ D.maximalLocal) :
    (blockU L).map L.subtype ≠ (blockU K).map K.subtype := by
  intro he
  apply hout
  have hn : K ≤ normalizer ((blockU K).map K.subtype : Set G) :=
    K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  rw [←he] at hn
  exact hn.trans (source_original_block_layer_normalizer_le D e ht htn hb)

theorem source_original_escaping_pair_component_three_rank
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (N K C R : Subgroup G) (hsq : IsSQTK KnownSimple.IsKnownSimple N)
    (hN : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) N)
    (hC : C ∈ Chapter1.cComponentsIn N) (hLC : L < C) (hKC : K ≤ C)
    (hL : IsL2EvenBlock L 2) (hK : IsShort K)
    (hcL : pCore 2 L = blockU L) (hcK : pCore 2 K = blockU K)
    (hzL : center L = ⊥) (hzK : center K = ⊥)
    (hRL : Chapter1.IsSylowIn 2 R L) (hRK : Chapter1.IsSylowIn 2 R K)
    (hout : ¬ K ≤ D.maximalLocal) : 2 ≤ primeRank 3 C := by
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hN hC.1 hC.2.subnormal
  have hSe : (S : Subgroup C) = ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [hS,subgroupOf_map_subtype]
  have hlocal : L.subgroupOf C ∈ localCComponents S := by
    rw [hSe]
    exact SourceEmbeddings.local_restrict
      (localCComponents_antitone inf_le_left D.maximal.1.1) hLC.le
  have htop : (⊤ : Subgroup C).IsCComponent := by
    simpa only [subgroupOf_self] using hC.2.subgroupOf_of_le le_rfl hC.1
  have hsqC : IsSQTK KnownSimple.IsKnownSimple C := ⟨
    hsq.stronglyQuasithin.of_injective (inclusion hC.1) (inclusion_injective hC.1),
    hsq.isKGroup.of_injective (inclusion hC.1) (inclusion_injective hC.1)⟩
  exact source_natural_pair_component_three_rank L K C R htop hsqC hLC hKC S hlocal
    hL hK hcL hcK hzL hzK hRL hRK
    (source_original_escaping_block_layers_ne D e ht htn hb K hout)

/-- The actual oriented pair contradicts the terminal component's cubic-rank bound. -/
theorem SourceOriginalOrientedTorus.false
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
    {hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)}
    {t : G} {ht : t ∈ (T : Subgroup G)} {htn : t ∉ normalizer (L : Set G)}
    {K C P : Subgroup G} {s : G}
    (O : SourceOriginalOrientedTorus D e hn ht htn K C P s)
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)=⊥)
    (hL : IsL2EvenBlock L 2) (hcoreL : pCore 2 L=blockU L)
    (hSO : baumann (T : Subgroup G) ≤ localOrbit T L)
    (hS : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (localOrbit T L ⊔ baumann (T : Subgroup G)))
    (hSL : baumann (T : Subgroup G) ≤ normalizer (L : Set G)) : False := by
  let K' := K.map (MulAut.conj s).toMonoidHom
  let C' := C.map (MulAut.conj s).toMonoidHom
  let P' := P.map (MulAut.conj s).toMonoidHom
  let hCR : C' ≤ localOrbit T L := O.borel.trans ((map_subtype_le _).trans inf_le_left)
  let q := (originalA5ProductProjection D e hn ht htn).comp (inclusion hCR)
  let D₂ := ((MonoidHom.fst _ _).comp q).ker.map C'.subtype
  let B := baumann (T : Subgroup G)
  let A := ⁅B,D₂⁆ ⊔ D₂
  let N := normalizer (A : Set G)
  obtain ⟨I,⟨hI,hLI,hKI,_,hr⟩,_⟩ := O.terminal_component hb hz hL hcoreL hSO hS hSL
  have hI' : I ∈ Chapter1.cComponentsIn N := hI
  have hKI' : K' ≤ I := hKI
  obtain ⟨_,_,hRL,hRK,_⟩ := O.common_sylow_borel hL hcoreL hSO hS hSL
  obtain ⟨_,hD₂J,_,hD₂,_,_⟩ :=
    source_original_borel_torus_axes D e hn ht htn hb hz C' O.borel O.torus_card
  have hD₂S : D₂ ≤ normalizer (B : Set G) :=
    (map_subtype_le _).trans (O.borel.trans (source_original_borel_normalizes_baumann hSO hS))
  have hP₂ := (source_original_conjugate_commutator_sylow D hL hcoreL hS hSL ht
    D₂ hD₂J hD₂ hD₂S).2
  have hR := source_original_opposite_borel_normalized D e hn hL hcoreL hS hSL ht
    D₂ hD₂J hD₂ hD₂S
  let a := (MulAut.conj t).subgroupMap L
  have hJ : IsShort (L.map (MulAut.conj t).toMonoidHom) :=
    RankOne.Solvable.isShort_of_equiv a hL.2.1
  have hA : pCore 2 A ≠ ⊥ := IsShort.borel_core_ne_bot _ ⁅B,D₂⁆ D₂ hJ hP₂
    (normalizer_commutator_ge_right B D₂)
  obtain ⟨hN,hsq⟩ := source_natural_borel_normalizer_sylow D e hn A K' hA
    (hLI.le.trans hI'.1) hR (hKI'.trans hI'.1) O.escapes
  have hlower := source_original_escaping_pair_component_three_rank D e ht htn hb
    N K' I ⁅B,P'⁆ hsq hN hI' hLI hKI' hL O.natural.2.1 hcoreL O.core
    (source_original_block_center_eq_bot D hn hb hz) O.center hRL hRK O.escapes
  omega

end CFSG.Quasithin.Chapter10
