module
public import CFSG.Quasithin.Chapter10.SourceA5NormalizerControl
public import CFSG.Quasithin.Chapter10.SourceNonnormalPairAction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import Theory.GroupTheory.RelativeSylowNormalizer
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The prescribed element-centralizer component in the A5 branch

The maximal local group permutes the original two components. A vector
centralizing L but not their join therefore has its centralizer in M inside
the stabilizer of L. Its prescribed Sylow centralizer is consequently Sylow
in C_M(v); the already proved normalizer bound promotes it to C_G(v).
Original 1.2.4 then embeds L in a unique normal C-component of C_G(v).

This isolates the component step of Aschbacher–Smith 10.2.1, printed p.743.
The noncentralization condition is the source moved-layer geometry; it
cannot be replaced by nontriviality for an arbitrary vector.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

private theorem uniqueness : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- The original Sylow stabilizer is Sylow in the maximal-local stabilizer. -/
theorem source_nonnormal_stabilizer_sylow
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      (D.maximalLocal ⊓ normalizer (L : Set G)) := by
  let M := D.maximalLocal
  let A := L.subgroupOf M
  let N := normalizer (A : Set M)
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  have hlocal : IsSQTK KnownSimple.IsKnownSimple M :=
    D.simpleQTKE.twoLocal_sqtk (uniqueness D).normalizer_maximal.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_,hlocal.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hlocal.stronglyQuasithin p hp ho)
  have hnot : ¬ A.Normal := fun ha =>
    hn (hTM.trans ((normal_subgroupOf_iff_le_normalizer hLM).mp ha))
  obtain ⟨hi,_⟩ := (Chapter1.Section02.proposition_1_2_1_three_index_knownSimple hQ
    D.component_in_maximalLocal).resolve_left hnot
  let : N.Normal := normal_of_index_eq_two hi
  let S := T.subtype hTM
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal N
  have hs : Chapter1.IsSylowIn 2 ((S : Subgroup M) ⊓ N) N := by
    refine ⟨P,?_⟩
    rw [hP,subgroupOf_map_subtype]
  have hh := (Chapter1.IsSylowIn.map_iff M.subtype M.subtype_injective).mpr hs
  have hN : N.map M.subtype = M ⊓ normalizer (L : Set G) := by
    rw [show N = (normalizer (L : Set G)).subgroupOf M from
      (subgroupOf_normalizer_eq hLM).symm,subgroupOf_map_subtype,inf_comm]
  rw [Subgroup.map_inf _ _ _ M.subtype_injective,hN,
    show (S : Subgroup M).map M.subtype = (T : Subgroup G) from
      map_subgroupOf_eq_of_le hTM,←inf_assoc,inf_eq_left.mpr hTM] at hh
  exact hh

/-- A vector distinguishing the two original components has a stabilizing
centralizer inside M. -/
theorem source_nonnormal_element_centralizer_stabilizes
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G)) :
    D.maximalLocal ⊓ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨t,ht,htn,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  intro m hm
  rcases source_nonnormal_maximal_pair D hn ht htn m hm.1 with he | he
  · exact mem_normalizer_iff_map_conj_eq.mpr he
  · exfalso
    apply hv0
    have hCL : L ≤ centralizer ({v} : Set G) :=
      fun x hx => mem_centralizer_singleton_iff.mpr (hvL x hx)
    have hCt : L.map (MulAut.conj t).toMonoidHom ≤ centralizer ({v} : Set G) := by
      rw [←he]
      rintro x ⟨y,hy,rfl⟩
      have hmv : (MulAut.conj m) v = v := by
        change m * v * m⁻¹ = v
        rw [mem_centralizer_singleton_iff.mp hm.2,mul_inv_cancel_right]
      apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg (MulAut.conj m) (hvL y hy)
      simpa only [map_mul,hmv,MulEquiv.coe_toMonoidHom] using hh
    intro x hx
    exact mem_centralizer_singleton_iff.mp ((sup_le hCL hCt) (hpair ▸ hx))

/-- The prescribed source centralizer is Sylow in the full element centralizer. -/
theorem source_a5_element_centralizer_sylow
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hCT : (T : Subgroup G) ⊓ centralizer ({v} : Set G) =
      (T : Subgroup G) ⊓ normalizer (L : Set G)) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      (centralizer ({v} : Set G)) := by
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_normalizer_componentOrbit L T
  have hRC : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤
      centralizer ({v} : Set G) := hCT ▸ inf_le_right
  have hs := (source_nonnormal_stabilizer_sylow D hn).restrict
    (le_inf (inf_le_left.trans hTM) hRC)
    (le_inf inf_le_left (source_nonnormal_element_centralizer_stabilizes D hn hvL hv0))
  exact exists_sylow_eq_of_relative_normalizer_le hs inf_le_right
    (le_inf (inf_le_right.trans (source_a5_sylow_stabilizer_normalizer_le D e hn)) inf_le_left)

omit D [Finite G] in
private theorem element_centralizer_core_ne_bot {v : G}
    (hvT : v ∈ (T : Subgroup G)) (hv1 : v ≠ 1)
    {X : Subgroup G} (hvX : v ∈ X) (hX : X ≤ centralizer ({v} : Set G)) :
    X.pCoreIn 2 ≠ ⊥ := by
  have hp : IsPGroup 2 (zpowers v) := T.isPGroup'.to_le (zpowers_le.mpr hvT)
  have hn : X ≤ normalizer (zpowers v : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [zpowers_eq_closure,centralizer_closure]
    exact hX
  have hle := le_pCoreIn_of_normalizes hp (zpowers_le.mpr hvX) hn
  intro he
  exact hv1 (mem_bot.mp (he ▸ hle (mem_zpowers v)))

/-- Original 1.2.4 supplies the unique containing component, normal in the
actual centralizer, for the prescribed source vector. -/
theorem source_a5_element_containing_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvT : v ∈ (T : Subgroup G)) (hv1 : v ≠ 1)
    (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hCT : (T : Subgroup G) ⊓ centralizer ({v} : Set G) =
      (T : Subgroup G) ⊓ normalizer (L : Set G)) :
    ∃ I : Subgroup G, L ≤ I ∧ I ≤ centralizer ({v} : Set G) ∧
      (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent ∧
      centralizer ({v} : Set G) ≤ normalizer (I : Set G) := by
  let X := centralizer ({v} : Set G)
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hvX : v ∈ X := mem_centralizer_singleton_iff.mpr rfl
  have hLX : L ≤ X := by
    intro l hl
    exact mem_centralizer_singleton_iff.mpr (hvL l hl)
  have hRX : R ≤ X := by rw [show R = (T : Subgroup G) ⊓ X from hCT.symm]; exact inf_le_right
  have hvR : v ∈ R := by rw [show R = (T : Subgroup G) ⊓ X from hCT.symm]; exact ⟨hvT,hvX⟩
  have hcoreX := element_centralizer_core_ne_bot hvT hv1 hvX le_rfl
  have hlocal : L ∈ Chapter1.L G R := by
    refine ⟨D.maximal.1.1.subgroupOf_of_le le_sup_left
      (sup_le le_sup_left (inf_le_left.trans le_sup_right)),?_,?_⟩
    · exact (source_a5_element_centralizer_sylow D e hn hvL hv0 hCT).restrict
        le_sup_right (sup_le hLX hRX)
    · exact element_centralizer_core_ne_bot hvT hv1 (mem_sup_right hvR)
        (sup_le hLX hRX)
  obtain ⟨P,hP⟩ := source_a5_element_centralizer_sylow D e hn hvL hv0 hCT
  have hP' : (P : Subgroup X) = R.subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hRX]
  have hlocalX : L.subgroupOf X ∈ Chapter1.L X (P : Subgroup X) := by
    rw [hP']
    exact (Chapter1.mem_LIn_iff_subgroupOf hRX hLX).mp ⟨hLX,hlocal⟩
  have hPL : (P : Subgroup X) ≤ normalizer (L.subgroupOf X : Set X) := by
    rw [hP',←subgroupOf_normalizer_eq hLX]
    exact fun x hx => hx.2
  obtain ⟨K,⟨hK,hLK,hKn⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (Chapter1.Section02.uniqueness_local_quotient_sqtk D.simpleQTKE hcoreX) P hlocalX hPL
  let I := K.map X.subtype
  have hIX : I ≤ X := map_subtype_le K
  have he : I.subgroupOf X = K := comap_map_eq_self_of_injective X.subtype_injective K
  refine ⟨I,?_,hIX,he.symm ▸ hK,?_⟩
  · rw [←map_subgroupOf_eq_of_le hLX]
    exact map_mono hLK
  · exact (normal_subgroupOf_iff_le_normalizer hIX).mp (he.symm ▸ hKn)

end CFSG.Quasithin.Chapter10
