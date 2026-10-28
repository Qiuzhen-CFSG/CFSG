module

public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup.Baumann
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.Saturation

/-!
# C.5.4 on a normalized original block

The equation K=[K,J(T)] forces nontrivial Thompson action on U(K).
The original short-block centralizer theorem identifies the intrinsic
kernel with O₂(KT). The actual action and S₅ Baumann calculation then put
O₂(K Baum(T)) inside Baum(T) and identify its full permutation image.

Source: Aschbacher–Smith C.5.3–4, printed pp.154–155.
-/
public section
open Subgroup Stellmacher BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
open ConjugateSource CounterexampleCharacteristic.ReducedMarking
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem thompson_moves_of_commutator (K T : Subgroup G) (hK : IsShort K)
    (hmove : K = ⁅K,elementaryAbelianMaxJ T⁆) :
    ¬ elementaryAbelianMaxJ T ≤ centralizer (sourceModule K : Set G) := by
  intro hJ
  have hKN : K ≤ normalizer (sourceModule K : Set G) :=
    K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hKC : K ≤ centralizer (sourceModule K : Set G) := by
    conv_lhs => rw [hmove]
    exact (commutator_mono le_rfl hJ).trans
      (le_normalizer_iff_commutator_le_right.mp
        (hKN.trans (normalizer_le_normalizer_centralizer (sourceModule K))))
  have hz : blockU K ≤ center K := by
    intro u hu
    apply mem_center_iff.mpr
    intro k
    exact Subtype.ext (hKC k.property u (mem_map_of_mem K.subtype hu)).symm
  exact (ne_of_lt hK.irreducible.1) (inf_eq_left.mpr hz)

omit [Finite G] in
theorem native_thompson_moves_of_commutator (K T : Subgroup G) (hK : IsShort K)
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hmove : K = ⁅K,elementaryAbelianMaxJ T⁆) :
    ¬ elementaryAbelianMaxJ (P : Subgroup (K ⊔ T : Subgroup G)) ≤
      centralizer ((sourceModule K).subgroupOf (K ⊔ T) : Set (K ⊔ T : Subgroup G)) := by
  intro hh
  rw [native_centralizer (K ⊔ T) (sourceModule K) ((map_subtype_le _).trans le_sup_left)] at hh
  have hm := map_mono (f := (K ⊔ T).subtype) hh
  rw [← elementaryAbelianMaxJ_map_injective (K ⊔ T).subtype
    (K ⊔ T).subtype_injective,hP,subgroupOf_map_subtype] at hm
  exact thompson_moves_of_commutator K T hK hmove (hm.trans inf_le_left)

/-- Every local action premise here is constructed from the original block. -/
theorem normalized_source (K T : Subgroup G) (hK : IsAlternatingBlock K 5)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hmove : K = ⁅K,elementaryAbelianMaxJ T⁆) :
    ∃ (q : (K ⊔ T : Subgroup G) →* FivePerm)
      (e : sourceModule K ≃* Multiplicative (core (Fin 5))),
      q.ker = (centralizer (sourceModule K : Set G)).subgroupOf (K ⊔ T) ∧
      (K.subgroupOf (K ⊔ T)).map q = alternatingGroup (Fin 5) ∧
      (∀ (s : (K ⊔ T : Subgroup G)) (u : sourceModule K),
        (e.symm (Multiplicative.ofAdd
          (coreRepresentation (Fin 5) (q s) (e u).toAdd)) : G) =
            (s : G) * (u : G) * (s : G)⁻¹) ∧
      (K ⊔ ChapterB.baumann T).pCoreIn 2 ≤ ChapterB.baumann T ∧
      ∃ a : FivePerm, ((ChapterB.baumann T).subgroupOf (K ⊔ T)).map q =
        (ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom := by
  let A := K ⊔ T
  let V := (sourceModule K).subgroupOf A
  let : V.Normal := reduced_module_normal K T hn
  let : IsElementaryAbelian 2 V := reduced_module_elementary K T hK.2.1
  obtain ⟨q,e,hker,himage,he⟩ := exists_action hK le_sup_left (sup_le K.le_normalizer hn)
  have hV : sourceModule K ≤ A := (map_subtype_le _).trans le_sup_left
  let e' : V ≃* Multiplicative (core (Fin 5)) := (subgroupOfEquivOfLe hV).trans e
  have hk : q.ker = centralizer (V : Set A) := by
    rw [native_centralizer A (sourceModule K) hV]
    exact hker
  have he' : ∀ (s : A) (u : V),
      (e'.symm (Multiplicative.ofAdd
        (coreRepresentation (Fin 5) (q s) (e' u).toAdd)) : A) = s * (u : A) * s⁻¹ := by
    intro s u
    apply Subtype.ext
    exact he s ⟨(u : A),u.property⟩
  have hJ := native_thompson_moves_of_commutator K T hK.2.1 P hP hmove
  have hA : alternatingGroup (Fin 5) ≤ q.range := himage ▸ map_le_range q _
  have hC := reduced_module_core K T hK.2.1 hT hn
  have hs := source_conclusions V P hC q hk e' he' hJ hA
  have hres := CounterexampleCharacteristic.normal_extension_residual K T hK.2.1.twoPerfect hT hn
  have hc := core_le_baumann_of_native_saturation K T hK.2.1 hT hn P hP hres hs.2.2
  have hVT : V ≤ P := (reduced_module_reduced K T hK.2.1 hT hn).le_pCore.trans
    (pCore_isPGroup.le_sylow_of_normal P)
  obtain ⟨_,a,ha⟩ := thompson_baumann_image V q hk e' he' P hVT hJ hA
  have hB : ChapterB.baumann (P : Subgroup A) = (ChapterB.baumann T).subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [map_subgroupOf_eq_of_le (show ChapterB.baumann T ≤ A from inf_le_left.trans le_sup_right)]
    exact (baumann_map_injective A.subtype A.subtype_injective (P : Subgroup A)).trans
      (congrArg ChapterB.baumann hP)
  rw [hB] at ha
  exact ⟨q,e,hker,himage,he,hc,a,ha⟩

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
