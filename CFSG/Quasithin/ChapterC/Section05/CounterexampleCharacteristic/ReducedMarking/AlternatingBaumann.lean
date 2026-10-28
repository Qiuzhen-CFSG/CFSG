module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.AlternatingCoordinates
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.Saturation
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd.Sylow
/-!
# The genuine reduced alternating Baumann image and core

Apply the checked S₅ Baumann argument to the literal original module and
restricted normalizer action. Centralizer saturation puts O₂(K Baum(T))
inside Baum(T). Its image is a transposition four-group. The original marked
D₅ already lies in the same two-group image of T, so odd-degree Sylow
geometry identifies the new image with that very D₅. No change of module
coordinates or extra action hypothesis is needed.

Source: Aschbacher–Smith C.5.4 and C.5.9, printed pp.155 and161.
-/
public section
open Subgroup Stellmacher BinaryPermutation Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
open ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

theorem alternating_reduced_baumann (h : AlternatingPairSetup R K L)
    (T : Subgroup G) (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G))
    (hST : ChapterB.baumann R ≤ T)
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hmin : ChapterB.IsMinimalParabolicOver P ⊤)
    (hno : ∀ N : Subgroup G, N ≤ T → normalizer (T : Set G) ≤ normalizer (N : Set G) →
      K ⊔ T ≤ normalizer (N : Set G) → N = ⊥) :
    letI : ((sourceModule K).subgroupOf (K ⊔ T)).Normal := reduced_module_normal K T hn
    letI : IsElementaryAbelian 2 ((sourceModule K).subgroupOf (K ⊔ T)) := reduced_module_elementary K T h.block.2.1
    ∃ (q : (K ⊔ T : Subgroup G) →* FivePerm) (hq : Function.Surjective q)
      (hker : q.ker = centralizer ((sourceModule K).subgroupOf (K ⊔ T) : Set (K ⊔ T : Subgroup G))),
      let p := (alternatingNativeCoordinates h T).toMonoidHom.toAdditiveLeft.toZModLinearMap 2
      (∀ g v, p (NormalElementaryQuotient.representation _ q hq hker g v) =
        coreRepresentation (Fin 5) g (p v)) ∧
      (∀ s : (K ⊔ ChapterB.baumann R : Subgroup G),
        q (inclusion (sup_le_sup_left hST K) s) = h.action s) ∧
      (K ⊔ ChapterB.baumann T).pCoreIn 2 ≤ ChapterB.baumann T ∧
      ((ChapterB.baumann T).subgroupOf (K ⊔ T)).map q = ChapterB.Offenders.D 5 := by
  let : ((sourceModule K).subgroupOf (K ⊔ T)).Normal := reduced_module_normal K T hn
  let : IsElementaryAbelian 2 ((sourceModule K).subgroupOf (K ⊔ T)) := reduced_module_elementary K T h.block.2.1
  obtain ⟨q,hq,hker,hp,he,hcompat⟩ := alternating_native_marking h T hn hST
  let p := (alternatingNativeCoordinates h T).toMonoidHom.toAdditiveLeft.toZModLinearMap 2
  have hk : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation _ q hq hker g v = v := by
    intro v hv g hg
    have hz : v = 0 := hp.1 (hv.trans (map_zero p).symm)
    rw [hz,map_zero]
  have hJ := native_thompson_moves K T h.block.2.1 hT hn P hP hno
  have hred := reduced_module_reduced K T h.block.2.1 hT hn
  have hsat := (SymmetricFive.source_alpha_and_saturation P hmin
    ((sourceModule K).subgroupOf (K ⊔ T)) hred q hq hker p hp.2 he hk hJ).2.2
  have hres := normal_extension_residual K T h.block.2.1.twoPerfect hT hn
  have hc := core_le_baumann_of_native_saturation K T h.block.2.1 hT hn P hP hres hsat
  have hUT : (sourceModule K).subgroupOf (K ⊔ T) ≤ (P : Subgroup (K ⊔ T : Subgroup G)) :=
    hred.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal P)
  obtain ⟨_,hcard,a,ha⟩ := SymmetricFive.source_thompson_baumann
    ((sourceModule K).subgroupOf (K ⊔ T)) P hUT q hq hker p hp.2 he hk hJ
  have hB : ChapterB.baumann (P : Subgroup (K ⊔ T : Subgroup G)) =
      (ChapterB.baumann T).subgroupOf (K ⊔ T) := by
    apply map_injective (K ⊔ T).subtype_injective
    rw [map_subgroupOf_eq_of_le (show ChapterB.baumann T ≤ K ⊔ T from inf_le_left.trans le_sup_right)]
    simpa only [ChapterB.baumann,ChapterB.thompsonAlpha,hP] using
      baumann_map_injective (K ⊔ T).subtype (K ⊔ T).subtype_injective (P : Subgroup (K ⊔ T : Subgroup G))
  rw [hB] at ha hcard
  have hD : ChapterB.Offenders.D 5 ≤ (T.subgroupOf (K ⊔ T)).map q := by
    intro d hd
    obtain ⟨s,hs,hsd⟩ := (h.baumann_image.symm ▸ hd :
      d ∈ ((ChapterB.baumann R).subgroupOf (K ⊔ ChapterB.baumann R)).map h.action)
    exact ⟨inclusion (sup_le_sup_left hST K) s,hST hs,(hcompat s).trans hsd⟩
  have hcase : ChapterB.Offenders.CaseAFamily 5
      (((ChapterB.baumann T).subgroupOf (K ⊔ T)).map q) := ⟨2,by decide,by decide,a,ha⟩
  have hle := ChapterB.Offenders.Odd.caseAFamily_le_D_of_isPGroup (Or.inl rfl)
    (hT.comap_subtype.map q) hD hcase
    (map_mono (subgroupOf_mono (K ⊔ T) (show ChapterB.baumann T ≤ T from inf_le_left)))
  have himage : ((ChapterB.baumann T).subgroupOf (K ⊔ T)).map q = ChapterB.Offenders.D 5 := by
    apply eq_of_le_of_card_ge hle
    rw [hcard]
    exact (ChapterB.Offenders.Odd.card_disjointTranspositions (n := 5) (m := 2)
      (Or.inl rfl) (by decide)).le
  exact ⟨q,hq,hker,he,hcompat,hc,himage⟩
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
