module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.AlternatingBaumann
/-!
# Constructing the actual reduced alternating-five setup

The reduced Baumann theorem supplies the module containment, exact core and
unchanged marked four-group. The original H¹ calculation supplies the full
module-centralizer product. Normal Sylow restriction constructs the actual
T∩K Sylow subgroup. Restricting the proved KT action and its original module
coordinates then fills every field of the genuine C.5.3–4 setup on Baum(T).

Source: Aschbacher–Smith C.5.4 and C.5.9, printed pp.155 and161.
-/
public section
open Subgroup Stellmacher BinaryPermutation Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
open ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

theorem exists_alternating_reduced_setup (h : AlternatingPairSetup R K L)
    (T : Subgroup G) (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G))
    (hST : ChapterB.baumann R ≤ T)
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hmin : ChapterB.IsMinimalParabolicOver P ⊤)
    (hno : ∀ N : Subgroup G, N ≤ T → normalizer (T : Set G) ≤ normalizer (N : Set G) →
      K ⊔ T ≤ normalizer (N : Set G) → N = ⊥)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    Nonempty (AlternatingPairSetup T K ⊥) := by
  let S := ChapterB.baumann T
  let A := K ⊔ T
  let B := K ⊔ S
  have hSB : S ≤ B := le_sup_right
  have hBA : B ≤ A := sup_le_sup_left (show S ≤ T from inf_le_left) K
  have hUA : sourceModule K ≤ A := (map_subtype_le _).trans le_sup_left
  let : ((sourceModule K).subgroupOf A).Normal := reduced_module_normal K T hn
  let : IsElementaryAbelian 2 ((sourceModule K).subgroupOf A) := reduced_module_elementary K T h.block.2.1
  obtain ⟨q,hq,hker,he,hcompat,hQS,himage⟩ := alternating_reduced_baumann h T hT hn hST P hP hmin hno
  have hc := reduced_baumann_core K T h.block.2.1 hT hn ⟨P,hP⟩
  have hUS : sourceModule K ≤ S := hc.2.1.trans hQS
  have hcore : B.pCoreIn 2 = S ⊓ centralizer (sourceModule K : Set G) := by
    apply le_antisymm (le_inf hQS (hc.2.2.2.2.1.le.trans inf_le_right))
    exact (le_inf (inf_le_left.trans hSB) inf_le_right).trans hc.2.2.2.2.1.ge
  let act := q.comp (inclusion hBA)
  have hmap (V : Subgroup G) (hVB : V ≤ B) :
      (V.subgroupOf B).map act = (V.subgroupOf A).map q := by
    ext y
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact ⟨inclusion hBA v,hv,rfl⟩
    · rintro ⟨v,hv,rfl⟩
      exact ⟨⟨v,hVB hv⟩,hv,rfl⟩
  have hblock : (K.subgroupOf A).map q = alternatingGroup (Fin 5) := by
    ext y
    constructor
    · rintro ⟨k,hk,rfl⟩
      let k₀ : (K ⊔ ChapterB.baumann R : Subgroup G) := ⟨k,(show K ≤ K ⊔ ChapterB.baumann R from le_sup_left) hk⟩
      have hkq : q k = h.action k₀ := hcompat k₀
      rw [hkq]
      exact h.block_image.le (mem_map_of_mem h.action hk)
    · intro hy
      obtain ⟨k,hk,rfl⟩ := h.block_image.symm ▸ hy
      exact ⟨inclusion (sup_le_sup_left hST K) k,hk,hcompat k⟩
  have hKN : K ≤ A := le_sup_left
  let KN := K.subgroupOf A
  let : KN.Normal := (normal_subgroupOf_iff_le_normalizer hKN).mpr (sup_le K.le_normalizer hn)
  obtain ⟨Q,hQ⟩ := P.exists_sylow_map_eq_inf_of_normal KN
  let eK := subgroupOfEquivOfLe hKN
  let Q' := Q.mapSurjective (f := eK.toMonoidHom) eK.surjective
  have hQ' : (Q' : Subgroup K).map K.subtype = T ⊓ K := by
    change ((Q : Subgroup KN).map eK.toMonoidHom).map K.subtype = _
    calc
      _ = ((Q : Subgroup KN).map KN.subtype).map A.subtype := by rw [map_map,map_map]; rfl
      _ = ((P : Subgroup A) ⊓ KN).map A.subtype := congrArg (fun D => D.map A.subtype) hQ
      _ = T ⊓ K := by rw [map_inf _ _ _ A.subtype_injective,hP,map_subgroupOf_eq_of_le hKN]
  refine ⟨{
    twoGroup := hT
    block := h.block
    commute := bot_le
    module_le := hUS
    normalizes := inf_le_left.trans hn
    core := hcore
    product := hcore.trans (h.centralizer_in_normalizing_subgroup x hx hnc S hUS (inf_le_left.trans hn))
    permutes := fun r hr => Or.inl (mem_normalizer_iff_map_conj_eq.mp (hn hr))
    sylow := Q'
    sylow_image := hQ'
    action := act
    coordinates := h.coordinates
    block_image := (hmap K le_sup_left).trans hblock
    baumann_image := (hmap S le_sup_right).trans himage
    equivariant := ?_ }⟩
  intro s u
  let v : Additive ((sourceModule K).subgroupOf A) := Additive.ofMul ⟨⟨u,hUA u.property⟩,u.property⟩
  let p := (alternatingNativeCoordinates h T).toMonoidHom.toAdditiveLeft.toZModLinearMap 2
  let ρ := NormalElementaryQuotient.representation _ q hq hker
  have hh := congrArg (fun w : core (Fin 5) => (h.coordinates.symm (Multiplicative.ofAdd w) : G))
    (he (q (inclusion hBA s)) v)
  change (h.coordinates.symm (h.coordinates
    ⟨((ρ (q (inclusion hBA s)) v).toMul : A),(ρ (q (inclusion hBA s)) v).toMul.property⟩) : G) = _ at hh
  rw [h.coordinates.symm_apply_apply] at hh
  have hv := congrArg Subtype.val (NormalElementaryQuotient.representation_apply _ q hq hker (inclusion hBA s) v)
  exact hh.symm.trans hv
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
