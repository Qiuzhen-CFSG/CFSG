module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion
public import Theory.GroupTheory.PerfectCenterFrattini
public import Theory.GroupTheory.GeneralizedFitting.NormalComponentCentralizer
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import Theory.GroupTheory.SelfCentralizingCore

/-!
# The retained central extension in the exceptional MS pair

The extension kernel is E = O_{2,Z}(K) O₂(M), where M = LR and K is
L on the relative carrier. Its image modulo Q = O₂(M) is exactly the
embedded center of the component image. Thus E/Q has order three in the
exceptional branch. Perfectness of the component proves source (A)'s
no-supplement condition, while characteristic two kills O_{2'}(E).

These are preparation facts for MS93, not core exhaustion. The odd covering
kernel is retained, and R is the original odd-index radical throughout.
Source: Meierfrankenfeld--Stellmacher (1993), Hypothesis (A), pp.828--829;
Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "T" => R.subgroupOf (L ⊔ R)

/-- Source E, including the central preimage of the original relative component. -/
@[expose] def extensionKernel (_h : SmallMSPair κ L R) : Subgroup M :=
  (centralPreimage (pCore 2 K)).map (K).subtype ⊔ pCore 2 M

instance extensionKernel_normal (h : SmallMSPair κ L R) : (extensionKernel h).Normal := by
  let := h.relative_normal
  have hn : ((centralPreimage (pCore 2 K)).map (K).subtype).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    exact (show (⊤ : Subgroup M) ≤ normalizer (K : Set M) from
      le_normalizer_of_normal).trans
      (normalizer_le_normalizer_characteristic_image K (centralPreimage (pCore 2 K)))
  let := hn
  exact inferInstanceAs
    (((centralPreimage (pCore 2 K)).map (K).subtype) ⊔ pCore 2 M).Normal

/-- The two-core of the retained extension kernel is exactly the ambient core. -/
theorem extensionKernel_twoCore (h : SmallMSPair κ L R) :
    (extensionKernel h).pCoreIn 2 = pCore 2 M := by
  unfold pCoreIn
  rw [pCore_subnormal_eq_comap 2
    (inferInstance : (extensionKernel h).Normal).isSubnormal,
    map_comap_eq, range_subtype]
  exact inf_eq_right.mpr le_sup_right

/-- Source (A)'s odd core vanishes by characteristic-two inheritance, while
its odd quotient is retained. -/
theorem extensionKernel_oddCore (h : SmallMSPair κ L R) :
    pPrimeCore 2 (extensionKernel h) = ⊥ :=
  pPrimeCore_eq_bot_of_centralizer_pCore_le 2
    (normal_core_selfCentralizing h.relative_self_centralizing (extensionKernel h))

private theorem center_map_equiv {A B : Type*} [Group A] [Group B]
    (f : A ≃* B) : (center A).map f.toMonoidHom = center B := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (centerCongr f ⟨a, ha⟩).property
  · intro hx
    exact ⟨f.symm x, (centerCongr f.symm ⟨x, hx⟩).property, f.apply_symm_apply x⟩

/-- Modulo the actual two-core, the kernel is exactly the component center. -/
theorem extensionKernel_image (h : SmallMSPair κ L R) :
    (extensionKernel h).map (QuotientGroup.mk' (pCore 2 M)) =
      (center (componentImage L R)).map (componentImage L R).subtype := by
  let q := QuotientGroup.mk' (pCore 2 M)
  let f := cComponentTwoCoreQuotientEquiv h.component
  have hf : f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)) =
      q.subgroupMap K := by
    ext k
    rfl
  have hi : q.comp (K).subtype = (componentImage L R).subtype.comp
      (f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) := by
    rw [hf]
    rfl
  rw [extensionKernel, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
    map_map]
  change (centralPreimage (pCore 2 K)).map (q.comp (K).subtype) = _
  rw [hi, ← MonoidHom.comp_assoc, ← map_map, map_centralPreimage,
    ← map_map, center_map_equiv]

/-- The intrinsic index is three; the cubic covering kernel is not removed. -/
theorem extensionKernel_core_index (h : SmallMSPair κ L R)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    (pCore 2 (extensionKernel h)).index = 3 := by
  have he : pCore 2 (extensionKernel h) =
      (pCore 2 M).subgroupOf (extensionKernel h) :=
    pCore_subnormal_eq_comap 2 (inferInstance : (extensionKernel h).Normal).isSubnormal
  rw [he, ← relIndex, ← QuotientGroup.ker_mk' (pCore 2 M), relIndex_ker,
    extensionKernel_image h, card_map_of_injective (componentImage L R).subtype_injective]
  let f := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  let c := (cComponentTwoCoreQuotientEquiv h.component).symm.trans
    (QuotientGroup.congr _ _ f (pCore_map_iso 2 f))
  exact (Nat.card_congr (centerCongr c).toEquiv).trans hz

/-- Source (A)'s quotient is odd on the original kernel, with no Sylow assumption. -/
theorem extensionKernel_odd_index (h : SmallMSPair κ L R)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    Nat.Coprime 2 (pCore 2 (extensionKernel h)).index := by
  rw [extensionKernel_core_index h hz]
  decide

private theorem perfect_le_of_le_sup_center {A : Type*} [Group A]
    (C F : Subgroup A) [C.Normal] [Group.IsPerfect C]
    (h : C ≤ F ⊔ (center C).map C.subtype) : C ≤ F := by
  let Z := (center C).map C.subtype
  let : Z.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    exact (show (⊤ : Subgroup A) ≤ normalizer (C : Set A) from
      le_normalizer_of_normal).trans
      (normalizer_le_normalizer_characteristic_image C (center C))
  have hs : F.subgroupOf C ⊔ center C = ⊤ := by
    apply top_unique
    intro c _
    obtain ⟨f, hf, z, hz, he⟩ := mem_sup_of_normal_right.mp (h c.property)
    obtain ⟨z', hz', rfl⟩ := hz
    have hfC : f ∈ C := (C.mul_mem_cancel_right z'.property).mp (he ▸ c.property)
    have hc : (⟨f, hfC⟩ : C) * z' = c := Subtype.ext he
    rw [← hc]
    exact mul_mem (mem_sup_left hf) (mem_sup_right hz')
  have ht := eq_top_of_sup_center_eq_top (F.subgroupOf C) hs
  intro c hc
  have hm : (⟨c, hc⟩ : C) ∈ F.subgroupOf C := ht ▸ mem_top _
  exact hm

/-- Perfectness removes every proposed supplement to the retained odd center,
which is the last clause of source (A). -/
theorem extensionKernel_no_supplement (h : SmallMSPair κ L R)
    (F : Subgroup M) (hF : K ≤ F ⊔ extensionKernel h) :
    extensionKernel h ≤ F ⊔ (extensionKernel h).pCoreIn 2 := by
  let := h.relative_normal
  let := h.component_perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)).symm.toMonoidHom)
    (subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)).symm.surjective
  let q := QuotientGroup.mk' (pCore 2 M)
  let : (componentImage L R).Normal := (inferInstance : (K).Normal).map q
    (QuotientGroup.mk'_surjective _)
  let : Group.IsPerfect (componentImage L R) := Group.IsPerfect.map q
  have hCF : componentImage L R ≤ F.map q ⊔
      (center (componentImage L R)).map (componentImage L R).subtype := by
    have hm := map_mono (f := q) hF
    rw [Subgroup.map_sup, extensionKernel_image h] at hm
    exact hm
  have hEF : (extensionKernel h).map q ≤ F.map q := by
    rw [extensionKernel_image h]
    exact (map_subtype_le _).trans (perfect_le_of_le_sup_center _ _ hCF)
  have hh := map_le_iff_le_comap.mp hEF
  rwa [comap_map_eq, QuotientGroup.ker_mk', ← extensionKernel_twoCore h] at hh

/-- The retained kernel intersects the component in its exact central preimage. -/
theorem extensionKernel_component_intersection (h : SmallMSPair κ L R) :
    (extensionKernel h).comap (K).subtype = centralPreimage (pCore 2 K) := by
  ext k
  constructor
  · intro hk
    obtain ⟨z, hz, q, hq, he⟩ := mem_sup_of_normal_right.mp hk
    obtain ⟨z', hz', rfl⟩ := hz
    have hqK : q ∈ K := ((K).mul_mem_cancel_left z'.property).mp (he ▸ k.property)
    have hq' : (⟨q, hqK⟩ : K) ∈ pCore 2 K := by
      rw [pCore_subnormal_eq_comap 2 h.component.subnormal]
      exact hq
    have hk' : z' * (⟨q, hqK⟩ : K) = k := Subtype.ext he
    rw [← hk']
    exact mul_mem hz' (le_centralPreimage _ hq')
  · intro hk
    exact mem_sup_left (mem_map_of_mem (K).subtype hk)

/-- The component in M/E has the actual alternating-six marking. The map
starts with the literal quotient by E, so no unconnected family tag occurs. -/
def extensionKernel_component_equiv (h : SmallMSPair κ L R) (e : CentralMarking L) :
    (K).map (QuotientGroup.mk' (extensionKernel h)) ≃* alternatingGroup (Fin 6) := by
  let q := (QuotientGroup.mk' (extensionKernel h)).subgroupMap K
  have hk : q.ker = centralPreimage (pCore 2 K) := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact extensionKernel_component_intersection h
  let f := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  let c := QuotientGroup.congr _ _ f (pCore_map_iso 2 f)
  exact (QuotientGroup.quotientKerEquivOfSurjective q
    ((QuotientGroup.mk' (extensionKernel h)).subgroupMap_surjective K)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      ((centralPreimageQuotientEquiv (pCore 2 K)).trans
        ((QuotientGroup.congr _ _ c (center_map_equiv c)).trans
          (SmallMSPair.alternatingCentralQuotientEquiv e))))

/-- The initial orbit's full centralizer is bounded by E, keeping the possible
odd center. This uses the genuine initial action and no exhaustion equality. -/
theorem orbit_centralizer_le_extensionKernel (h : SmallMSPair κ L R)
    (e : CentralMarking L) :
    centralizer (ChapterC.MSCentralOrbit.omegaOrbit (R.subgroupOf (L ⊔ R)) : Set M) ≤
      extensionKernel h := by
  let := h.relative_normal
  let := h.relative_core_quasisimple e
  let q := QuotientGroup.mk' (pCore 2 M)
  let C := componentImage L R
  let : C.Normal := (inferInstance : (K).Normal).map q (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv h.component)
  have hsup : C ⊔ (T).map q = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 M) x
    obtain ⟨k, hk, r, hr, rfl⟩ := h.relative_product m
    rw [map_mul]
    exact mul_mem (mem_sup_left (mem_map_of_mem q hk))
      (mem_sup_right (mem_map_of_mem q hr))
  have hF : generalizedFitting (M ⧸ pCore 2 M) = C :=
    generalizedFitting_eq_of_quasisimple_two_quotient C
      (isPGroup_quotient_of_sup_eq_top C ((T).map q)
        (h.relative_radical.isPGroup.map q) hsup) (pCore_quotient_pCore_eq_bot 2)
  have hfC : fittingSubgroup (M ⧸ pCore 2 M) ≤ C :=
    (fitting_le_generalizedFitting _).trans hF.le
  have hfc : fittingSubgroup (M ⧸ pCore 2 M) ≤ centralizer (C : Set _) := by
    rw [fitting_eq_map_centralizer_of_normal_component C]
    exact map_subtype_le _
  have hfZ : fittingSubgroup (M ⧸ pCore 2 M) ≤ (center C).map C.subtype := by
    intro x hx
    refine ⟨⟨x, hfC hx⟩, mem_center_iff.mpr ?_, rfl⟩
    intro y
    exact Subtype.ext (hfc hx y y.property)
  have hi := (ChapterC.MSCentralOrbit.centralizer_image_le_fitting K T h.component
    h.relative_radical.isPGroup h.relative_radical_ne_bot h.relative_radical.twoCore_le
    h.relative_self_centralizing h.relative_product h.relative_characteristic).trans hfZ
  rw [← extensionKernel_image h] at hi
  have hh := map_le_iff_le_comap.mp hi
  rwa [comap_map_eq, QuotientGroup.ker_mk', sup_of_le_left
    (show pCore 2 M ≤ extensionKernel h from le_sup_right)] at hh

/-- The larger central-omega layer has the same upper bound on its kernel. -/
theorem centralOmega_centralizer_le_extensionKernel (h : SmallMSPair κ L R)
    (e : CentralMarking L) :
    centralizer (centralOmega L R : Set M) ≤ extensionKernel h :=
  (centralizer_le (ChapterC.MSCentralOrbit.omegaOrbit_le_centralOmega T
    h.relative_radical.twoCore_le h.relative_self_centralizing)).trans
      (orbit_centralizer_le_extensionKernel h e)

/-- Before exhaustion there are exactly two possible kernels on X: Q or E.
The cubic alternative is retained as a genuine remaining case. -/
theorem centralOmega_centralizer_cases (h : SmallMSPair κ L R)
    (e : CentralMarking L) (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    centralizer (centralOmega L R : Set M) = pCore 2 M ∨
      centralizer (centralOmega L R : Set M) = extensionKernel h := by
  let D := centralizer (centralOmega L R : Set M)
  have hQD : pCore 2 M ≤ D := by
    intro q hq x hx
    exact (((mem_omegaCenterIn_iff _ _).mp hx).2.1 q hq).symm
  have hDE := centralOmega_centralizer_le_extensionKernel h e
  have hi : (pCore 2 M).relIndex (extensionKernel h) = 3 := by
    change ((pCore 2 M).comap (extensionKernel h).subtype).index = 3
    rw [← pCore_subnormal_eq_comap 2
      (inferInstance : (extensionKernel h).Normal).isSubnormal]
    exact extensionKernel_core_index h hz
  have hm := relIndex_mul_relIndex (pCore 2 M) D (extensionKernel h) hQD hDE
  rw [hi] at hm
  have hd : (pCore 2 M).relIndex D ∣ 3 := ⟨D.relIndex (extensionKernel h), hm.symm⟩
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with hone | hthree
  · exact Or.inl (le_antisymm (relIndex_eq_one.mp hone) hQD)
  · rw [hthree] at hm
    have hone : D.relIndex (extensionKernel h) = 1 := by omega
    exact Or.inr (le_antisymm hDE (relIndex_eq_one.mp hone))

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
