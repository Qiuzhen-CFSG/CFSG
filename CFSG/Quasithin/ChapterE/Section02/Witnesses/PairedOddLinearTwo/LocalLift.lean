module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedOddLinearTwo.LocalGeometry
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.OriginalImage
public import Theory.GroupTheory.SylowQuotientPreimage

/-!
# Lifting the component-local subgroup to the original source

When the original maximal core equals O₂(H), the full preimage of the
component-local subgroup has the prescribed Sylow intersection. The Sylow
kernel lifts minimal parabolicity, while the component automizer identifies
the new simple component image with the original one. A normal elementary
Sylow subgroup outside the original core stays outside the new core.

This keeps all maximal subgroups, quotient maps and component embeddings
literal for the paired PSL₂(7) reduction in Aschbacher–Smith E.2.17, p.230.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
variable {H : Type*} [Group H] [Finite H]

theorem source_component_local_geometry
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hJ : ChapterB.minimalParabolicCore T hP = pCore 2 H)
    (hHX : IsStronglyQuasithin (H ⧸ ChapterB.minimalParabolicCore T hP))
    (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hVT : V ≤ T) (hVN : (V.subgroupOf (T : Subgroup H)).Normal)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hVK : V ≤ normalizer (K : Set H)) :
    ∃ L : Subgroup H, V ≤ L ∧ pCore 2 H ≤ L ∧
      ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup H).subgroupOf L ∧
        ∃ hPS : ChapterB.IsMinimalParabolicOver S ⊤,
          ¬ Group.IsSolvable L ∧ ∃ K0 : Subgroup L,
            K0.IsCComponent ∧ K0.Normal ∧ K0 ⊔ (S : Subgroup L) = ⊤ ∧
            Nonempty ((K0.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hPS))) ≃*
              K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ∧
            (ChapterB.minimalParabolicMax S hPS).map L.subtype ≤ ChapterB.minimalParabolicMax T hP ∧
            ¬ V.subgroupOf L ≤ ChapterB.minimalParabolicCore S hPS := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  have hq := QuotientGroup.mk'_surjective J
  let TX := T.mapSurjective hq
  let C := K.map q
  let N := normalizer (C : Set (H ⧸ J))
  let B := C ⊔ ((TX : Subgroup (H ⧸ J)) ⊓ N)
  let L := B.comap q
  have hCB : C ≤ B := le_sup_left
  have hBN : B ≤ N := sup_le C.le_normalizer inf_le_right
  have hJL : J ≤ L := by
    intro x hx
    change q x ∈ B
    rw [show q x=1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact B.one_mem
  have hJT : J ≤ (T : Subgroup H) := by
    change ChapterB.minimalParabolicCore T hP ≤ _
    rw [hJ]
    exact pCore_isPGroup.le_sylow_of_normal T
  have hKL : K ≤ L := fun x hx => hCB (mem_map_of_mem q hx)
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  have hLN : L ≤ normalizer (K : Set H) := by
    rw [←normalizer_cComponent_quotient hK J]
    exact comap_mono hBN
  have hVL : V ≤ L := by
    intro v hv
    exact (show (TX : Subgroup (H ⧸ J)) ⊓ N ≤ B from le_sup_right)
      ⟨mem_map_of_mem q (hVT hv),
        (show v ∈ N.comap q from (normalizer_cComponent_quotient hK J).symm ▸ hVK hv)⟩
  have hi := Structure.source_component_simple_image T hP hs K hK hgen
  let : IsSimpleGroup C := hi.1
  obtain ⟨hPX,hJX⟩ := Structure.source_star_minimal_core_free T hP
  have hZ : center C = ⊥ := by
    let := hi.2.1.2
    rcases (inferInstance : (center C).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative C (center_eq_top_iff.mp hz)).elim
  obtain ⟨SB,hSB,ha,hPB,hMB,hJB⟩ := component_local_minimal hHX TX hPX hi.2.1 hi.2.2.2 hZ
  let a := (NormalizerAction.quotient C).comp (inclusion hBN)
  obtain ⟨S,hS⟩ := Sylow.exists_subgroupOf_eq_comap T q B SB hSB
  let qL : L →* B := (q.comp L.subtype).codRestrict B (fun x => x.property)
  have hqL : Function.Surjective qL := by
    intro y
    obtain ⟨x,hx⟩ := hq y
    exact ⟨⟨x,show q x ∈ B from hx ▸ y.property⟩,Subtype.ext hx⟩
  have hker : qL.ker ≤ (S : Subgroup L) := by
    intro x hx
    rw [hS]
    exact hJT ((QuotientGroup.eq_one_iff (x:H)).mp (congrArg Subtype.val hx))
  have hSim : (S : Subgroup L).map qL = (SB : Subgroup B) := by
    rw [hS,hSB]
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact mem_map_of_mem q hx
    · rintro ⟨x,hx,he⟩
      exact ⟨⟨x,show q x ∈ B from he ▸ y.property⟩,hx,Subtype.ext he⟩
  have heS : S.mapSurjective hqL = SB := Sylow.ext hSim
  have hPim : ChapterB.IsMinimalParabolicOver (S.mapSurjective hqL) ⊤ := heS.symm ▸ hPB
  let hPS := ChapterB.minimalParabolic_of_surjective S qL hqL hker hPim
  have hMim : ChapterB.minimalParabolicMax (S.mapSurjective hqL) hPim ≤
      (ChapterB.minimalParabolicMax TX hPX).subgroupOf B := by
    subst SB
    exact hMB
  have hJim : ChapterB.minimalParabolicCore (S.mapSurjective hqL) hPim = a.ker := by
    subst SB
    exact hJB
  have hML : (ChapterB.minimalParabolicMax S hPS).map L.subtype ≤
      ChapterB.minimalParabolicMax T hP := by
    rintro x ⟨y,hy,rfl⟩
    rw [ChapterB.minimalParabolicMax_comap S qL hqL hker hPim] at hy
    have hh := hMim hy
    have hMX : ChapterB.minimalParabolicMax TX hPX =
        (ChapterB.minimalParabolicMax T hP).map q :=
      (ChapterB.minimalParabolicMax_map_core T hP q hq (by rw [QuotientGroup.ker_mk'])).symm
    rw [hMX] at hh
    have hJM : J ≤ ChapterB.minimalParabolicMax T hP :=
      hJT.trans (ChapterB.minimalParabolicMax_spec T hP).2
    have hpre : ((ChapterB.minimalParabolicMax T hP).map q).comap q =
        ChapterB.minimalParabolicMax T hP := comap_map_eq_self (by rwa [QuotientGroup.ker_mk'])
    exact hpre ▸ hh
  let K0 := K.subgroupOf L
  let : K0.Normal := (normal_subgroupOf_iff_le_normalizer hKL).mpr hLN
  have hK0 : K0.IsCComponent := hK.subgroupOf hKL
  have hgen0 : K0 ⊔ (S : Subgroup L) = ⊤ := by
    have hKim : K0.map qL = C.subgroupOf B := by
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact mem_map_of_mem q hx
      · rintro ⟨x,hx,he⟩
        exact ⟨⟨x,hKL hx⟩,hx,Subtype.ext he⟩
    have he : (K0 ⊔ (S : Subgroup L)).map qL = (⊤ : Subgroup L).map qL := by
      rw [Subgroup.map_sup,hKim,hSim,map_top_of_surjective qL hqL,hSB]
      apply map_injective B.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hCB,subgroupOf_map_subtype,
        ←MonoidHom.range_eq_map,range_subtype]
      have hTI : (TX : Subgroup (H ⧸ J)) ⊓ B = (TX : Subgroup (H ⧸ J)) ⊓ N :=
        le_antisymm (inf_le_inf_left _ hBN) (le_inf inf_le_left le_sup_right)
      rw [hTI]
    have he' := map_eq_map_iff.mp he
    simpa only [sup_eq_left.mpr (hker.trans le_sup_right),top_sup_eq] using he'
  have hsL : ¬ Group.IsSolvable L := by
    intro hh
    let := hh
    exact hK0.not_isSolvable inferInstance
  let b := a.comp qL
  have hb : Function.Surjective b := ha.comp hqL
  have hcore : ChapterB.minimalParabolicCore S hPS = b.ker := by
    rw [ChapterB.minimalParabolicCore_comap S qL hqL hker hPim,hJim]
    rfl
  have hKb : K0.map b = NormalizerAction.componentImage C := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨inclusion C.le_normalizer ⟨q x,mem_map_of_mem q hx⟩,
        mem_map_of_mem q hx,rfl⟩
    · rintro ⟨c,hc,rfl⟩
      obtain ⟨k,hk,he⟩ := hc
      refine ⟨⟨k,hKL hk⟩,hk,?_⟩
      change NormalizerAction.quotient C ⟨q k,hBN (hKL hk)⟩ = NormalizerAction.quotient C c
      congr 1
      exact Subtype.ext he
  let q0 := QuotientGroup.mk' (ChapterB.minimalParabolicCore S hPS)
  let eL := (QuotientGroup.quotientMulEquivOfEq hcore).trans
    (QuotientGroup.quotientKerEquivOfSurjective b hb)
  have heL (x : L) : eL (q0 x) = b x := rfl
  have hKe : (K0.map q0).map eL.toMonoidHom = NormalizerAction.componentImage C := by
    rw [map_map,show eL.toMonoidHom.comp q0 = b from MonoidHom.ext heL,hKb]
  let eK : K0.map q0 ≃* C := ((eL.subgroupMap (K0.map q0)).trans
    (MulEquiv.subgroupCongr hKe)).trans (NormalizerAction.componentEquivOfCenterEqBot C hZ).symm
  have houtL : ¬ V.subgroupOf L ≤ ChapterB.minimalParabolicCore S hPS := by
    intro hh
    let W := V.map q
    let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
    have hWT : W ≤ (TX : Subgroup (H ⧸ J)) := map_mono hVT
    have hTW : (TX : Subgroup (H ⧸ J)) ≤ normalizer (W : Set (H ⧸ J)) :=
      (map_mono ((normal_subgroupOf_iff_le_normalizer hVT).mp hVN)).trans (le_normalizer_map q)
    have hWN : (W.subgroupOf (TX : Subgroup (H ⧸ J))).Normal :=
      (normal_subgroupOf_iff_le_normalizer hWT).mpr hTW
    have hne : W ≠ ⊥ := by
      intro he
      exact hout (by simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff V).mp he)
    apply component_local_image_nontrivial TX hPX hJX C hi.2.2.2 W hWT hWN hne
    rintro z ⟨v,hv,rfl⟩
    have hvb : b ⟨v,hVL hv⟩ = 1 := by
      have hx := hh (show (⟨v,hVL hv⟩ : L) ∈ V.subgroupOf L from hv)
      rwa [hcore] at hx
    exact (NormalizerAction.quotient_eq_one_iff C
      ⟨q v,hBN (hVL hv)⟩).mp hvb
  have hQL : pCore 2 H ≤ L := by rw [←hJ]; exact hJL
  exact ⟨L,hVL,hQL,S,hS,hPS,hsL,K0,hK0,inferInstance,hgen0,⟨eK⟩,hML,houtL⟩
end CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
