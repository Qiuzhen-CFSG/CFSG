module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryLocalCore

/-!
# The two-core of the original residual/Sylow local base

For a paired plane U, keep L₀ = O²(C_L(U)) and T₀ = C_T(U).
We prove O₂(L₀T₀) = O₂(LT). The whole-orbit centralizer C in LT
is normal. Its residual lies in L₀, while its Sylow intersection is Q,
so C lies in L₀T₀. In the symmetric-three quotient, L₀ maps onto A₃.
Consequently L₀T₀ is normal in C_{LT}(U), whose two-core is already Q.
No assumption that C is a two-group, or that T₀ is Sylow in C_G(U),
is used.

The chosen-orbit application is NonFFSourceDoubledBinaryResidualCore.
This discharges the crucial local-core identity of Aschbacher–Smith
§7.7.2–3, printed pp.704–705, refs/quasithin.pdf. The constrained-group
and ambient-containment arguments remain with qt-d-1222-nonff-doubled.
-/

open Subgroup
public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryResidualCore

private theorem map_pCoreIn_subgroupOf
    {G : Type*} [Group G] (p : ℕ) (A J : Subgroup G) (hAJ : A ≤ J) :
    ((A.subgroupOf J).pCoreIn p).map J.subtype = A.pCoreIn p := by
  let e : A.subgroupOf J ≃* A := subgroupOfEquivOfLe hAJ
  have he : J.subtype.comp (A.subgroupOf J).subtype = A.subtype.comp e.toMonoidHom := rfl
  rw [pCoreIn, map_map, he, ← map_map, pCore_map_iso]
  rfl

private theorem map_residual_subgroupOf
    {G : Type*} [Group G] [Finite G] (p : ℕ) (A J : Subgroup G) (hAJ : A ≤ J) :
    ((pResidual p (A.subgroupOf J)).map (A.subgroupOf J).subtype).map J.subtype =
      (pResidual p A).map A.subtype := by
  let e : A.subgroupOf J ≃* A := subgroupOfEquivOfLe hAJ
  have he : J.subtype.comp (A.subgroupOf J).subtype = A.subtype.comp e.toMonoidHom := rfl
  rw [map_map, he, ← map_map, map_pResidual_of_surjective p _ e.surjective]

private theorem kernel_le_localBase
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (L C K : Subgroup G) [L.Normal] [C.Normal]
    (hgen : L ⊔ (S : Subgroup G) = ⊤) (hCK : C ≤ K)
    (hSC : (S : Subgroup G) ⊓ C ≤ (S : Subgroup G) ⊓ K) :
    C ≤ (pResidual 2 (L ⊓ K : Subgroup G)).map (L ⊓ K).subtype ⊔
      ((S : Subgroup G) ⊓ K) := by
  let RC := (pResidual 2 C).map C.subtype
  have hRL : RC ≤ L := (map_pResidual_le 2 C.subtype).trans
    (sInf_le ⟨inferInstance, isPGroup_quotient_of_sup_eq_top L (S : Subgroup G)
      S.isPGroup' hgen⟩)
  have hRCK : RC ≤ L ⊓ K := le_inf hRL ((map_subtype_le _).trans hCK)
  have hR : RC ≤ (pResidual 2 (L ⊓ K : Subgroup G)).map (L ⊓ K).subtype := by
    have hp := (pResidual_eq_top_iff 2 RC).mpr (isPPerfect_embedded_pResidual 2 C)
    have hm := embedded_pResidual_mono 2 hRCK
    rw [hp, ← MonoidHom.range_eq_map, range_subtype] at hm
    exact hm
  obtain ⟨SC,hSC'⟩ := S.exists_subgroupOf_eq_of_normal C
  have hs := congrArg (fun A : Subgroup C => A.map C.subtype)
    (pResidual_sup_sylow_eq_top SC)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype,
    hSC', subgroupOf_map_subtype] at hs
  rw [← hs]
  exact sup_le (hR.trans le_sup_left) (hSC.trans le_sup_right)

private theorem symmetricThree_residual :
    pResidual 2 (Equiv.Perm (Fin 3)) = alternatingGroup (Fin 3) := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    change (alternatingGroup (Fin 3)).index = 2 ^ 1
    simp
  · intro x hx
    have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      rfl
    have hp : x ^ 3 = 1 := congrArg Subtype.val
      (hc ▸ pow_card_eq_one' (x := (⟨x,hx⟩ : alternatingGroup (Fin 3))))
    exact mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hp))

private theorem residual_sylow_core
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (L C K : Subgroup G) [L.Normal] [C.Normal]
    (hgen : L ⊔ (S : Subgroup G) = ⊤) (hCK : C ≤ K)
    (hSC : (S : Subgroup G) ⊓ C = pCore 2 G)
    (hcore : K.pCoreIn 2 = pCore 2 G)
    (π : K →* Equiv.Perm (Fin 3)) (hker : π.ker ≤ C.subgroupOf K)
    (hπ : Function.Surjective (π.comp (inclusion (show L ⊓ K ≤ K from inf_le_right)))) :
    ((pResidual 2 (L ⊓ K : Subgroup G)).map (L ⊓ K).subtype ⊔
      ((S : Subgroup G) ⊓ K)).pCoreIn 2 = pCore 2 G := by
  let R := (pResidual 2 (L ⊓ K : Subgroup G)).map (L ⊓ K).subtype
  let B := R ⊔ ((S : Subgroup G) ⊓ K)
  have hBK : B ≤ K := sup_le ((map_subtype_le _).trans inf_le_right) inf_le_right
  have hCB : C ≤ B := kernel_le_localBase S L C K hgen hCK (inf_le_inf_left _ hCK)
  have hQB : pCore 2 G ≤ B := by
    rw [← hSC]
    exact (inf_le_inf_left _ hCK).trans le_sup_right
  have hkerB : π.ker ≤ B.subgroupOf K := hker.trans (subgroupOf_mono K hCB)
  let P := (B.subgroupOf K).map π
  have hAP : alternatingGroup (Fin 3) ≤ P := by
    rw [← symmetricThree_residual, ← map_pResidual_of_surjective 2 _ hπ]
    rintro x ⟨r,hr,rfl⟩
    refine ⟨inclusion inf_le_right r,?_,rfl⟩
    exact (show R ≤ B from le_sup_left) (mem_map_of_mem (L ⊓ K).subtype hr)
  have hPi : P.index ∣ 2 := by
    simpa using index_dvd_of_le hAP
  have hPN : P.Normal := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hPi with he | he
    · exact normal_of_index_eq_one he
    · exact normal_of_index_eq_two he
  have hBN : (B.subgroupOf K).Normal := by
    have he : P.comap π = B.subgroupOf K := by
      rw [comap_map_eq,sup_eq_left.mpr hkerB]
    rw [← he]
    exact hPN.comap π
  apply le_antisymm
  · exact (pCoreIn_mono_of_normalizes hBK
      ((normal_subgroupOf_iff_le_normalizer hBK).mp hBN)).trans_eq hcore
  · exact le_pCoreIn_of_normalizes pCore_isPGroup hQB
      (by rw [normalizer_eq_top]; exact le_top)

private theorem relative_residual_sylow_core
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (L C K : Subgroup G)
    (hTN : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hCK : C ≤ K) (hKJ : K ≤ L ⊔ (T : Subgroup G))
    (hCN : L ⊔ (T : Subgroup G) ≤ normalizer (C : Set G))
    (hTC : (T : Subgroup G) ⊓ C = (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcore : K.pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (π : K →* Equiv.Perm (Fin 3)) (hker : π.ker ≤ C.subgroupOf K)
    (hπ : Function.Surjective (π.comp (inclusion (show L ⊓ K ≤ K from inf_le_right)))) :
    ((pResidual 2 (L ⊓ K : Subgroup G)).map (L ⊓ K).subtype ⊔
      ((T : Subgroup G) ⊓ K)).pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := L ⊔ (T : Subgroup G)
  let S : Sylow 2 J := T.subtype le_sup_right
  let LJ := L.subgroupOf J
  let CJ := C.subgroupOf J
  let KJ := K.subgroupOf J
  let R := (pResidual 2 (L ⊓ K : Subgroup G)).map (L ⊓ K).subtype
  let B := R ⊔ ((T : Subgroup G) ⊓ K)
  let BJ := (pResidual 2 (LJ ⊓ KJ : Subgroup J)).map (LJ ⊓ KJ).subtype ⊔
    ((S : Subgroup J) ⊓ KJ)
  let e : KJ ≃* K := subgroupOfEquivOfLe hKJ
  let πJ := π.comp e.toMonoidHom
  have hLJ : L ≤ J := le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hCJ : C ≤ J := hCK.trans hKJ
  let _ : LJ.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hTN)
  let _ : CJ.Normal := normal_subgroupOf_of_le_normalizer hCN
  have hgen : LJ ⊔ (S : Subgroup J) = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hLJ,
      map_subgroupOf_eq_of_le hTJ,← MonoidHom.range_eq_map,range_subtype]
  have hSC : (S : Subgroup J) ⊓ CJ = pCore 2 J := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_inf _ _ _ J.subtype_injective,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTJ,map_subgroupOf_eq_of_le hCJ]
    exact hTC
  have hcoreJ : KJ.pCoreIn 2 = pCore 2 J := by
    apply map_injective J.subtype_injective
    rw [map_pCoreIn_subgroupOf 2 K J hKJ]
    exact hcore
  have hπJ : Function.Surjective
      (πJ.comp (inclusion (show LJ ⊓ KJ ≤ KJ from inf_le_right))) := by
    intro x
    obtain ⟨r,hr⟩ := hπ x
    exact ⟨⟨⟨r,hLJ r.property.1⟩,r.property⟩,hr⟩
  have hBJ : BJ.pCoreIn 2 = pCore 2 J := residual_sylow_core S LJ CJ KJ hgen
    (subgroupOf_mono J hCK) hSC hcoreJ πJ (fun x hx => hker hx) hπJ
  have hBmap : BJ.map J.subtype = B := by
    rw [Subgroup.map_sup,Subgroup.map_inf _ _ _ J.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ,map_subgroupOf_eq_of_le hKJ]
    congr 1
    exact map_residual_subgroupOf 2 (L ⊓ K) J (inf_le_right.trans hKJ)
  have hBJ' : BJ = B.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [hBmap,map_subgroupOf_eq_of_le
      (sup_le ((map_subtype_le _).trans (inf_le_right.trans hKJ)) (inf_le_right.trans hKJ))]
  have hh := congrArg (fun A : Subgroup J => A.map J.subtype) hBJ
  rw [hBJ',map_pCoreIn_subgroupOf 2 B J
    (sup_le ((map_subtype_le _).trans (inf_le_right.trans hKJ)) (inf_le_right.trans hKJ))] at hh
  exact hh

open Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE
open BinaryLinearThree
open CFSG.Quasithin.Chapter7.NormalizedSource
open DoubledBinaryPlanes DoubledBinaryPlaneQuotient DoubledBinaryLocalCore

/-- The original residual/Sylow local base has exactly the ambient local two-core. -/
theorem pairedPlane_localBase_core
    {G : Type*} [_root_.Group G] [Finite G]
    (W₀ L : Subgroup G) (T : Sylow 2 G) [IsElementaryAbelian 2 W₀]
    (hTN : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hLN : L ≤ normalizer (W₀ : Set G))
    (hTW : (T : Subgroup G) ≤ normalizer (W₀ : Set G))
    (hQ : (T : Subgroup G) ⊓ centralizer (W₀ : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (q : L →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (E : Additive W₀ ≃ₗ[ZMod 2] NaturalDual.Space)
    (hE : ∀ l w, E (automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) =
        NaturalDual.action (q l) (E w))
    (a : Automizer W₀ ≃* MulAut BinaryLinearThree.Group)
    (ha : ∀ l, a (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) = MulAut.conj (q l))
    (hcov : ∀ b g w, E (automizerRepresentation W₀ b (E.symm (NaturalDual.action g (E w)))) =
      NaturalDual.action (a b g) (E (automizerRepresentation W₀ b w)))
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hfv : f v = 1) :
    (localBase L (T : Subgroup G) (ambientPlane W₀ E v f)).pCoreIn 2 =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let U := ambientPlane W₀ E v f
  let J := L ⊔ (T : Subgroup G)
  let K := J ⊓ centralizer (U : Set G)
  let C := J ⊓ centralizer (W₀ : Set G)
  have hJN : J ≤ normalizer (W₀ : Set G) := sup_le hLN hTW
  have hCK : C ≤ K := inf_le_inf_left J (centralizer_le (ambientPlane_le_orbit W₀ E v f))
  have hCN : J ≤ normalizer (C : Set G) :=
    (le_inf J.le_normalizer (hJN.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hTC : (T : Subgroup G) ⊓ C = J.pCoreIn 2 := by
    change (T : Subgroup G) ⊓ (J ⊓ centralizer (W₀ : Set G)) = _
    rw [← inf_assoc,inf_eq_left.mpr (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact hQ
  have hcore : K.pCoreIn 2 = J.pCoreIn 2 := pairedPlane_core W₀ L J hLN le_sup_left
    hJN (hQ ▸ (show (T : Subgroup G) ⊓ centralizer (W₀ : Set G) ≤
      centralizer (W₀ : Set G) from inf_le_right)) q hq E hE a ha hcov v f hfv
  let P := inducedAutomizer W₀ (centralizer (U : Set G))
  let i : K →* normalizer (W₀ : Set G) := inclusion (inf_le_left.trans hJN)
  let qK := W₀.normalizerMonoidHom.rangeRestrict.comp i
  have hqK (k : K) : qK k ∈ P := ⟨i k,k.property.2,rfl⟩
  let p : K →* P := qK.codRestrict P hqK
  obtain ⟨σ⟩ := ambientPlane_equiv W₀ L hLN q hq E hE a ha hcov v f hfv
  let π := σ.toMonoidHom.comp p
  have hker : π.ker ≤ C.subgroupOf K := by
    intro k hk
    have hp : p k = 1 := σ.injective (by
      rw [σ.map_one]
      exact hk)
    have hN : W₀.normalizerMonoidHom (i k) = 1 :=
      congrArg (fun b : P => b.val.val) hp
    change i k ∈ W₀.normalizerMonoidHom.ker at hN
    rw [normalizerMonoidHom_ker] at hN
    exact ⟨k.property.1,hN⟩
  have hπ : Function.Surjective
      (π.comp (inclusion (show L ⊓ K ≤ K from inf_le_right))) := by
    intro x
    have hb := (component_centralizer_image W₀ L hLN q hq E a ha hcov v f hfv).ge
      (σ.symm x).property
    obtain ⟨n,hn,he⟩ := hb
    let r : (L ⊓ K : Subgroup G) := ⟨n,hn.1,(show L ≤ J from le_sup_left) hn.1,hn.2⟩
    have hp : p (inclusion inf_le_right r) = σ.symm x := Subtype.ext he
    refine ⟨r,?_⟩
    change σ (p (inclusion inf_le_right r)) = x
    rw [hp,σ.apply_symm_apply]
  have hh := relative_residual_sylow_core T L C K hTN hCK inf_le_left hCN hTC hcore π hker hπ
  have hLK : L ⊓ K = L ⊓ centralizer (U : Set G) := by
    change L ⊓ (J ⊓ _) = _
    rw [← inf_assoc,inf_eq_left.mpr (show L ≤ J from le_sup_left)]
  have hTK : (T : Subgroup G) ⊓ K = (T : Subgroup G) ⊓ centralizer (U : Set G) := by
    change (T : Subgroup G) ⊓ (J ⊓ _) = _
    rw [← inf_assoc,inf_eq_left.mpr (show (T : Subgroup G) ≤ J from le_sup_right)]
  rw [hLK,hTK] at hh
  exact hh

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryResidualCore
