module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.PrimePSL2
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.KernelIdentification
public import CFSG.Quasithin.ChapterA.Section01.RankActions.PrimeSL2CoverRigidity
public import CFSG.Quasithin.ChapterA.Section01.RankActions.PerfectActions.LinearRecognition
public import Theory.GroupTheory.PerfectCenterFrattini

/-!
# A.3.12 in the noncentral odd-core branch

The preceding genuine noncentral-Fitting theorem constructs the actual
quotient L/O(L) as prime-field SL₂. Map the original local component using
the exact quotient and the original full Sylow intersection. Prime-field
perfect-subgroup recognition gives the full image or SL₂(5). In the former
case the original B supplements O(L). In the latter, its projective image
is proper: perfection forbids a proper central supplement in SL₂. The
full-Sylow prime PSL₂ sieve supplies both exceptional congruences.

Thus the source alternatives (21) and (22) are proved with the intrinsic
odd core and the literal image of B, without a desired-embedding premise.

Source: Aschbacher–Smith A.3.12(21)–(22), printed pp.47–48, from A.3.6;
the application in C.5.12 is on printed p.163.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The full noncentral-Fitting branch of A.3.12, with the prime-field
odd-core quotient produced from the original SQTK assumptions. -/
theorem embedding_of_noncentral_fitting
    {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    (hn : ¬ fittingSubgroup L ≤ center L) : A312Embedding B L := by
  let := hL.perfect
  have hquot := NoncentralFitting.primeSL2FittingQuotient_of_noncentral
    RankActions.primeSL2CoverRigidity hG hO hL hn
  have hFO := NoncentralFitting.fitting_eq_oddCore hL hO hquot
  obtain ⟨p, hp, hlarge, ⟨e⟩⟩ := hquot
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  let N := pPrimeCore 2 L
  let q := QuotientGroup.mk' N
  let a : (L ⧸ N) ≃* SL(2, ZMod p) :=
    (QuotientGroup.quotientMulEquivOfEq hFO.symm).trans e
  let f := a.toMonoidHom.comp q
  have hf : Function.Surjective f := a.surjective.comp (QuotientGroup.mk'_surjective N)
  have hk : f.ker = N := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective, QuotientGroup.ker_mk']
  let : Group.IsSolvable N := by
    let n : N ≃* fittingSubgroup L := MulEquiv.subgroupCongr hFO.symm
    exact Group.isSolvable_of_isSolvable_injective (f := n.toMonoidHom) n.injective
  let : Group.IsSolvable f.ker := hk.symm ▸ inferInstance
  let : Group.IsPerfect SL(2, ZMod p) := Group.IsPerfect.ofSurjective hf
  have hnc : ⁅pPrimeCore 2 L, (⊤ : Subgroup L)⁆ ≠ ⊥ := by
    intro he
    apply hn
    rw [hFO]
    exact commutator_top_right_eq_bot_iff_le_center.mp he
  have hlargeModel : LocalModels.IsSL (L ⧸ pPrimeCore 2 L) 2 p :=
    ⟨ZMod p, inferInstance, inferInstance, by simp, ⟨a⟩⟩
  obtain ⟨S, _, hlocal⟩ := exists_local_sylow_restriction T hB hBL hL.subnormal
  let K := (B.subgroupOf L).map f
  let Sf := S.mapSurjective hf
  have hK : K ∈ localCComponents Sf :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal f
  have htopK : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using
      hK.subgroupOf_of_le (show K ≤ K from le_rfl) (show K ≤ K ⊔ Sf from le_sup_left)
  let : Group.IsPerfect K := Group.IsPerfect.top_iff.mp htopK.perfect
  let : Nontrivial (⊤ : Subgroup K) := (nontrivial_iff_ne_bot _).mpr htopK.ne_bot
  let : Nontrivial K := (topEquiv (G := K)).injective.nontrivial
  by_cases hKt : K = ⊤
  · have hgen : B ⊔ N.map L.subtype = L := by
      have hi := congrArg (Subgroup.comap f) hKt
      change ((B.subgroupOf L).map f).comap f = (⊤ : Subgroup SL(2, ZMod p)).comap f at hi
      rw [comap_map_eq, hk, comap_top] at hi
      have hm := congrArg (Subgroup.map L.subtype) hi
      simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le hBL,
        ← MonoidHom.range_eq_map, range_subtype] using hm
    exact .twenty_one p hp ho hnc hgen hlargeModel
  have hsmall : Nonempty (K ≃* SL(2, ZMod 5)) := by
    rcases RankActions.primePerfectSL2Recognition p hlarge K inferInstance inferInstance
      with hfull | hsmall
    · obtain ⟨k⟩ := hfull
      exact (hKt (K.eq_top_of_card_eq (Nat.card_congr k.toEquiv))).elim
    · exact hsmall.2
  let r := GorensteinWalter.sl2ProjectiveProjection (ZMod p)
  let : Group.IsSolvable r.ker := by
    rw [GorensteinWalter.sl2ProjectiveProjection_ker]
    infer_instance
  have hr := GorensteinWalter.sl2ProjectiveProjection_surjective (ZMod p)
  let E := K.map r
  have hE : E ∈ localCComponents (Sf.mapSurjective hr) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hK r
  have hEn : E ≠ ⊤ := by
    intro ht
    have hi := congrArg (Subgroup.comap r) ht
    change (K.map r).comap r = (⊤ : Subgroup PSL(2, ZMod p)).comap r at hi
    rw [comap_map_eq, GorensteinWalter.sl2ProjectiveProjection_ker, comap_top] at hi
    exact hKt (eq_top_of_sup_center_eq_top K hi)
  have htopL : (⊤ : Subgroup L).IsCComponent := by
    simpa only [subgroupOf_self] using hL.subgroupOf le_rfl
  have htopSL : (⊤ : Subgroup SL(2, ZMod p)).IsCComponent := by
    have h := cComponent_map_of_solvable_ker htopL f hf
    rwa [map_top_of_surjective f hf] at h
  have htopPSL : (⊤ : Subgroup PSL(2, ZMod p)).IsCComponent := by
    have h := cComponent_map_of_solvable_ker htopSL r hr
    rwa [map_top_of_surjective r hr] at h
  have hprojective : ClassicalGroup.IsPSL (⊤ : Subgroup PSL(2, ZMod p)) 2 p :=
    ⟨ZMod p, inferInstance, inferInstance, by simp, ⟨topEquiv⟩⟩
  have hprime := (proper_primePSL2_models (Sf.mapSurjective hr)
    hE htopPSL le_top hEn hp ho hprojective).1
  obtain ⟨k⟩ := hsmall
  let b : (B.subgroupOf L).map q ≃* K :=
    (((B.subgroupOf L).map q).equivMapOfInjective a.toMonoidHom a.injective).trans
      (MulEquiv.subgroupCongr (map_map _ _ _))
  exact .twenty_two p hprime hnc hlargeModel
    ⟨ZMod 5, inferInstance, inferInstance, by simp, ⟨b.trans k⟩⟩

/-- Apply cases (21)–(22) after the original ambient two-core quotient.
All noncentral structure inputs are derived in that actual SQTK quotient. -/
theorem twoCore_embedding_of_noncentral_fitting
    {𝒦 : GroupClass.{u}} (hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G))
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ Chapter1.L G T) (hL : L.IsCComponent) (hBL : B ≤ L)
    (hn : ¬ fittingSubgroup (L.map (QuotientGroup.mk' (pCore 2 G))) ≤
      center (L.map (QuotientGroup.mk' (pCore 2 G)))) :
    A312Embedding (B.map (QuotientGroup.mk' (pCore 2 G)))
      (L.map (QuotientGroup.mk' (pCore 2 G))) := by
  let := pCore_isNilpotent (p := 2) (G := G)
  apply embedding_of_noncentral_fitting hQ (pCore_quotient_pCore_eq_bot 2)
    (T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G)))
    ?_ (hL.map_quotient (pCore 2 G)) (map_mono hBL) hn
  simpa only [Sylow.coe_mapSurjective] using
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hB

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
