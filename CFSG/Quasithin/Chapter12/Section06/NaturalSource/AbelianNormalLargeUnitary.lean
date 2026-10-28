module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalUnitaryBorel
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.UnitaryLargeBorelField
public import Theory.GroupTheory.NormalizerQuotientInner
public import Theory.GroupTheory.PPerfectHom
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalUnitaryField
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank
public import Theory.GroupTheory.PrimeRankCentralizer
/-!
# Excluding the original large odd-degree unitary component

Apply ninth-power field rigidity to the literal K/O₂(K) quotient. The
image of the original T supplies the two-group of actors and contains
the inner image of T intersect K. Cubic displacement is supplied by
the original marked Borel with its full intrinsic two-core. The identity
L₁=[L₁,T intersect L] puts the component-action image in a two-group,
and two-perfectness kills it. In odd degree the centerless component
has full ambient three-rank; its centralizer cannot contain the surviving
original elementary nine. Combined with the even-degree exclusion, the
normal projective-unitary parameter is therefore three.

Source: Aschbacher--Smith 12.6.31, printed pp.836--837.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H)

include hz hTV hTz hbound hTI hns hH hKH in
/-- Above degree three, the original T intersect L acts on K/O₂(K) by root inner automorphisms. -/
theorem SourceHypothesis.original_abelian_normal_unitaryLarge_root_inner
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L)
    {n : ℕ} (hn3 : 3 < n)
    (hm : ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2 ^ n)) :
    ∃ hnK : (T : Subgroup G) ≤ normalizer (K : Set G),
      ∀ s : ((T : Subgroup G) ⊓ L : Subgroup G),
        quotientAut (pCore 2 K) (K.normalizerMonoidHom ⟨s,hnK s.property.1⟩) ∈
          (((T : Subgroup G).subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))).map
            MulAut.conj := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨P,hP,hB,_,hnB,_⟩ := S.original_abelian_normal_unitaryThree_borel
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hout hn2 hm
  let B := K ⊓ M L
  let N := normalizer (P : Set K)
  let e : N ≃* B := (N.equivMapOfInjective K.subtype K.subtype_injective).trans
    (MulEquiv.subgroupCongr hB)
  have hPK : (P : Subgroup K) = (T : Subgroup G).subgroupOf K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [hP,subgroupOf_map_subtype]
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hTH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn)
  obtain ⟨hnBT,hodd,hcube⟩ := S.original_abelian_normal_unitaryThree_borel_torus_action
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hout hn2 hm
  have hcore := S.original_abelian_normal_unitaryThree_borel_core
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hout hn2 hm
  obtain ⟨F,hF,hfin,J,hcardF,hconj,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let X := BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J
  let q : K →* X := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker ≤ (P : Subgroup K) := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  let f : (T : Subgroup G) →* MulAut X :=
    (MulAut.congr eK).toMonoidHom.comp
      ((quotientAut (pCore 2 K)).comp (K.normalizerMonoidHom.comp (inclusion hTK)))
  let A := f.range
  have hA : IsPGroup 2 A := T.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hPA : ((P : Subgroup K).map q).map MulAut.conj ≤ A := by
    rintro _ ⟨x,⟨k,hkP,rfl⟩,rfl⟩
    have hkT : (k : G) ∈ (T : Subgroup G) := by rw [hPK] at hkP; exact hkP
    refine ⟨⟨k,hkT⟩,?_⟩
    change MulAut.congr eK (quotientAut (pCore 2 K)
      (K.normalizerMonoidHom ⟨k,hTK hkT⟩)) = MulAut.conj (q k)
    rw [show quotientAut (pCore 2 K) (K.normalizerMonoidHom ⟨k,hTK hkT⟩) =
      MulAut.conj (QuotientGroup.mk' (pCore 2 K) k) from
      normalizerQuotientAction_inner K (pCore 2 K) k]
    exact MulAut.congr_conj eK _
  refine ⟨hTK,?_⟩
  intro s'
  let s : G := s'.val
  have hs : s ∈ (T : Subgroup G) ⊓ L := s'.property
  let α := K.normalizerMonoidHom ⟨s,hTK hs.1⟩
  let β := MulAut.congr eK (quotientAut (pCore 2 K) α)
  have heq (x : K) : q (α x) = β (q x) := by
    change eK (QuotientGroup.mk' _ (α x)) =
      eK (quotientAut (pCore 2 K) α (eK.symm (eK (QuotientGroup.mk' _ x))))
    rw [eK.symm_apply_apply,quotientAut_apply_mk]
  have hαP : (P : Subgroup K).map α.toMonoidHom = P := by
    rw [hPK]
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      change s * (x : G) * s⁻¹ ∈ (T : Subgroup G)
      exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem hs.1 hx)
        ((T : Subgroup G).inv_mem hs.1)
    · intro x hx
      refine ⟨α.symm x,?_,α.apply_symm_apply x⟩
      have hi : α.symm = K.normalizerMonoidHom ⟨s⁻¹,(normalizer (K : Set G)).inv_mem (hTK hs.1)⟩ := by
        exact (map_inv K.normalizerMonoidHom ⟨s,hTK hs.1⟩).symm
      rw [hi]
      change s⁻¹ * (x : G) * s⁻¹⁻¹ ∈ (T : Subgroup G)
      rw [inv_inv]
      exact (T : Subgroup G).mul_mem
        ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem hs.1) hx) hs.1
  have hc (x : K) (hx : x ∈ normalizer (P : Set K)) :
      (α x * x⁻¹)^3 ∈ (P : Subgroup K) := by
    let b' : B := e ⟨x,hx⟩
    let aB := B.normalizerMonoidHom ⟨s,hnBT hs.1⟩
    have hh := hcube ⟨s,hs⟩ b'
    have hzq : QuotientGroup.mk' (pCore 2 B) ((aB b' * b'⁻¹)^3) = 1 := by
      simpa only [map_pow,map_mul,map_inv] using hh
    have hmem := (QuotientGroup.eq_one_iff _).mp hzq
    have him := mem_map_of_mem B.subtype hmem
    change ((aB b' * b'⁻¹)^3 : B).val ∈ B.pCoreIn 2 at him
    rw [hcore] at him
    rw [hPK]
    exact him.1
  have hstep := UnitaryBorelField.large_normalizer_actor_mem_root_inner J hn3
    hcardF hconj q hq P hk A hA hPA α β
    (show β ∈ A from ⟨⟨s,hs.1⟩,rfl⟩) heq hαP hc
  obtain ⟨x,⟨k,hkP,rfl⟩,hkβ⟩ := hstep
  refine ⟨QuotientGroup.mk' (pCore 2 K) k,⟨k,hPK ▸ hkP,rfl⟩,?_⟩
  apply (MulAut.congr eK).injective
  exact (MulAut.congr_conj eK _).trans hkβ
include hz hTV hTz hbound hTI hns hH hKH in
/-- The original two-perfect residual centralizes the large unitary component
modulo its full intrinsic two-core. -/
theorem SourceHypothesis.original_abelian_normal_unitaryLarge_commutator_core
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L)
    {n : ℕ} (hn3 : 3 < n)
    (hm : ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2 ^ n)) :
    ⁅(D.fullSetup hZ T z).L₁,K⁆ ≤ K.pCoreIn 2 := by
  let E := D.fullSetup hZ T z
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hnK : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hn
  let A := E.L₁.subgroupOf H
  let U := ((T : Subgroup G) ⊓ L : Subgroup G).subgroupOf H
  let R := ((T : Subgroup G) ⊓ K : Subgroup G).subgroupOf H
  let f : H →* MulAut (K ⧸ pCore 2 K) :=
    (normalizerQuotientAction K (pCore 2 K)).comp (inclusion hnK)
  obtain ⟨hnT,hi⟩ := S.original_abelian_normal_unitaryLarge_root_inner
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hout hn3 hm
  have hUi : U.map f ≤ R.map f := by
    rintro _ ⟨s,hs,rfl⟩
    obtain ⟨x,⟨k,hkT,rfl⟩,hk⟩ := hi ⟨s,hs⟩
    refine ⟨⟨k,hKH k.property⟩,⟨hkT,k.property⟩,?_⟩
    change normalizerQuotientAction K (pCore 2 K) ⟨k,hnK (hKH k.property)⟩ = _
    rw [normalizerQuotientAction_inner K (pCore 2 K) k]
    exact hk
  obtain ⟨_,_,_,_,hnB,_⟩ := S.original_abelian_normal_unitaryThree_borel
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hout (by omega) hm
  have hcore := S.original_abelian_normal_unitaryThree_borel_core
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hout (by omega) hm
  have hLR : E.L₁ ≤ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
    rw [←hcore]
    exact (le_sup_left.trans hnB).trans
      (normalizer_le_normalizer_characteristic_image (K ⊓ M L) (pCore 2 (K ⊓ M L : Subgroup G)))
  have hAR : A ≤ normalizer (R : Set H) := by
    intro a ha
    exact (((T : Subgroup G) ⊓ K : Subgroup G).le_normalizer_comap H.subtype) (hLR ha)
  have hfull : ⁅A,U⁆ = A := by
    rw [←SubgroupTransport.subgroupOf_commutator _ _ hLH (inf_le_left.trans hTH),
      S.original_point_residual_full_commutator D hZ z hz hTz]
  have hARf : A.map f ≤ normalizer (R.map f : Set (MulAut (K ⧸ pCore 2 K))) :=
    (map_mono hAR).trans (R.le_normalizer_map f)
  have hAf : A.map f ≤ R.map f := by
    calc
      A.map f = ⁅A.map f,U.map f⁆ := by rw [←map_commutator,hfull]
      _ ≤ ⁅A.map f,R.map f⁆ := commutator_mono le_rfl hUi
      _ ≤ R.map f := le_normalizer_iff_commutator_le_right.mp hARf
  have hAp : IsPPerfect 2 A :=
    (isPPerfect_embedded_pResidual 2 (L ⊓ E.Gz)).of_surjective
      (subgroupOfEquivOfLe hLH).symm.toMonoidHom (subgroupOfEquivOfLe hLH).symm.surjective
  have hRp : IsPGroup 2 (R.map f) :=
    ((T.isPGroup'.to_le (show (T : Subgroup G) ⊓ K ≤ T from inf_le_left)).comap_subtype).map f
  let g : A →* R.map f := (f.comp A.subtype).codRestrict _ (fun a => hAf (mem_map_of_mem f a.property))
  have hg := hAp.hom_eq_one_of_isPGroup hRp g
  have hf (a : A) : f a = 1 := congrArg Subtype.val (DFunLike.congr_fun hg a)
  apply commutator_le.mpr
  intro a ha k hk
  let aH : A := ⟨⟨a,hLH ha⟩,ha⟩
  let kK : K := ⟨k,hk⟩
  let α := K.normalizerMonoidHom ⟨a,hnK (hLH ha)⟩
  have he : QuotientGroup.mk' (pCore 2 K) (α kK) =
      QuotientGroup.mk' (pCore 2 K) kK := by
    have hh := congrArg (fun b : MulAut (K ⧸ pCore 2 K) => b (QuotientGroup.mk' (pCore 2 K) kK)) (hf aH)
    change quotientAut (pCore 2 K) α (QuotientGroup.mk' (pCore 2 K) kK) = _ at hh
    rwa [quotientAut_apply_mk] at hh
  have hm : α kK * kK⁻¹ ∈ pCore 2 K := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 K) (α kK * kK⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  exact mem_map_of_mem K.subtype hm

include hz hTV hTz hbound hTI hns hH hKH in
/-- Centralization survives in the original ambient quotient. -/
theorem SourceHypothesis.original_abelian_normal_unitaryLarge_star_centralizes
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L)
    {n : ℕ} (hn3 : 3 < n)
    (hm : ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2 ^ n)) :
    actorImage H (D.fullSetup hZ T z).L₁ ≤
      centralizer (actorImage H K : Set (H ⧸ pCore 2 H)) := by
  have hLH : (D.fullSetup hZ T z).L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hnK : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hn
  have hc := (S.original_abelian_normal_unitaryLarge_commutator_core
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hout hn3 hm).trans
    (pCoreIn_mono_of_normalizes hKH hnK)
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  unfold actorImage
  rw [←map_commutator,←SubgroupTransport.subgroupOf_commutator _ _ hLH hKH]
  apply le_of_eq
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [QuotientGroup.ker_mk']
  have hh := comap_mono (f := H.subtype) hc
  have he : (H.pCoreIn 2).subgroupOf H = pCore 2 H :=
    comap_map_eq_self_of_injective H.subtype_injective _
  exact hh.trans he.le

variable (hK : (K.subgroupOf H).IsCComponent)

include hz hTV hTz hbound hTI hns hH hKH hK in
/-- The original normal projective unitary component has no odd parameter
above three: its surviving E₉ would centralize a centerless component of full three-rank. -/
theorem SourceHypothesis.original_abelian_normal_unitaryLarge_odd_excluded
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L)
    {n : ℕ} (hn3 : 3 < n) (hodd : Odd n)
    (hm : ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2 ^ n)) : False := by
  let E := D.fullSetup hZ T z
  let B := actorImage H K
  have hc := S.original_abelian_normal_unitaryLarge_star_centralizes
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hout hn3 hm
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let e : B ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J :=
    (componentStarEquiv H K hKH hK).symm.trans eK
  have hzB : center B = ⊥ := by
    apply bot_unique
    intro x hx
    have hzJ := BenderSuzuki.MatrixGroups.HermitianForm.EvenProjectiveComparison.center_eq_bot
      J (by omega : 0 < n) hcard hconj
    exact mem_bot.mpr (e.map_eq_one_iff.mp
      (mem_bot.mp (hzJ ▸ ((centerCongr e) ⟨x,hx⟩).property)))
  have hr := S.original_star_three_rank D hZ z hz hH
  have hrB : primeRank 3 B = 2 := by
    apply le_antisymm ((primeRank_subgroup_le 3 B).trans hr)
    rw [primeRank_equiv 3 e]
    exact Theory.SpecificGroups.SignedThreeCubicRank.unitary_projective
      J (by omega) hcard hconj hodd
  let P : Sylow 3 E.L₁ := Classical.choice inferInstance
  let P₀ := (P : Subgroup E.L₁).map E.L₁.subtype
  have hP := S.original_point_sylow_star D hZ z hz hTz hH P
  have hcardP : Nat.card (actorImage H P₀) = 9 := hP.2.1
  have hPA : actorImage H P₀ ≤ actorImage H E.L₁ := map_mono (comap_mono (map_subtype_le _))
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := actorImage H P₀) 3
    (by rw [hcardP]; decide)
  have hpow : (x : H ⧸ pCore 2 H)^3 = 1 :=
    congrArg Subtype.val ((orderOf_eq_prime_iff.mp hx).1)
  have hxc := hc (hPA x.property)
  have hxB : (x : H ⧸ pCore 2 H) ∈ B :=
    mem_of_prime_pow_eq_one_of_centralizes_rank_two hr B hrB hpow hxc
  have hzx : (⟨x,hxB⟩ : B) ∈ center B := by
    rw [mem_center_iff]
    intro b
    exact Subtype.ext (hxc b b.property)
  have hzx1 : (⟨x,hxB⟩ : B) = 1 := by
    rw [hzB] at hzx
    exact mem_bot.mp hzx
  have he : (x : H ⧸ pCore 2 H) = 1 := congrArg Subtype.val hzx1
  exact (orderOf_eq_prime_iff.mp hx).2 (Subtype.ext he)

variable (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- In the original normal PSU₃ row, only the degree-three parameter
survives the even-degree and large odd-degree exclusions. -/
theorem SourceHypothesis.original_abelian_normal_unitaryThree_degree_eq_three
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L)
    {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2 ^ n)) : n = 3 := by
  have ho := S.original_abelian_normal_unitaryThree_odd D hZ z hz hTV hTz hbound hTI hns
    hH hKH hK hgen hn hout hn2 hm
  have hnle : n ≤ 3 := by
    by_contra h
    exact S.original_abelian_normal_unitaryLarge_odd_excluded D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hn hout (by omega) ho hm
  have hh := Nat.odd_iff.mp ho
  omega

end CFSG.Quasithin.Chapter12.Section06
