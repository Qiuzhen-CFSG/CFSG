module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootCentralizerFactorization

/-!
# Simultaneous placement of the actual opposite roots

Place the first root and original whole Cartan in a full-core complement.
The retained Cartan-centralizing conjugator places the second root. Pull
that root back into the complement, then factor the conjugator through the
two actual root centralizers. The first factor preserves the first root
and gives the same placement of the second root.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceOppositeRootComplement
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85.OriginalExtension
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR

/-- The same original whole Cartan and both actual opposite root subgroups
are contained simultaneously in a complement to the full H-core. -/
theorem source_opposite_root_cartan_complement
    (c : CompatibleCartans ![locals T M Mc H 1,locals T M Mc H 0]
      (reducedSylow ![locals T M Mc H 1,locals T M Mc H 0] (T : Subgroup G)))
    (R S : Subgroup G) (hRH : R≤H) (hSH : S≤H)
    (hR : IsPGroup 2 R) (hS : IsPGroup 2 S) (hR8 : Nat.card R=8) (hS8 : Nat.card S=8)
    (hkR : Disjoint R (H.pCoreIn 2)) (hkS : Disjoint S (H.pCoreIn 2))
    (hCR : c.D 0 ⊔ c.D 1≤normalizer (R:Set G))
    (hCS : c.D 0 ⊔ c.D 1≤normalizer (S:Set G))
    (hne : (R.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))≠
      (S.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) :
    ∃ K : Subgroup H, (pCore 2 H).IsComplement' K ∧
      c.D 0 ⊔ c.D 1≤K.map H.subtype ∧ R≤K.map H.subtype ∧ S≤K.map H.subtype ∧
      ∃ f : K ≃* Theory.PSL2.BinaryGroup 3,
        ∀ k:K,f k=(sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR)
          (QuotientGroup.mk' (pCore 2 H) (k:H)) := by
  classical
  obtain ⟨K,hK,hCK,hRK,_,_⟩ := SourceRootCartanComplement.source_root_cartan_complement
    hG T hempty hM hu hmany hcard e H hH eR c R hRH hR hR8 hkR hCR
  let C := c.D 0 ⊔ c.D 1
  have hCH : C≤H := hCK.trans (map_subtype_le K)
  have hC7 : Nat.card C=7 := by
    have hc := SourceCartan.source_cartan_order hG T hempty hM hu hmany hcard e H hH eR c
    rw [cartan,card_map_of_injective middleMap_injective,
      Nat.card_congr (subgroupOfEquivOfLe c.joint_le).toEquiv] at hc
    exact hc
  let A := C.subgroupOf H
  have hAK : A≤K := by
    intro a ha
    obtain ⟨k,hk,he⟩ := hCK ha
    exact (Subtype.ext he : k=a) ▸ hk
  have hA7 : Nat.card A=7 := (Nat.card_congr (subgroupOfEquivOfLe hCH).toEquiv).trans hC7
  let S₁ := S.subgroupOf H
  have hS₁ : IsPGroup 2 S₁ := hS.of_equiv (subgroupOfEquivOfLe hSH).symm
  have hS₁8 : Nat.card S₁=8 := (Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv).trans hS8
  have hkS₁ : Disjoint S₁ (pCore 2 H) := by
    apply disjoint_def.mpr
    intro s hs hq
    exact Subtype.ext (hkS.le_bot ⟨hs,mem_map_of_mem H.subtype hq⟩)
  have hAS₁ : A≤normalizer (S₁:Set H) := fun a ha => S.le_normalizer_comap H.subtype (hCS ha)
  obtain ⟨v,hv,hSv⟩ := SourceRootCartanComplement.source_seven_root_conjugator
    hG T hempty hM hu hmany hcard e H hH eR K hK A S₁ hAK hA7 hS₁ hS₁8 hkS₁ hAS₁
  have hvQ : (v:G)∈H.pCoreIn 2 := mem_map_of_mem H.subtype hv.1
  have hvC : (v:G)∈centralizer (C:Set G) := by
    intro x hx
    exact congrArg Subtype.val (hv.2 (⟨x,hCH hx⟩:H) hx)
  let S₀ := S.map (MulAut.conj (v:G)⁻¹).toMonoidHom
  have hS₀H : S₀≤H := by
    rintro x ⟨s,hs,rfl⟩
    exact H.mul_mem (H.mul_mem (H.inv_mem v.property) (hSH hs)) (H.inv_mem (H.inv_mem v.property))
  have hS₀K : S₀≤K.map H.subtype := by
    rintro x ⟨s,hs,rfl⟩
    obtain ⟨k,hk,he⟩ := hSv (show (⟨s,hSH hs⟩:H)∈S₁ from hs)
    have hh := congrArg Subtype.val he
    change (v:G)*(k:G)*(v:G)⁻¹=s at hh
    refine ⟨k,hk,?_⟩
    change (k:G)=(v:G)⁻¹*s*((v:G)⁻¹)⁻¹
    rw [←hh]
    group
  have hS₀ : IsPGroup 2 S₀ := hS.map (MulAut.conj (v:G)⁻¹).toMonoidHom
  have hS₀8 : Nat.card S₀=8 := (card_map_of_injective (MulAut.conj (v:G)⁻¹).injective).trans hS8
  have hkS₀ : Disjoint S₀ (H.pCoreIn 2) := by
    have hh := disjoint_map (f:=(MulAut.conj (v:G)⁻¹).toMonoidHom)
      (MulAut.conj (v:G)⁻¹).injective hkS
    have hn : (H.pCoreIn 2).map (MulAut.conj (v:G)⁻¹).toMonoidHom=H.pCoreIn 2 :=
      mem_normalizer_iff_map_conj_eq.mp
        ((H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
          (H.inv_mem v.property))
    rwa [hn] at hh
  have hCS₀ : C≤normalizer (S₀:Set G) := by
    have hh := (map_mono (f:=(MulAut.conj (v:G)⁻¹).toMonoidHom) hCS).trans
      (S.le_normalizer_map (MulAut.conj (v:G)⁻¹).toMonoidHom)
    have he : C.map (MulAut.conj (v:G)⁻¹).toMonoidHom=C :=
      mem_normalizer_iff_map_conj_eq.mp (centralizer_le_normalizer (C:Set G)
        ((centralizer (C:Set G)).inv_mem hvC))
    rwa [he] at hh
  let π := QuotientGroup.mk' (pCore 2 H)
  have hvπ : π v=1 := (QuotientGroup.eq_one_iff v).mpr hv.1
  have hS₀π : (S₀.subgroupOf H).map π=(S.subgroupOf H).map π := by
    apply le_antisymm
    · rintro z ⟨x,hx,rfl⟩
      obtain ⟨s,hs,he⟩ := hx
      let sH : H := ⟨s,hSH hs⟩
      have hx' : x=v⁻¹*sH*v := by
        apply Subtype.ext
        change (x:G)=(v:G)⁻¹*s*(v:G)
        change (v:G)⁻¹*s*((v:G)⁻¹)⁻¹=(x:G) at he
        simpa only [inv_inv] using he.symm
      exact ⟨sH,hs,by rw [hx',map_mul,map_mul,map_inv,hvπ,inv_one,one_mul,mul_one]⟩
    · rintro z ⟨s,hs,rfl⟩
      let x : H := v⁻¹*s*v
      have hx : x∈S₀.subgroupOf H := by
        refine ⟨s,hs,?_⟩
        change (v:G)⁻¹*(s:G)*((v:G)⁻¹)⁻¹=(v:G)⁻¹*(s:G)*(v:G)
        rw [inv_inv]
      exact ⟨x,hx,by change π (v⁻¹*s*v)=π s; rw [map_mul,map_mul,map_inv,hvπ,inv_one,one_mul,mul_one]⟩
  obtain ⟨a,ha,b,hb,hab⟩ := SourceRootCentralizerFactorization.source_two_root_core_factorization
    hG T hempty hM hu hmany hcard e H hH eR C R S₀ hCH hRH hS₀H hC7 hR hS₀ hR8 hS₀8
    hkR hkS₀ hCR hCS₀ (by rwa [hS₀π]) v ⟨hvQ,hvC⟩
  let aH : H := ⟨a,(pCoreIn_le 2 H) ha.1.1⟩
  let K' := K.map (MulAut.conj aH).toMonoidHom
  have hK' : (pCore 2 H).IsComplement' K' := by
    apply isComplement'_of_card_mul_and_disjoint
    · rw [card_map_of_injective (MulAut.conj aH).injective]
      exact hK.card_mul_card
    · have hh := disjoint_map (f:=(MulAut.conj aH).toMonoidHom) (MulAut.conj aH).injective hK.disjoint
      have hn : (pCore 2 H).map (MulAut.conj aH).toMonoidHom=pCore 2 H :=
        Subgroup.Normal.map_conj_eq (pCore 2 H) aH
      rwa [hn] at hh
  have hfix (B : Subgroup G) (hBK : B≤K.map H.subtype) (haB : a∈centralizer (B:Set G)) :
      B≤K'.map H.subtype := by
    intro x hx
    obtain ⟨k,hk,he⟩ := hBK hx
    refine ⟨MulAut.conj aH k,⟨k,hk,rfl⟩,?_⟩
    change a*(k:G)*a⁻¹=x
    change (k:G)=x at he
    rw [he,←haB x hx,mul_inv_cancel_right]
  have hSK' : S≤K'.map H.subtype := by
    intro s hs
    let x := (v:G)⁻¹*s*(v:G)
    have hx : x∈S₀ := ⟨s,hs,by change (v:G)⁻¹*s*((v:G)⁻¹)⁻¹=x; rw [inv_inv]⟩
    obtain ⟨k,hk,hek⟩ := hS₀K hx
    refine ⟨MulAut.conj aH k,⟨k,hk,rfl⟩,?_⟩
    have hbX : x*b=b*x := hb.2 x hx
    change a*(k:G)*a⁻¹=s
    change (k:G)=x at hek
    rw [hek]
    have hsx : s=(v:G)*x*(v:G)⁻¹ := by dsimp only [x]; group
    rw [hsx,hab]
    calc
      a*x*a⁻¹=a*(b*x*b⁻¹)*a⁻¹ := by rw [←hbX,mul_inv_cancel_right]
      _=(a*b)*x*(a*b)⁻¹ := by group
  let ε := sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR
  let f := hK'.symm.QuotientMulEquiv.symm.trans ε
  refine ⟨K',hK',hfix C hCK ha.1.2,hfix R hRK ha.2,hSK',f,?_⟩
  intro k
  apply congrArg ε
  change hK'.symm.QuotientMulEquiv.symm k=π (k:H)
  apply hK'.symm.QuotientMulEquiv.injective
  rw [MulEquiv.apply_symm_apply,quotientMulEquiv_mk_apply_of_isComplement']

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceOppositeRootComplement
