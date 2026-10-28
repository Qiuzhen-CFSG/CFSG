module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.Source
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.KernelNormality
public import Theory.SpecificGroups.PSL2.GraphNormalizerGeneration

/-! The companion component normalizes the actual bad overcomponent.
The source centrality of i on N_S(K) places its Sylow subgroup times t
inside R. Its intersection with R₀ is the graph subgroup used by the
proved PSL₂ involution-fixed generation theorem. Source2.5.19, p.564. -/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection OvercomponentsSource PrimeRows CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

theorem source_companion_normalizes_prime_orbit
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p)
    (eK : K ≃* PSL(2,ZMod p))
    (t i : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hi : BadInvolution ((S : Subgroup H).map H.subtype) K i)
    (hiZ : i ∈ centerIn ((S : Subgroup H).map H.subtype ⊓ normalizer (K : Set G)))
    (u : G) (hu : u ∈ (S : Subgroup H).map H.subtype)
    (hc : K ≤ centralizer (K.map (MulAut.conj u).toMonoidHom : Set G)) :
    let Gi := centralizer ({i} : Set G)
    let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
    K.map (MulAut.conj u).toMonoidHom ≤ normalizer (X.map Gi.subtype : Set G) := by
  let Y := (S : Subgroup H).map H.subtype
  let C := K.map (MulAut.conj u).toMonoidHom
  let Gi := centralizer ({i} : Set G)
  let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
  let XA := X.map Gi.subtype
  let R := (Y ⊓ centralizer (K : Set G)) ⊓ Gi
  let e : K ≃* C := (MulAut.conj u).subgroupMap K
  let : Fact p.Prime := ⟨hp.1⟩
  have hCH : C ≤ H := by
    rintro _ ⟨k,hk,rfl⟩
    exact H.mul_mem (H.mul_mem (map_subtype_le _ hu) (c.component_le hk))
      (H.inv_mem (map_subtype_le _ hu))
  have hCK : C ≤ centralizer (K : Set G) := le_centralizer_iff.mp hc
  have htH := (MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ).1
  have htCC : t ∈ centralizer (C : Set G) :=
    fun x hx => mem_centralizer_singleton_iff.mp (htH (hCH hx))
  have hzC : center C = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have he : e.symm x ∈ center K := ((centerCongr e).symm ⟨x,hx⟩).property
    rw [MathieuSourceSetup.component_center_eq_bot c hG hempty hgen,mem_bot] at he
    exact e.symm.map_eq_one_iff.mp he
  have htNotC : t ∉ C := by
    intro htmem
    have hz : (⟨t,htmem⟩ : C) ∈ center C :=
      mem_center_iff.mpr (fun x => Subtype.ext (htCC x x.property))
    rw [hzC,mem_bot] at hz
    have ht1 : t=1 := congrArg Subtype.val hz
    rw [ht1,orderOf_one] at ht
    omega
  obtain ⟨P₀,hP₀⟩ := MathieuSourceSetup.exists_relative_component_sylow c
  let P := P₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPS : (P : Subgroup C).map C.subtype ≤ Y := by
    rintro x ⟨v,⟨w,hw,rfl⟩,rfl⟩
    have hwY : (w:G)∈Y := by rw [hP₀] at hw; exact hw
    exact Y.mul_mem (Y.mul_mem hu hwY) (Y.inv_mem hu)
  have hWR : (P : Subgroup C).map C.subtype ⊔ zpowers t ≤ R := by
    apply sup_le
    · intro x hx
      have hxC : x∈C := map_subtype_le _ hx
      have hxN : x∈normalizer (K:Set G) := Subgroup.centralizer_le_normalizer _ (hCK hxC)
      exact ⟨⟨hPS hx,hCK hxC⟩,mem_centralizer_singleton_iff.mpr (hiZ.2 x ⟨hPS hx,hxN⟩)⟩
    · apply zpowers_le.mpr
      exact ⟨⟨htZ.1,fun k hk => mem_centralizer_singleton_iff.mp (htH (c.component_le hk))⟩,
        mem_centralizer_singleton_iff.mpr (htZ.2 i hi.1.1).symm⟩
  have hidx := (source_bad_prime_kernel c hG hempty hgen hb hstar hp hp7 eK
    t i ht htC htZ hi).2
  have htX : t ∉ centralizer (XA : Set G) := by
    intro htc
    obtain ⟨htI,hrows⟩ := source_bad_prime_rows c hG hempty hgen hb hstar
      hp hp7 eK t i ht htC htZ hi
    rcases hrows with ⟨hX,_,_,a,ha,hact,_,_,_⟩ |
      ⟨J,hJ,hm,hpair,_,_⟩
    · have ha1 : a = 1 := by
        apply MulEquiv.ext
        intro x
        apply Subtype.ext
        apply Subtype.ext
        have hh := htc ((x : Gi) : G) (mem_map_of_mem Gi.subtype x.property)
        have he := hact x
        rw [← hh,mul_inv_cancel_right] at he
        exact he
      rw [ha1,orderOf_one] at ha
      omega
    · let ti : Gi := ⟨t,htI⟩
      change X = J ⊔ J.map (MulAut.conj ti).toMonoidHom at hpair
      have hJC : J.map Gi.subtype ≤ XA :=
        map_mono (hpair.symm ▸ (show J ≤ J ⊔ J.map (MulAut.conj ti).toMonoidHom
          from le_sup_left))
      have htiJ : ti ∈ centralizer (J : Set Gi) := by
        intro x hx
        exact Subtype.ext (htc (x : G) (hJC (mem_map_of_mem Gi.subtype hx)))
      exact hm (mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.centralizer_le_normalizer _ htiJ)).symm
  have hpower : ∃ k, p-1=2^k ∨ p+1=2^k := by
    rcases hp.2 with ⟨k,hk⟩ | ⟨k,hk⟩
    · exact ⟨2^k,Or.inl (by omega)⟩
    · exact ⟨k,Or.inr hk⟩
  exact prime_component_normalizes_of_index_two_kernel hp7 hpower C R XA
    (e.symm.trans eK) P t ht htCC htNotC hWR hidx htX (fun j hj hj2 =>
      source_prime_kernel_centralizer_normalizes c hG hempty hgen hb hstar hp hp7 eK
        t i ht htC htZ hi j hj2 hj)
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
