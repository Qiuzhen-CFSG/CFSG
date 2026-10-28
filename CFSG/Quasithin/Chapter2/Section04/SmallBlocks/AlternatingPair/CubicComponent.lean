module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.CoverMarks
public import Theory.GroupTheory.CComponent.RankTwoResidual
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-! The original opposite block supplies a cubic centralizing the selected
A₅ block. In a component with centerless rank-two quotient and outer two-group,
the existing three-residual theorem places that same cubic inside the component.
It survives the two-core quotient, where the original block embeds faithfully.
This supplies the marked cubic-centralizer obstruction for source 2.4.25. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]
variable {M M₀ : Subgroup G} {d : MinimalBlockSetup M}

theorem AlternatingPairSourceSetup.phi_component_cubic_configuration
    (c : AlternatingPairSourceSetup d M₀)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    [IsQuasisimple D] (hz : center D = ⊥) (hr : 2 ≤ primeRank 3 D)
    (ho : IsPGroup 2 (MulAut.Outer D)) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let GI := normalizer (Phi S L : Set G)
    ∀ (K : Subgroup GI), IsComponent GI K → L.subgroupOf GI ≤ K →
    ∀ e : (K ⧸ pCore 2 K) ≃* D,
    let A := (L.subgroupOf GI).subgroupOf K
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
    IsAlternatingBlock (A.map q) 5 ∧
      Nat.card ((blockU (A.map q)).map (A.map q).subtype) = 16 ∧
      Nonempty (L ≃* A.map q) ∧
      ∃ b : D, orderOf b = 3 ∧ b ∈ centralizer (A.map q : Set D) := by
  intro S L GI K hK hLK e A q
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv e.symm
  have hzK : center (K ⧸ pCore 2 K) = ⊥ := by
    apply le_bot_iff.mp
    intro y hy
    exact e.map_eq_one_iff.mp (hz.le ((centerCongr e) ⟨y,hy⟩).property)
  have hrK : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by rwa [primeRank_congr 3 e]
  have hoK : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)) :=
    ho.of_injective (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective
  have henv := c.phi_normalizer_source hG T hM hTM hu hST hSM hMT hi
  have hLG : L ≤ GI := henv.2.2.2.1.trans (Subgroup.centralizer_le_normalizer _)
  have hres : K = primeToResidual 3 GI :=
    hK.isCComponent.eq_primeToResidual_three_of_rank_outer_two hzK hrK
      ((hG.twoLocal_sqtk henv.2.1).stronglyQuasithin 3 Nat.prime_three (by decide)) hoK
  obtain ⟨b,hb,hbL⟩ := c.phi_cubic_centralizer
  have hbK : b ∈ K := by
    rw [hres]
    exact mem_primeToResidual_of_pow (n:=1) (by simpa only [pow_one,←hb] using pow_orderOf_eq_one b)
  let k : K := ⟨b,hbK⟩
  have hk : orderOf k = 3 := (Subgroup.orderOf_coe k).symm.trans hb
  have hqk : q k ≠ 1 := by
    intro hh
    have hm : k ∈ pCore 2 K := (QuotientGroup.eq_one_iff k).mp
      (e.map_eq_one_iff.mp hh)
    have hp : (⟨k,hm⟩ : pCore 2 K)^3=1 := Subtype.ext (hk ▸ pow_orderOf_eq_one k)
    have he1 : (⟨k,hm⟩ : pCore 2 K)=1 :=
      (pCore_isPGroup.powEquiv (by decide : Nat.Coprime 2 3)).injective (by
        simpa only [IsPGroup.powEquiv_apply,one_pow] using hp)
    have hk1 : k=1 := congrArg Subtype.val he1
    simp only [hk1,orderOf_one] at hk
    omega
  let f : A →* D := q.comp A.subtype
  obtain ⟨hA₀,hcard₀,hf₀,_,_⟩ :=
    c.block_component_twoCore_quotient_marks hG T hM hTM hu hST hSM hMT hi K hK hLK
  have hfi : Function.Injective f := e.injective.comp hf₀
  have hrange : f.range = A.map q := by
    rw [MonoidHom.range_comp]
    simp only [Subgroup.range_subtype]
  let a : A ≃* L := (subgroupOfEquivOfLe hLK).trans (subgroupOfEquivOfLe hLG)
  let af : A ≃* A.map q := (MonoidHom.ofInjective hfi).trans (MulEquiv.subgroupCongr hrange)
  let eL : L ≃* A.map q := a.symm.trans af
  have hA : IsAlternatingBlock (A.map q) 5 :=
    RankOne.Solvable.isAlternatingBlock_of_equiv af hA₀
  have hcard : Nat.card ((blockU (A.map q)).map (A.map q).subtype) = 16 := by
    rw [card_map_of_injective (A.map q).subtype_injective,
      ←RankOne.Solvable.blockU_map_equiv af,
      card_map_of_injective af.injective,
      ←card_map_of_injective A.subtype_injective]
    exact hcard₀
  refine ⟨hA,hcard,⟨eL⟩,q k,?_,?_⟩
  · exact (Nat.dvd_prime Nat.prime_three).mp (hk ▸ orderOf_map_dvd q k) |>.resolve_left
      (fun he => hqk (orderOf_eq_one_iff.mp he))
  · rintro y ⟨l,hl,rfl⟩
    have hc : l*k=k*l := Subtype.ext (hbL (l:GI) hl)
    simpa only [map_mul] using congrArg q hc

theorem AlternatingPairSourceSetup.cubic_centralizer_overcomponent_false
    (c : AlternatingPairSourceSetup d M₀)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    [IsQuasisimple D] (hz : center D = ⊥) (hr : 2 ≤ primeRank 3 D)
    (ho : IsPGroup 2 (MulAut.Outer D))
    (hno : ∀ E : Subgroup D, IsElementaryAbelian 2 E → Nat.card E = 16 →
      ∀ b : D, orderOf b = 3 → E ≤ centralizer ({b} : Set D) → False) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let GI := normalizer (Phi S L : Set G)
    ∀ (K : Subgroup GI), IsComponent GI K → L.subgroupOf GI ≤ K →
      Nonempty ((K ⧸ pCore 2 K) ≃* D) → False := by
  intro S L GI K hK hLK ⟨e⟩
  obtain ⟨hA,hcard,_,b,hb,hbA⟩ :=
    c.phi_component_cubic_configuration hG T hM hTM hu hST hSM hMT hi hz hr ho K hK hLK e
  let A := ((L.subgroupOf GI).subgroupOf K).map
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))
  let U := (blockU A).map A.subtype
  let : IsElementaryAbelian 2 U := hA.2.1.elementary.map A.subtype
  exact hno U inferInstance hcard b hb (fun u hu =>
    mem_centralizer_singleton_iff.mpr (hbA u (map_subtype_le _ hu)))

end CFSG.Quasithin.Chapter2
