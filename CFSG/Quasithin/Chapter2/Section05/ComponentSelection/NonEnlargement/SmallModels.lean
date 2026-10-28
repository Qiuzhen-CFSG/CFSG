module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement.Source
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.C129Complete
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.SmallComponents
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
/-!
# Original small-component persistence in the source normalizer

The same original Sylow normalizes K and is Sylow in N(E). Earlier
containment supplies an ordinary containing component C with its original
2.5.2 model. Full-Sylow rigidity handles the even rank-two and Bender
models; cubic rank excludes prime-linear targets; exact small orders
exclude every remaining strict inclusion. Thus PSL₃(3) and M₁₁ persist
as ordinary components, independently of their later 2.5.15 exclusion.
Source: Aschbacher–Smith 2.5.6, printed p.554.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallPersistence
open ChapterA.Section03.OddPrime.SourceModels.SmallComponents
open ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]
private theorem prime_rank_one {F : Type*} [Field F] [Finite F]
    (hp : (Nat.card F).Prime) (hlarge : 3<Nat.card F) : primeRank 3 PSL(2,F) ≤ 1 := by
  let : Fact (3<Nat.card F) := ⟨hlarge⟩
  let P : Sylow 3 PSL(2,F) := default
  exact P.primeRank_le_one_of_isCyclic
    (GorensteinWalter.PSL2Cover.odd_sylow_cyclic_of_card_prime F hp 3 (by decide) P)


private theorem binary_three_rank (C : Type*) [Group C] [Finite C]
    (hz : IsPGroup 2 (center C)) (hm : ClassicalGroup.IsPSL (C ⧸ center C) 3 2) :
    primeRank 3 C ≤ 1 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hc : Nat.card (C ⧸ center C)=168 := by
    rw [Nat.card_congr e.toEquiv]
    have hh := Atlas.ExceptionalSupport.card_psl_mul (F:=F) 3
    norm_num [hF,Fin.prod_univ_succ] at hh
    exact hh
  rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (center C) hz]
  let P : Sylow 3 (C ⧸ center C) := default
  apply P.primeRank_le_one_of_isCyclic
  apply isCyclic_of_card_dvd_prime (p:=3)
  rw [P.card_eq_multiplicity,hc]
  decide +kernel

theorem component_in_normalizer_of_small_model
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {M H K S T E : Subgroup G} {z : G}
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀:Subgroup G)≤M)
    (hunique : ∀ N:Subgroup G, IsMaximalTwoLocal N → (T₀:Subgroup G)≤N → N=M)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (d : SourceTuple M H S T z) (hK : IsComponentIn K H) (hgen : H=K⊔S)
    (hm : Nonempty (K ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (K ≃* Sporadic.Mathieu.M11))
    (hE:E≠⊥) (hEC:E≤S⊓centralizer (K:Set G)) (hSE:S≤normalizer (E:Set G)) :
    IsComponentIn K (normalizer (E:Set G)) := by
  have hZ : IsPGroup 2 (center K) := by
    rw [small_center hm]
    exact IsPGroup.of_subsingleton _ _
  let : IsQuasisimple K := hK.quasisimple
  have hr := small_rank hm
  obtain ⟨P,C,hP,hC,hKC,hZC,⟨cC⟩,U,hUK⟩ :=
    NonEnlargement.exists_normalizing_containing_component hG localC129Input_knownSimple
      T₀ hM hT₀M hunique hempty d hK hgen hZ (by decide : Odd 3) hr hE hEC hSE
  let : IsQuasisimple C := hC.quasisimple
  let eK : K.subgroupOf C ≃* K := subgroupOfEquivOfLe hKC
  let : IsQuasisimple (K.subgroupOf C) := IsQuasisimple.of_mulEquiv eK.symm
  have hZKC : IsPGroup 2 (center (K.subgroupOf C)) := hZ.of_equiv (centerCongr eK.symm)
  have hrank : 2≤primeRank 3 (K.subgroupOf C) := by rwa [primeRank_equiv 3 eK]
  have heq : K.subgroupOf C=⊤ := by
    by_cases hb : ClassificationModels.IsBenderModel C
    · exact eq_top_of_bender (K.subgroupOf C) U hUK hb
    have hmodels := MathieuSourceSetup.nonBender_model cC hG localC129Input_knownSimple hempty hb
    rcases hmodels with hs | hl | ht | ht
    · obtain ⟨F,_,_,m,hm₀,hF,⟨e⟩⟩ := hs
      by_cases hm₁ : m=1
      · have hF₂ : Nat.card F=2 := by simpa [hm₁] using hF
        have hc : Nat.card C=360 := (Nat.card_congr
          (e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix hF₂)).toEquiv).trans
          (by rw [nat_card_alternatingGroup]; norm_num)
        have hd := card_dvd_of_le hKC
        rcases small_card hm with hk | hk <;> rw [hk,hc] at hd <;> norm_num at hd
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      have hcard : 2<Nat.card F := by
        rw [hF]
        calc 2=2^1 := by norm_num
             _<2^m := Nat.pow_lt_pow_right (by decide) (by omega)
      exact Theory.SpecificGroups.Classical.EvenRankTwoSylowRigidity.symplectic
        (K.subgroupOf C) hZKC (by decide : Odd 3) hrank U hUK hcard
        (e.trans (Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two hcard))
    · obtain ⟨F,_,_,m,hm₀,hF,⟨e⟩⟩ := hl
      by_cases hm₁ : m=1
      · have hb := binary_three_rank C hZC
          ⟨F,inferInstance,inferInstance,by simpa [hm₁] using hF,⟨e⟩⟩
        have hh := primeRank_mono 3 hKC
        omega
      exact Theory.SpecificGroups.Classical.EvenRankTwoSylowRigidity.linear
        (K.subgroupOf C) hZKC (by decide : Odd 3) hrank U hUK (n:=m) (by omega) hF e
    · have he : K=C := by
        have hd := card_dvd_of_le hKC
        apply eq_of_le_of_card_ge hKC
        rcases small_card hm with hk | hk <;> rcases small_card ht with hc | hc <;>
          rw [hk,hc] at hd ⊢ <;> norm_num at *
      rw [he,subgroupOf_self]
    · obtain ⟨r,hr,hrlarge,⟨e⟩⟩ := ht
      let : Fact r.Prime := ⟨hr.1⟩
      have hb := prime_rank_one (F:=ZMod r) (by simpa using hr.1) (by simp; omega)
      have hh := Theory.GroupTheory.primeRank_le_of_injective 3
        (e.toMonoidHom.comp (inclusion hKC)) (e.injective.comp (inclusion_injective hKC))
      omega
  have hKCeq : K=C := by
    have he := congrArg (Subgroup.map C.subtype) heq
    simpa only [map_subgroupOf_eq_of_le hKC,←MonoidHom.range_eq_map,range_subtype] using he
  simpa only [hKCeq] using hC
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallPersistence
