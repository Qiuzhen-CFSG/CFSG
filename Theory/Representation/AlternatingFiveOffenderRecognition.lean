module
public import Theory.Representation.AlternatingFiveQuotientDisplacement
public import Theory.SpecificGroups.AlternatingFiveSolvableSylow
public import Theory.Representation.BinaryOffender.ConjugateSubgroupSaturation
public import Theory.Representation.BinaryOffender.MarkedCentralQuotient
public import Theory.Representation.BinaryOffender.FixedQuotientKernel
public import Theory.Representation.BinaryFourOddKernel
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
/-!
# Recognition of an offender above alternating five

An offender of order at most four cannot have order two, since a quotient-visible
involution moves at least two binary dimensions. Two conjugates of its full
four-group image generate A5; Frattini nongeneration lifts this to the acting
group. Their fixed-space codimensions bound the global fixed quotient by four.
The quotient action remains faithful because its kernel is a two-group and the
original odd-by-A5 actor has trivial two-core. Finally the degree-four perfect
binary action excludes the odd nilpotent kernel.

The original group need not be perfect: the consumer applies this theorem to
its faithful action image after the minimal-parabolic kernel reduction.
Source: Niles, Pushing-up in finite groups (1979), Lemma2.8, pp.32–33.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open Theory.PSL2.SylowFixedQuotients
namespace Representation.AlternatingFiveOffenderRecognition
local notation "A5" => alternatingGroup (Fin 5)
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

theorem offender_card_four
    (ρ:Representation (ZMod 2) G W) (hf:Function.Injective ρ)
    (q:G→*A5) (hs:Function.Surjective q) (P:Subgroup G)
    (hc:Nat.card P=2 ∨ Nat.card P=4)
    (hm:Nat.card (P.map q)=Nat.card P)
    (hd:fixedCodim ρ P≤Nat.log 2 (Nat.card P)) : Nat.card P=4 := by
  rcases hc with hc | hc
  · let : IsCyclic P := isCyclic_of_prime_card hc
    obtain ⟨a,ha⟩ := P.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
    have hqa : orderOf (q a)=2 := by
      rw [←Nat.card_zpowers, ←MonoidHom.map_zpowers,ha,hm,hc]
    have hlo := displacement_ge_two_of_alternating_five_quotient ρ hf q hs a hqa
    rw [ha] at hlo
    have hlog : Nat.log 2 (Nat.card P)=1 := by rw [hc]; decide
    omega
  · exact hc

private theorem card_five : Nat.card A5=60 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem exists_sylow_conjugate (S:Sylow 2 A5) :
    ∃ g:A5, (S:Subgroup A5) ⊔ (S:Subgroup A5).map (MulAut.conj g).toMonoidHom=⊤ := by
  let : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
  have hN : normalizer (S:Set A5)≠⊤ := by
    intro htop
    let : (S:Subgroup A5).Normal := normalizer_eq_top_iff.mp htop
    rcases (inferInstance : (S:Subgroup A5).Normal).eq_bot_or_eq_top with he | he
    · have hh := alternating_sylow_card S
      rw [he] at hh
      simp at hh
    · have hh := alternating_sylow_card S
      rw [he, Nat.card_congr (topEquiv:(⊤:Subgroup A5)≃*A5).toEquiv,card_five] at hh
      norm_num at hh
  obtain ⟨g,hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hN)
  refine ⟨g,?_⟩
  by_contra hn
  let Q:Sylow 2 A5 := g • S
  have hQ : (Q:Subgroup A5)=(S:Subgroup A5).map (MulAut.conj g).toMonoidHom := rfl
  have hle := alternatingGroup.proper_sylow_overgroup_le_normalizer S _ hn le_sup_left
  have hQN : (Q:Subgroup A5)≤normalizer (S:Set A5) := by rw [hQ]; exact le_sup_right.trans hle
  have hQS : (Q:Subgroup A5)≤(S:Subgroup A5) := by
    have hh := Q.isPGroup'.inf_normalizer_sylow S
    rw [inf_eq_left.mpr hQN] at hh
    exact inf_eq_left.mp hh.symm
  have he:Q=S := Sylow.ext (Q.is_maximal' S.isPGroup' hQS).symm
  exact hg.2 (Sylow.smul_eq_iff_mem_normalizer.mp he)

theorem conjugate_generation
    (q:G→*A5) (hs:Function.Surjective q) (hk:q.ker≤frattini G)
    (P:Subgroup G) (hP:IsPGroup 2 P) (hc:Nat.card (P.map q)=4) :
    ∃g:G,P⊔P.map (MulAut.conj g).toMonoidHom=⊤ := by
  obtain ⟨S,hS⟩ := (hP.map q).exists_le_sylow
  have hPS : P.map q=(S:Subgroup A5) :=
    eq_of_le_of_card_ge hS (by rw [hc,alternating_sylow_card])
  obtain ⟨b,hb⟩ := exists_sylow_conjugate S
  obtain ⟨g,rfl⟩ := hs b
  refine ⟨g,?_⟩
  have he : (P.map (MulAut.conj g).toMonoidHom).map q =
      (P.map q).map (MulAut.conj (q g)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro a
    change q (g*a*g⁻¹)=q g*q a*(q g)⁻¹
    simp only [map_mul,map_inv]
  have hmap : (P⊔P.map (MulAut.conj g).toMonoidHom).map q=⊤ := by
    rw [Subgroup.map_sup,he,hPS]
    exact hb
  have hsup : (P⊔P.map (MulAut.conj g).toMonoidHom)⊔q.ker=⊤ := by
    have hh := congrArg (fun T:Subgroup A5=>T.comap q) hmap
    rwa [comap_map_eq,comap_top] at hh
  apply frattini_nongenerating
  apply top_unique
  rw [←hsup]
  exact sup_le_sup_left hk _

omit [Finite G] in
theorem fixed_quotient_degree_le_four
    (ρ:Representation (ZMod 2) G W) (P:Subgroup G) (g:G)
    (hg:P⊔P.map (MulAut.conj g).toMonoidHom=⊤)
    (hd:fixedCodim ρ P≤2) : fixedCodim ρ ⊤≤4 := by
  let c:Fin 2→G := ![1,g]
  have h1 : (MulAut.conj (1:G)).toMonoidHom=MonoidHom.id G := by
    apply MonoidHom.ext
    intro a
    change 1*a*1⁻¹=a
    simp
  have hgen : (⊤:Subgroup G)≤⨆i,P.map (MulAut.conj (c i)).toMonoidHom := by
    rw [←hg]
    apply sup_le
    · simpa only [c,Matrix.cons_val_zero,h1,map_id] using
        (le_iSup (fun i:Fin 2=>P.map (MulAut.conj (c i)).toMonoidHom) 0)
    · exact le_iSup (fun i:Fin 2=>P.map (MulAut.conj (c i)).toMonoidHom) 1
  have hb := fixedCodim_le_card_mul_of_subgroup_conjugates ρ ⊤ P c hgen
  simp only [Fintype.card_fin] at hb
  omega

theorem two_core_eq_bot
    (q:G→*A5) (hs:Function.Surjective q) (ho:Odd (Nat.card q.ker)) : pCore 2 G=⊥ := by
  let : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
  let : ((pCore 2 G).map q).Normal := (inferInstance : (pCore 2 G).Normal).map q hs
  have hle : pCore 2 G≤q.ker := by
    apply (Subgroup.map_eq_bot_iff _).mp
    rcases (inferInstance : ((pCore 2 G).map q).Normal).eq_bot_or_eq_top with he | he
    · exact he
    · have hp : IsPGroup 2 ((pCore 2 G).map q) := pCore_isPGroup.map q
      obtain ⟨n,hn⟩ := hp.exists_card_eq
      have hdiv : 5 ∣ 2^n := by
        rw [←hn,he,Nat.card_congr (topEquiv:(⊤:Subgroup A5)≃*A5).toEquiv,card_five]
        decide
      have : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide) hdiv
      norm_num at this
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p:=2) (G:=G)).exists_card_eq
  have hdiv : 2^n ∣ Nat.card q.ker := hn ▸ card_dvd_of_le hle
  have hn0 : n=0 := by
    by_contra hn0
    have hd : 2 ∣ 2^n := dvd_pow_self 2 hn0
    exact ho.not_two_dvd_nat (hd.trans hdiv)
  apply Subgroup.card_eq_one.mp
  rw [hn,hn0,pow_zero]

omit [Finite G] [FiniteDimensional (ZMod 2) W] in
theorem fixed_quotient_faithful
    (ρ:Representation (ZMod 2) G W) (hf:Function.Injective ρ)
    (hc:pCore 2 G=⊥) : Function.Injective (fixedQuotient ρ ⊤) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  let x:(⊤:Subgroup G) := ⟨g,mem_top g⟩
  have hx : x∈(fixedQuotientRepresentation ρ ⊤).ker :=
    (mem_fixedQuotient_ker_iff ρ ⊤ x).mpr ((quotient_kernel_iff ρ ⊤ g).mp hg)
  have hh := fixedQuotient_ker_le_pCore ρ hf ⊤ hx
  rw [pCore_eq_comap_of_normal,hc] at hh
  exact hh

/-- A quadratic offender above A5 removes the original odd action kernel. -/
theorem recognize [Group.IsPerfect G]
    (ρ:Representation (ZMod 2) G W) (hf:Function.Injective ρ)
    (q:G→*A5) (hs:Function.Surjective q)
    (ho:Odd (Nat.card q.ker)) [Group.IsNilpotent q.ker]
    (hFr:q.ker≤frattini G) (P:Subgroup G) (hp:IsPGroup 2 P)
    (hc:Nat.card P=2 ∨ Nat.card P=4) (hm:Nat.card (P.map q)=Nat.card P)
    (hd:fixedCodim ρ P≤Nat.log 2 (Nat.card P)) :
    Function.Injective q ∧ Nat.card P=4 ∧ fixedCodim ρ ⊤=4 := by
  have hfour := offender_card_four ρ hf q hs P hc hm hd
  have hd2 : fixedCodim ρ P≤2 := by simpa only [hfour,show Nat.log 2 4=2 by decide] using hd
  obtain ⟨g,hg⟩ := conjugate_generation q hs hFr P hp (hm.trans hfour)
  have hu := fixed_quotient_degree_le_four ρ P g hg hd2
  have hfaith := fixed_quotient_faithful ρ hf (two_core_eq_bot q hs ho)
  have hdiv : 5 ∣ Nat.card A5 := by rw [card_five]; decide
  have hlo := BinaryPrimeDegree.orderOf_le_finrank (fixedQuotient ρ ⊤) hfaith
    (by decide : Nat.Prime 5) (by decide) (hdiv.trans (card_dvd_of_surjective q hs))
  rw [BinaryPrimeDegree.orderOf_two_mod_five] at hlo
  have hdim : Module.finrank (ZMod 2) (W⧸fixedSpace ρ ⊤)=4 := by
    change 4≤fixedCodim ρ ⊤ at hlo
    change fixedCodim ρ ⊤=4
    omega
  exact ⟨BinaryFourOddKernel.injective_alternatingFive_of_odd_nilpotent_kernel
    (fixedQuotient ρ ⊤) hfaith hdim q hs ho,hfour,hdim⟩
end Representation.AlternatingFiveOffenderRecognition
