module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.Source
public import Theory.GroupAction.FixedComponentPerfectActor
public import Theory.GroupTheory.GeneralizedFitting.CommutingPairPerfectActor
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.SecondExchanged

/-! A perfect subgroup fixing the original component pointwise and
normalizing its actual overcomponent centralizes that entire overcomponent.
The original swapping involution is retained in both rows. This is the
pointwise-fixer step of source 2.5.19, printed p.564. -/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection OvercomponentsSource PrimeRows CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

theorem source_prime_orbit_perfect_centralizer
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
    (C : Subgroup G) [Group.IsPerfect C]
    (hCK : C ≤ centralizer (K : Set G)) (hCt : C ≤ centralizer ({t} : Set G))
    (hCN : let Gi := centralizer ({i} : Set G)
      let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
      C ≤ normalizer (X.map Gi.subtype : Set G)) :
    let Gi := centralizer ({i} : Set G)
    let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
    C ≤ centralizer (X.map Gi.subtype : Set G) := by
  let Gi := centralizer ({i} : Set G)
  let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
  let XA := X.map Gi.subtype
  change C ≤ centralizer (XA : Set G)
  change C ≤ normalizer (XA : Set G) at hCN
  obtain ⟨htI,hrows⟩ := source_bad_prime_rows c hG hempty hgen hb hstar
    hp hp7 eK t i ht htC htZ hi
  rcases hrows with ⟨hX,_,_,a,ha,hact,hB,⟨eKB⟩,hmodel⟩ |
    ⟨A,hA,hm,hpair,hZA,⟨eAK⟩⟩
  · let : IsQuasisimple X := hX.2
    let B := ((K.subgroupOf Gi).subgroupOf X).subgroupOf a.fixedSubgroup
    have hcard := source_prime_quotient_fixer_card_le_two c hG hempty hgen hb a ha B hB.2 eKB hmodel
    let e : X ≃* XA := X.equivMapOfInjective Gi.subtype Gi.subtype_injective
    let f₀ : C →* MulAut XA := XA.normalizerMonoidHom.comp (inclusion hCN)
    let f : C →* MulAut X := (MulAut.congr e.symm).toMonoidHom.comp f₀
    have hf (q : C) (x : X) : (((f q) x : Gi) : G) =
        (q:G) * ((x:Gi):G) * (q:G)⁻¹ := by
      have he : e ((f q) x) = (f₀ q) (e x) := by
        change e (e.symm ((f₀ q) (e x))) = _
        exact e.apply_symm_apply _
      exact congrArg (fun y : XA => (y:G)) he
    have hf1 : f = 1 := MulAut.perfect_fixed_component_action_eq_one a B f (by
      intro q
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      apply Subtype.ext
      change (((f q) (a x) : Gi) : G) = ((a ((f q) x) : Gi) : G)
      rw [hf,hact,hact,hf]
      have hqt := mem_centralizer_singleton_iff.mp (hCt q.property)
      calc
        _ = ((q:G)*t) * ((x:Gi):G) * ((q:G)*t)⁻¹ := by group
        _ = (t*(q:G)) * ((x:Gi):G) * (t*(q:G))⁻¹ := by rw [hqt]
        _ = _ := by group) (by
      intro q x
      apply Subtype.ext
      apply Subtype.ext
      rw [hf]
      have hc := hCK q.property (((x:a.fixedSubgroup):X):Gi) x.property
      rw [←hc,mul_inv_cancel_right]) hcard
    intro q hq y hy
    obtain ⟨x,hx,rfl⟩ := hy
    have he := hf ⟨q,hq⟩ ⟨x,hx⟩
    rw [hf1] at he
    change (x:G) = q * (x:G) * q⁻¹ at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  · let ti : Gi := ⟨t,htI⟩
    change X = A ⊔ A.map (MulAut.conj ti).toMonoidHom at hpair
    let P := A.map Gi.subtype
    let eP : A ≃* P := A.equivMapOfInjective Gi.subtype Gi.subtype_injective
    let : IsQuasisimple A := hA.2
    let : IsQuasisimple P := IsQuasisimple.of_mulEquiv eP
    have hXA : XA = P ⊔ P.map (MulAut.conj t).toMonoidHom := by
      change X.map Gi.subtype = _
      rw [hpair,Subgroup.map_sup,map_map]
      change P ⊔ A.map ((MulAut.conj t).toMonoidHom.comp Gi.subtype) = _
      rw [←map_map]
    have hcA : A ≤ centralizer (A.map (MulAut.conj ti).toMonoidHom : Set Gi) :=
      commutator_eq_bot_iff_le_centralizer.mp
        (hA.commutator_eq_bot_of_ne (hA.map_conj ti) hm)
    have hcomm : P ≤ centralizer (P.map (MulAut.conj t).toMonoidHom : Set G) := by
      rintro x ⟨x,hx,rfl⟩ y ⟨v,⟨v,hv,rfl⟩,rfl⟩
      exact congrArg Subtype.val (hcA hx _ (mem_map_of_mem (MulAut.conj ti).toMonoidHom hv))
    have hmove : P.map (MulAut.conj t).toMonoidHom ≠ P := by
      intro he
      apply hm
      apply (map_injective Gi.subtype_injective)
      change A.map Gi.subtype = (A.map (MulAut.conj ti).toMonoidHom).map Gi.subtype
      rw [map_map]
      change P = A.map ((MulAut.conj t).toMonoidHom.comp Gi.subtype)
      rw [←map_map]
      exact he.symm
    have hKi : K ≤ Gi := fun k hk => mem_centralizer_singleton_iff.mpr (hi.1.2 k hk)
    have hKt := source_component_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ
    have hDt := component_in_subgroup_centralizer K t hKt Gi hKi htI
    have ht2 : ti ^ 2 = 1 := Subtype.ext (ht ▸ pow_orderOf_eq_one t)
    have hKnorm := NormPair.fixed_component_eq_norm hA hm.symm ht2 hDt
      (hpair ▸ le_componentOrbit (K.subgroupOf Gi) (oddELayer Gi))
    have hnorm : ∀ x ∈ P, x*(t*x*t⁻¹)∈K := by
      rintro x ⟨v,hv,rfl⟩
      have hh : componentSwapNorm hA hm.symm ⟨v,hv⟩ ∈ K.subgroupOf Gi := by
        rw [hKnorm]
        exact ⟨⟨v,hv⟩,rfl⟩
      exact hh
    rw [hXA] at hCN ⊢
    exact perfect_actor_centralizes_exchanged_pair P C t (ht ▸ pow_orderOf_eq_one t)
      hmove hcomm hCN hCt (fun q hq x hx => hCK hq _ (hnorm x hx))
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
