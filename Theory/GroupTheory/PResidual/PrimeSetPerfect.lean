module

public import Theory.GroupTheory.PResidual.PrimeSetFiniteImage
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.AmalgamLocalCores

/-!
# Perfect prime-set residuals and a common normal subgroup

Finite prime-set residuals are characteristic and pi-perfect. Adjoining a
normalizing two-group to a {2,3}-perfect subgroup preserves its embedded
residual. This lets a commutator bound modulo a two-group make that residual
normal under both sides of an amalgam. Characteristic two and the trivial
generated two-core then force the residual to vanish.

Source: Aschbacher–Smith 13.3.8, printed pp.886–887. The last theorem
retains the actual normalizers, commutator bound and generated group.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]

instance piResidual_characteristic (π:Set Nat.Primes) : (piResidual π G).Characteristic := by
  apply characteristic_iff_map_eq.mpr
  intro e
  exact map_piResidual_of_surjective π e.toMonoidHom e.surjective

theorem isPiPerfect_piResidual (π:Set Nat.Primes) : IsPiPerfect π (piResidual π G) := by
  let R:=piResidual π G
  let S:=piResidual π R
  let K:=S.map R.subtype
  let q:=QuotientGroup.mk' K
  let a:=q.comp R.subtype
  have hak:a.ker=S := by
    change (q.comp R.subtype).ker=S
    rw [←MonoidHom.comap_ker]
    rw [show q.ker=K from QuotientGroup.ker_mk' K]
    change (S.map R.subtype).comap R.subtype=S
    exact comap_map_eq_self_of_injective R.subtype_injective S
  have hF:IsPiGroup π a.range := by
    let e:R⧸S≃*a.range := (QuotientGroup.quotientMulEquivOfEq hak.symm).trans
      (QuotientGroup.quotientKerEquivRange a)
    exact (isPiGroup_quotient_piResidual π).of_equiv e.symm
  have hF':IsPiGroup π (R.map q) := by
    have he:a.range=R.map q := by
      change (q.comp R.subtype).range=_
      rw [MonoidHom.range_comp,range_subtype]
    exact he ▸ hF
  have hQ:IsPiGroup π ((G⧸K)⧸R.map q) :=
    (isPiGroup_quotient_piResidual π).of_equiv
      (QuotientGroup.quotientQuotientEquivQuotient K R (map_subtype_le S))
  have hGK:IsPiGroup π (G⧸K) :=
    IsPiGroup.of_normal_subgroup_and_quotient (R.map q) (hF'.isPiSubgroup _) hQ
  have hRK:R≤K := sInf_le ⟨inferInstance,hGK⟩
  apply (piResidual_eq_top_iff π R).mp
  apply top_unique
  intro x _
  obtain ⟨y,hy,he⟩:=hRK x.property
  have hxy:y=x := Subtype.ext he
  exact hxy ▸ hy

theorem piResidual_eq_of_isPiPerfect (π:Set Nat.Primes) (N:Subgroup G) [N.Normal]
    (hp:IsPiPerfect π N) (hq:IsPiGroup π (G⧸N)) : piResidual π G=N := by
  apply le_antisymm (show piResidual π G≤N from sInf_le ⟨inferInstance,hq⟩)
  have hh:=map_piResidual_le π N.subtype
  rw [(piResidual_eq_top_iff π N).mpr hp,←MonoidHom.range_eq_map,range_subtype] at hh
  exact hh

theorem embedded_piResidual_join_two (N Q:Subgroup G)
    (hp:IsPiPerfect twoThreePrimes N) (hq:IsPGroup 2 Q)
    (hn:Q≤normalizer (N:Set G)) :
    (piResidual twoThreePrimes (N⊔Q:Subgroup G)).map (N⊔Q).subtype=N := by
  let J:=N⊔Q
  have hNJ:N≤J:=le_sup_left
  have hQJ:Q≤J:=le_sup_right
  let : (N.subgroupOf J).Normal:=normal_subgroupOf_of_le_normalizer
    (sup_le N.le_normalizer hn)
  have hp':IsPiPerfect twoThreePrimes (N.subgroupOf J) := hp.of_surjective
    (subgroupOfEquivOfLe hNJ).symm.toMonoidHom (subgroupOfEquivOfLe hNJ).symm.surjective
  have hs:N.subgroupOf J⊔Q.subgroupOf J=⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hNJ,map_subgroupOf_eq_of_le hQJ,
      ←MonoidHom.range_eq_map,range_subtype]
  have h2:IsPGroup 2 (J⧸N.subgroupOf J) :=
    isPGroup_quotient_of_sup_eq_top _ _ hq.comap_subtype hs
  have hpi:IsPiGroup twoThreePrimes (J⧸N.subgroupOf J) := by
    rw [IsPiGroup_iff]
    intro p hd
    obtain ⟨n,hn⟩:=h2.exists_card_eq
    have he:p.val=2 := (Nat.dvd_prime Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow (hn ▸ hd)) |>.resolve_left p.property.ne_one
    exact Or.inl he
  rw [piResidual_eq_of_isPiPerfect twoThreePrimes _ hp' hpi,map_subgroupOf_eq_of_le hNJ]
/-- The residual-normalizer argument in13.3.8: a kernel commutator bound
and the original characteristic-two amalgam force a {2,3}-group. -/
theorem twoThree_of_residual_commutator (L H Y Q:Subgroup G)
    (hYH:Y≤H) (hnY:H≤normalizer (Y:Set G))
    (hQH:Q≤H) (hq:IsPGroup 2 Q) (hnQ:L≤normalizer (Q:Set G))
    (hcomm:⁅L,(piResidual twoThreePrimes Y).map Y.subtype⁆≤Q)
    (hcore:pCore 2 (L⊔H:Subgroup G)=⊥)
    (hchar:centralizer (pCore 2 H:Set H)≤pCore 2 H) : IsPiGroup twoThreePrimes Y := by
  let N:=(piResidual twoThreePrimes Y).map Y.subtype
  have hNY:N≤Y:=map_subtype_le _
  have hNH:N≤H:=hNY.trans hYH
  have hnH:H≤normalizer (N:Set G) := hnY.trans
    (normalizer_le_normalizer_characteristic_image Y (piResidual twoThreePrimes Y))
  have hp:IsPiPerfect twoThreePrimes N :=
    (isPiPerfect_piResidual twoThreePrimes).of_surjective
      (Y.subtype.subgroupMap (piResidual twoThreePrimes Y))
      (Y.subtype.subgroupMap_surjective (piResidual twoThreePrimes Y))
  have hnJoin:L≤normalizer ((N⊔Q:Subgroup G):Set G) := by
    apply le_normalizer_iff.mpr
    intro l hl x hx
    have hn:N.map (MulAut.conj l).toMonoidHom≤N⊔Q := by
      rintro _ ⟨n,hn,rfl⟩
      have hc:⁅l,n⁆∈Q:=hcomm (commutator_mem_commutator hl hn)
      have hm:(⁅l,n⁆)*n∈N⊔Q := (N⊔Q).mul_mem (mem_sup_right hc) (mem_sup_left hn)
      change l*n*l⁻¹∈N⊔Q
      simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hm
    have hqmap:Q.map (MulAut.conj l).toMonoidHom≤Q := by
      rintro _ ⟨q,hq,rfl⟩
      exact le_normalizer_iff.mp hnQ l hl q hq
    have hm:(N⊔Q).map (MulAut.conj l).toMonoidHom≤N⊔Q := by
      rw [Subgroup.map_sup]
      exact sup_le hn (hqmap.trans le_sup_right)
    exact hm (mem_map_of_mem _ hx)
  have hnL:L≤normalizer (N:Set G) := by
    rw [←embedded_piResidual_join_two N Q hp hq (hQH.trans hnH)]
    exact hnJoin.trans (normalizer_le_normalizer_characteristic_image (N⊔Q)
      (piResidual twoThreePrimes (N⊔Q:Subgroup G)))
  have hsup:H⊔(L⊔N)=L⊔H := by
    apply le_antisymm
    · exact sup_le le_sup_right (sup_le le_sup_left (hNH.trans le_sup_right))
    · exact sup_le (le_sup_left.trans le_sup_right) le_sup_left
  have hNb:N=⊥ := Theory.GroupTheory.AmalgamLocalCores.common_normal_eq_bot H (L⊔N) N
    (le_inf hNH le_sup_right) hnH (sup_le hnL N.le_normalizer) (by rwa [hsup]) hchar
  have he:piResidual twoThreePrimes Y=⊥ :=
    ((piResidual twoThreePrimes Y).map_eq_bot_iff_of_injective Y.subtype_injective).mp hNb
  have hh:=isPiGroup_quotient_piResidual (G:=Y) twoThreePrimes
  exact hh.of_equiv ((QuotientGroup.quotientMulEquivOfEq he).trans
    QuotientGroup.quotientBot).symm
end Subgroup

