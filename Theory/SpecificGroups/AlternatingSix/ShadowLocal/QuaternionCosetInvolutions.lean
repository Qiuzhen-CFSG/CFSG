module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.QuaternionInvolutionAction
public import Theory.GroupTheory.NormalizedSupCard
/-!
# Two natural involutions in a marked quaternion coset

A quaternion subgroup normalized by a natural outer involution embeds with
that involution in a Sylow two-subgroup of Aut(A₆). Its marked holomorph
coordinates identify the natural involutions in the quaternion coset with
the identity and central involution of Q₈. The transport preserves the
literal natural symmetric subgroup and requires only the source central
commutator condition, not a conclusion about conjugacy or cardinality.

Source: Aschbacher--Smith J.2.7(8), printed p.437; this is the two-element
quaternion fiber in the 480-element middle-layer count.
-/

public section
noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace AlternatingSix.ShadowLocal.QuaternionCosetInvolutions
open Holomorph
private abbrev qe := M10.LocalGeometry.Coordinates.quaternionEmbedding
set_option maxRecDepth 10000 in
private theorem pair_table (x y : Model) (hx : x ^ 2 ≠ 1)
    (hs : x ^ 2 = y ^ 2) (hi : y * x = x⁻¹ * y) (hn : x * y ≠ y * x) :
    (∃ d, qe d = x) ∧ (∃ d, qe d = y) := by
  revert x y
  decide +kernel

private theorem range_eq (f : QuaternionGroup 2 →* Model) (hf : Function.Injective f) :
    f.range = qe.range := by
  let i : QuaternionGroup 2 := .a 1
  let j : QuaternionGroup 2 := .xa 0
  have hi : f i ^ 2 ≠ 1 := by
    intro he
    have : i ^ 2 = 1 := hf (by simpa only [map_pow, map_one] using he)
    exact (by decide : i ^ 2 ≠ 1) this
  have hs : f i ^ 2 = f j ^ 2 := by
    rw [← map_pow, ← map_pow]
    congr 1
  have hj : f j * f i = (f i)⁻¹ * f j := by
    simpa only [map_mul, map_inv] using congrArg f
      (show j * i = i⁻¹ * j by decide)
  have hn : f i * f j ≠ f j * f i := by
    intro he
    exact (by decide : i * j ≠ j * i) (hf (by simpa only [map_mul] using he))
  obtain ⟨hiQ, hjQ⟩ := pair_table (f i) (f j) hi hs hj hn
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, rfl⟩
    have words : ∀ x : QuaternionGroup 2, ∃ k : Fin 4,
        x = i ^ k.val ∨ x = j * i ^ k.val := by decide
    obtain ⟨k, hk | hk⟩ := words x
    · rw [hk, map_pow]
      exact qe.range.pow_mem hiQ _
    · rw [hk, map_mul, map_pow]
      exact qe.range.mul_mem hjQ (qe.range.pow_mem hiQ _)
  · rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective
        M10.LocalGeometry.Coordinates.quaternionEmbedding_injective).toEquiv]

private theorem center_image (f : QuaternionGroup 2 →* Model) (hf : Function.Injective f) :
    f (.a 2) = qe (.a 2) := by
  have hm : f (.a 2) ∈ qe.range := range_eq f hf ▸ ⟨.a 2, rfl⟩
  obtain ⟨d, hd⟩ := hm
  have hne : qe d ≠ 1 := by
    rw [hd]
    intro he
    exact (by decide : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1)
      (hf (he.trans f.map_one.symm))
  have hs : (qe d) ^ 2 = 1 := by
    rw [hd, ← map_pow]
    exact f.map_one
  have ht : ∀ d : QuaternionGroup 2, qe d ≠ 1 → (qe d) ^ 2 = 1 → qe d = qe (.a 2) :=
    by decide
  exact hd.symm.trans (ht d hne hs)


set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 10000 in
private theorem coset_table (r : Model) (hr : r^2=1)
    (hn : ∃a, naturalEmbedding a=r) (hQ : ¬∃q, qe q=r)
    (hc : ∀q, ⁅r,qe q⁆=1 ∨ ⁅r,qe q⁆=qe (.a 2)) :
    ∀q : QuaternionGroup 2,
      ((r*qe q)^2=1 ∧ r*qe q≠1 ∧ ∃a, naturalEmbedding a=r*qe q) ↔
        q=1 ∨ q=.a 2 := by
  revert r
  decide +kernel

private theorem model_coset_iff (f : QuaternionGroup 2→*Model) (hf : Function.Injective f)
    (r : Model) (hr : r^2=1) (hn : r∈Holomorph.natural) (hQ : r∉f.range)
    (hc : ∀q, ⁅r,f q⁆=1 ∨ ⁅r,f q⁆=f (.a 2)) (q : QuaternionGroup 2) :
    ((r*f q)^2=1 ∧ r*f q≠1 ∧ r*f q∈Holomorph.natural) ↔ q=1 ∨ q=.a 2 := by
  have hR := range_eq f hf
  have hZ := center_image f hf
  have hc' (d : QuaternionGroup 2) : ⁅r,qe d⁆=1 ∨ ⁅r,qe d⁆=qe (.a 2) := by
    have hd : qe d∈f.range := hR.symm ▸ ⟨d,rfl⟩
    obtain ⟨a,ha⟩ := hd
    simpa only [ha,hZ] using hc a
  have hrQ : ¬∃d,qe d=r := by
    intro hh
    apply hQ
    rw [hR]
    exact hh
  have hm : f q∈qe.range := hR ▸ ⟨q,rfl⟩
  obtain ⟨d,hd⟩ := hm
  rw [← hd,Holomorph.mem_natural]
  rw [coset_table r hr ((Holomorph.mem_natural _).mp hn) hrQ hc']
  constructor
  · rintro (rfl | rfl)
    · left
      exact hf (hd.symm.trans (map_one qe) |>.trans (map_one f).symm)
    · right
      exact hf (hd.symm.trans hZ.symm)
  · rintro (rfl | rfl)
    · left
      exact M10.LocalGeometry.Coordinates.quaternionEmbedding_injective
        (hd.trans (map_one f) |>.trans (map_one qe).symm)
    · right
      exact M10.LocalGeometry.Coordinates.quaternionEmbedding_injective (hd.trans hZ)

/-- A natural involution centralizing the quaternion quotient has exactly two
natural involutions in its actual quaternion coset. -/
theorem natural_involutions_in_coset_card
    (Q : Subgroup AutA6) (hQ : Nonempty (Q≃*QuaternionGroup 2))
    (hQM : Q≤M10.extension) (β : AutA6) (hβ : orderOf β=2)
    (hβn : β∈ShadowLocal.natural) (hβM : β∉M10.extension)
    (hc : ∀q:Q, ⁅β,(q:AutA6)⁆∈(center Q).map Q.subtype) :
    Nat.card {q:Q // orderOf (β*(q:AutA6))=2 ∧ β*(q:AutA6)∈ShadowLocal.natural}=2 := by
  obtain ⟨eQ⟩ := hQ
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (n:=3) (by
    rw [Nat.card_congr eQ.toEquiv,Nat.card_eq_fintype_card]; decide +kernel)
  have hβ2 := (orderOf_eq_prime_iff.mp hβ).1
  have hconj (q : AutA6) (hq : q∈Q) : β*q*β⁻¹∈Q := by
    have hh := (map_subtype_le (center Q)) (hc ⟨q,hq⟩)
    have he : ⁅β,q⁆*q=β*q*β⁻¹ := by group
    exact he ▸ Q.mul_mem hh hq
  have hβinv : β⁻¹=β := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hβ2)
  have hβN : β∈normalizer (Q:Set AutA6) := by
    apply mem_normalizer_iff.mpr
    intro q
    refine ⟨hconj q,fun h => ?_⟩
    have hh := hconj _ h
    have he : β*(β*q*β⁻¹)*β⁻¹=q := by
      rw [hβinv]
      have hs : β*β=1 := by simpa only [pow_two] using hβ2
      calc β*(β*q*β)*β=(β*β)*q*(β*β) := by group
           _=q := by rw [hs,one_mul,mul_one]
    exact he ▸ hh
  have hzp : IsPGroup 2 (zpowers β) := IsPGroup.of_card (n:=1) (by rw [Nat.card_zpowers,hβ,pow_one])
  obtain ⟨T,hT⟩ := (hQ2.to_sup_of_normal_left' hzp (zpowers_le.mpr hβN)).exists_le_sylow
  have hQT : Q≤(T:Subgroup AutA6) := le_sup_left.trans hT
  have hβT : β∈T := hT (mem_sup_right (mem_zpowers β))
  let e := Identification.sylowEquiv T
  let j : QuaternionGroup 2→*T := (inclusion hQT).comp eQ.symm.toMonoidHom
  let f : QuaternionGroup 2→*Model := e.symm.toMonoidHom.comp j
  have hf : Function.Injective f := e.symm.injective.comp (inclusion_injective hQT |>.comp eQ.symm.injective)
  let b : T := ⟨β,hβT⟩
  let r : Model := e.symm b
  have hn (x:Model) : x∈Holomorph.natural ↔ (e x:AutA6)∈ShadowLocal.natural := by
    change x∈Holomorph.natural ↔ e x∈sylowNatural T
    rw [← Identification.sylowEquiv_natural T]
    constructor
    · exact fun hx => mem_map_of_mem e.toMonoidHom hx
    · rintro ⟨y,hy,he⟩
      exact e.injective he ▸ hy
  have hr : r^2=1 := by
    change (e.symm b)^2=1
    rw [← map_pow,show b^2=1 from Subtype.ext hβ2,map_one]
  have hrn : r∈Holomorph.natural := (hn r).mpr (by
    change (e (e.symm b):AutA6)∈ShadowLocal.natural
    simpa only [e.apply_symm_apply] using hβn)
  have hrQ : r∉f.range := by
    rintro ⟨q,hq⟩
    have he := congrArg (fun x:Model => (e x:AutA6)) hq
    change (e (e.symm (j q)):AutA6)=(e (e.symm b):AutA6) at he
    simp only [e.apply_symm_apply] at he
    change (eQ.symm q:AutA6)=β at he
    exact hβM (he ▸ hQM (eQ.symm q).property)
  have hcent : ∀z:Q, z∈center Q → z=1 ∨ z=eQ.symm (.a 2) := by
    intro z hz
    have hze : eQ z∈center (QuaternionGroup 2) := by
      apply mem_center_iff.mpr
      intro a
      have hh := congrArg eQ (mem_center_iff.mp hz (eQ.symm a))
      simpa only [map_mul,eQ.apply_symm_apply] using hh
    have ht : ∀z:QuaternionGroup 2,z∈center (QuaternionGroup 2) → z=1 ∨ z=.a 2 := by decide +kernel
    rcases ht (eQ z) hze with hh | hh
    · exact .inl (eQ.injective (hh.trans (map_one eQ).symm))
    · exact .inr (eQ.injective (hh.trans (eQ.apply_symm_apply _).symm))
  have hcf (q:QuaternionGroup 2) : ⁅r,f q⁆=1 ∨ ⁅r,f q⁆=f (.a 2) := by
    obtain ⟨z,hz,hze⟩ := hc (eQ.symm q)
    rcases hcent z hz with hz1 | hzz
    · left
      have hh : ⁅b,j q⁆=1 := Subtype.ext (hze.symm.trans (congrArg (fun z:Q => (z:AutA6)) hz1))
      change ⁅e.symm b,e.symm (j q)⁆=1
      simpa only [map_commutatorElement,map_one] using congrArg e.symm hh
    · right
      have hh : ⁅b,j q⁆=j (.a 2) := Subtype.ext (hze.symm.trans (congrArg (fun z:Q => (z:AutA6)) hzz))
      change ⁅e.symm b,e.symm (j q)⁆=e.symm (j (.a 2))
      simpa only [map_commutatorElement] using congrArg e.symm hh
  have hiff (q : Q) : (orderOf (β*(q:AutA6))=2 ∧ β*(q:AutA6)∈ShadowLocal.natural) ↔
      eQ q=1 ∨ eQ q=.a 2 := by
    have hmap : (e (r*f (eQ q)):AutA6)=β*(q:AutA6) := by
      change (e (e.symm b * e.symm (j (eQ q))):AutA6)=_
      rw [map_mul,e.apply_symm_apply,e.apply_symm_apply]
      simp only [j,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,eQ.symm_apply_apply]
      rfl
    have horder : orderOf (r*f (eQ q))=orderOf (β*(q:AutA6)) := by
      rw [← hmap]
      exact (e.orderOf_eq _).symm.trans (orderOf_injective (T:Subgroup AutA6).subtype (T:Subgroup AutA6).subtype_injective (e _)).symm
    rw [← horder,← hmap,← hn]
    rw [orderOf_eq_prime_iff]
    exact (and_assoc).trans (model_coset_iff f hf r hr hrn hrQ hcf (eQ q))
  let eqv : {q:Q // orderOf (β*(q:AutA6))=2 ∧ β*(q:AutA6)∈ShadowLocal.natural} ≃
      {a:QuaternionGroup 2 // a=1 ∨ a=.a 2} := eQ.toEquiv.subtypeEquiv hiff
  rw [Nat.card_congr eqv,Nat.card_eq_fintype_card]
  decide +kernel

end AlternatingSix.ShadowLocal.QuaternionCosetInvolutions
