module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Sylow fusion and containment through an odd kernel

The image of a strongly closed set in a Sylow subgroup is strongly closed
under a surjective homomorphism. To prove this, lift a conjugator and conjugate
the returning prime-power element into the original Sylow subgroup inside the
preimage of its image. Conjugation by an element of the original Sylow subgroup then removes
the correction in the image. This part requires no restriction on the kernel.

A kernel of odd order is injective on the Sylow two-subgroup. Hence elementary
four-groups survive, and containment between factor images reflects to the
original factors. This supplies the quotient step in the internal rigidity
argument for Aschbacher (1975), Lemma 3.4, printed pp.94–96.

`SylowFactorRigidity` names the precise remaining model theorem. No instance
of that proposition is asserted here.
-/

@[expose] public section

open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75.InternalRigidity

/-- The local factor-nesting assertion to be proved for each concrete model. -/
def SylowFactorRigidity (X : Type*) [Group X] : Prop :=
  ∀ (P : Sylow 2 X) (B C : Subgroup X), B ≤ P → C ≤ P →
    ⁅B, C⁆ = ⊥ → TwoRankAtLeastTwo B → TwoRankAtLeastTwo C →
    IsStronglyClosedSet ((B : Set X) ∪ C) (P : Subgroup X) ⊤ →
    B ≤ C ∨ C ≤ B

/-- Strong closure of a set descends through a surjection. -/
theorem stronglyClosed_image {G Q : Type*} [Group G] [Finite G] [Group Q]
    (P : Sylow 2 G) (U : Set G)
    (hU : IsStronglyClosedSet U (P : Subgroup G) ⊤)
    (q : G →* Q) (hq : Function.Surjective q) :
    IsStronglyClosedSet (q '' U) ((P : Subgroup G).map q) ⊤ := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_map_of_mem q (hU.1 hx)
  rintro _ ⟨x, hx, rfl⟩ g _ hg
  obtain ⟨g, rfl⟩ := hq g
  let K := ((P : Subgroup G).map q).comap q
  have hPK : (P : Subgroup G) ≤ K := fun x hx => mem_map_of_mem q hx
  have hxgK : g⁻¹ * x * g ∈ K := by
    simpa only [K, mem_comap, map_mul, map_inv] using hg
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_orderOf_eq_pow (⟨x, hU.1 hx⟩ : P)
  have hn' : orderOf (⟨g⁻¹ * x * g, hxgK⟩ : K) = 2 ^ n := by
    rw [Subgroup.orderOf_mk]
    calc
      orderOf (g⁻¹ * x * g) = orderOf x := by
        simpa only [MulAut.conj_apply, inv_inv] using (MulAut.conj g⁻¹).orderOf_eq x
      _ = 2 ^ n := by simpa only [Subgroup.orderOf_mk] using hn
  obtain ⟨y, k, hk⟩ := (P.subtype hPK).exists_isConj_of_orderOf_eq_prime_pow hn'
    |>.imp (fun _ hy => isConj_iff.mp hy)
  have hk' : (k : G) * (g⁻¹ * x * g) * (k : G)⁻¹ = ((y : K) : G) :=
    congrArg Subtype.val hk
  have hyU : ((y : K) : G) ∈ U := by
    have he : (g * (k : G)⁻¹)⁻¹ * x * (g * (k : G)⁻¹) = ((y : K) : G) := by
      rw [← hk']; group
    have hh := hU.2 x hx (g * (k : G)⁻¹) (mem_top _)
      (he.symm ▸ y.property)
    rwa [he] at hh
  obtain ⟨p, hp, hqp⟩ := (k.property : q (k : G) ∈ (P : Subgroup G).map q)
  have hpyp : p⁻¹ * ((y : K) : G) * p ∈ (P : Subgroup G) :=
    mul_mem (mul_mem (inv_mem hp) y.property) hp
  refine ⟨p⁻¹ * ((y : K) : G) * p, hU.2 _ hyU p (mem_top _) hpyp, ?_⟩
  rw [← hk']
  simp only [map_mul, map_inv, hqp]
  group

/-- An injective homomorphism transports an elementary four-group. -/
theorem rank_map_of_injective {G Q : Type*} [Group G] [Group Q]
    (q : G →* Q) (hq : Function.Injective q)
    (hG : TwoRankAtLeastTwo G) : TwoRankAtLeastTwo Q := by
  obtain ⟨E, hE, hsq⟩ := hG
  refine ⟨E.map q, ?_, ?_⟩
  · rw [card_map_of_injective hq, hE]
  · rintro ⟨x, a, ha, rfl⟩
    apply Subtype.ext
    change q a ^ 2 = 1
    rw [← map_pow, show a ^ 2 = 1 from congrArg Subtype.val (hsq ⟨a, ha⟩), map_one]

/-- Model rigidity lifts through a surjection with odd kernel. -/
theorem rigidity_of_surjective_coprime {G Q : Type*} [Group G] [Finite G] [Group Q]
    (q : G →* Q) (hq : Function.Surjective q)
    (hker : Nat.Coprime 2 (Nat.card q.ker))
    (hr : SylowFactorRigidity Q) : SylowFactorRigidity G := by
  intro P B C hBP hCP hBC hB hC hc
  have hi := injective_comp_subtype_of_coprime_ker q hker (P : Subgroup G) P.isPGroup'
  have hrank : ∀ A : Subgroup G, A ≤ P → TwoRankAtLeastTwo A →
      TwoRankAtLeastTwo (A.map q) := by
    intro A hAP hA
    apply rank_map_of_injective (q.subgroupMap A) _ hA
    intro x y he
    have he' : (⟨(x : G), hAP x.property⟩ : P) = ⟨(y : G), hAP y.property⟩ :=
      hi (congrArg Subtype.val he)
    exact Subtype.ext (congrArg (fun t : P => (t : G)) he')
  have hclosed : IsStronglyClosedSet ((B.map q : Set Q) ∪ C.map q)
      (P.mapSurjective hq : Subgroup Q) ⊤ := by
    simpa only [Sylow.coe_mapSurjective, Set.image_union, Subgroup.coe_map] using
      stronglyClosed_image P ((B : Set G) ∪ C) hc q hq
  have hcomm : ⁅B.map q, C.map q⁆ = ⊥ := by
    rw [← map_commutator, hBC, Subgroup.map_bot]
  have hreflect : ∀ A D : Subgroup G, A ≤ P → D ≤ P → A.map q ≤ D.map q → A ≤ D := by
    intro A D hAP hDP hm x hx
    obtain ⟨y, hy, he⟩ := hm (mem_map_of_mem q hx)
    have he' : (⟨y, hDP hy⟩ : P) = ⟨x, hAP hx⟩ := hi he
    have hyx : y = x := congrArg (fun t : P => (t : G)) he'
    exact hyx ▸ hy
  rcases hr (P.mapSurjective hq) (B.map q) (C.map q)
      (map_mono hBP) (map_mono hCP) hcomm (hrank B hBP hB) (hrank C hCP hC)
      hclosed with hh | hh
  · exact Or.inl (hreflect B C hBP hCP hh)
  · exact Or.inr (hreflect C B hCP hBP hh)

/-- Rigidity transports along an actual equivalence of the group carriers. -/
theorem rigidity_of_mulEquiv {G Q : Type*} [Group G] [Finite G] [Group Q]
    (e : G ≃* Q) (hr : SylowFactorRigidity Q) : SylowFactorRigidity G := by
  apply rigidity_of_surjective_coprime e.toMonoidHom e.surjective _ hr
  rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective, card_bot]
  exact Nat.coprime_one_right _

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75.InternalRigidity

end
