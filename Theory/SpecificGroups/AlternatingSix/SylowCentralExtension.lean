module

public import Theory.SpecificGroups.AlternatingSix.SylowFixedAction
public import Theory.GroupTheory.NormalSubgroupInvolutionFiber
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.PPerfectHom

/-!
# Faithful A₆ extensions with a Sylow-central involution

An inner involution has centralizer of order 32 in Aut(A₆). Thus a two-perfect
subgroup centralizing it is trivial in every faithful extension. For an outer
involution centralizing a Sylow subgroup, the exceptional automorphism fixed-group
calculation places its original action in the natural S₆. The component and
this action generate S₆, and the constructed equivalence preserves the given
A₆ coordinates and the conjugation equation.

The Sylow in A₆ is the intersection with the original ambient Sylow. No
characteristic-two hypothesis on an involution fixed group is used, and no
outer automorphism is silently applied to the component coordinates.

Source: GLS, Volume 3, Proposition 5.2.7; Aschbacher–Smith, combined manuscript
of 1 March 2004, 13.5.21, printed p.924 (PDF p.941).
-/

@[expose] public section
open Subgroup
open AlternatingSix.ShadowLocal
namespace AlternatingSix.SylowCentralExtension
variable {E : Type*} [Group E]

/-- A two-perfect subgroup centralizing an inner involution vanishes in a faithful A₆ extension. -/
theorem residual_centralizing_inner_eq_bot (K : Subgroup E) [K.Normal]
    (e : K ≃* A6) (hK : centralizer (K : Set E) = ⊥)
    (v : K) (hv : orderOf v = 2) (Y : Subgroup E) (hY : IsPPerfect 2 Y)
    (hc : Y ≤ centralizer {(v : E)}) : Y = ⊥ := by
  let f := normalConjThrough K e
  have hinj : Function.Injective f :=
    (MulAut.congr e).injective.comp (MulAut.conjNormal_injective_of_centralizer_eq_bot K hK)
  have hp : IsPGroup 2 (centralizer ({MulAut.conj (e v)} : Set AutA6)) :=
    IsPGroup.of_card (show Nat.card (centralizer ({MulAut.conj (e v)} : Set AutA6)) = 2 ^ 5 from
      inner_involution_centralizer_card (e v) ((e.orderOf_eq v).trans hv))
  let g : Y →* centralizer ({MulAut.conj (e v)} : Set AutA6) :=
    (f.comp Y.subtype).codRestrict _ (by
      intro y
      apply mem_centralizer_singleton_iff.mpr
      rw [← normalConjThrough_coe K e v]
      exact (map_mul f _ _).symm.trans
        ((congrArg f (mem_centralizer_singleton_iff.mp (hc y.property))).trans (map_mul f _ _)))
  have hg := hY.hom_eq_one_of_isPGroup hp g
  apply le_bot_iff.mp
  intro y hy
  have he : f y = 1 :=
    congrArg (fun a : Y →* centralizer ({MulAut.conj (e v)} : Set AutA6) =>
      (a ⟨y,hy⟩).val) hg
  exact hinj (he.trans f.map_one.symm)

variable [Finite E]
/-- A Sylow-central outer involution generates the natural S₆ with the component.
The equivalence preserves the supplied component coordinates and conjugation. -/
theorem exists_marked_symmetric_extension
    (K : Subgroup E) [K.Normal] (hK : centralizer (K : Set E) = ⊥)
    (e : K ≃* A6) (T : Sylow 2 E) (v : E) (hv : orderOf v = 2)
    (hfix : ∀ x ∈ (T : Subgroup E), v * x = x * v) (hout : v ∉ K) :
    ∃ q : (K ⊔ zpowers v : Subgroup E) ≃* Equiv.Perm (Fin 6),
      (∀ x : K, q ⟨x, (le_sup_left : K ≤ K ⊔ zpowers v) x.property⟩ = (e x : Equiv.Perm (Fin 6))) ∧
      ∀ (g : (K ⊔ zpowers v : Subgroup E)) (x : K),
        (e (MulAut.conjNormal (g : E) x) : Equiv.Perm (Fin 6)) =
          q g * (e x : Equiv.Perm (Fin 6)) * (q g)⁻¹ := by
  let f := normalConjThrough K e
  have hinj : Function.Injective f :=
    (MulAut.congr e).injective.comp (MulAut.conjNormal_injective_of_centralizer_eq_bot K hK)
  obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_normal K
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hfn : f v ∈ natural := involution_mem_natural_of_fixes_sylow Q (f v)
    ((orderOf_injective f hinj v).trans hv) (by
      rintro _ ⟨x,hx,rfl⟩
      change normalConjThrough K e v (e x) = e x
      rw [normalConjThrough_apply]
      congr 1
      apply Subtype.ext
      have hxT : (x : E) ∈ (T : Subgroup E) := by
        change x ∈ (T : Subgroup E).subgroupOf K
        rwa [← hP]
      change v * (x : E) * v⁻¹ = x
      rw [hfix x hxT, mul_inv_cancel_right])
  have hfi : f v ∉ AlternatingSix.ShadowLocal.inner := by
    rintro ⟨a,ha⟩
    exact normalConjThrough_not_inner K e (by rw [hK]; exact bot_le) v hout ⟨a,ha.symm⟩
  let B := K ⊔ zpowers v
  let R := B.map f
  have hir : AlternatingSix.ShadowLocal.inner ≤ R := by
    rintro _ ⟨a,rfl⟩
    refine ⟨(e.symm a : E), (le_sup_left : K ≤ B) (e.symm a).property, ?_⟩
    rw [normalConjThrough_coe, e.apply_symm_apply]
  have hrn : R ≤ natural := by
    apply map_le_iff_le_comap.mpr
    apply sup_le
    · intro x hx
      change f x ∈ natural
      rw [show f x = MulAut.conj (e ⟨x,hx⟩) from normalConjThrough_coe K e ⟨x,hx⟩]
      exact inner_le_natural ⟨_,rfl⟩
    · exact zpowers_le.mpr hfn
  have hlt : AlternatingSix.ShadowLocal.inner < R := lt_of_le_of_ne hir (by
    intro he
    apply hfi
    rw [he]
    exact mem_map_of_mem f ((le_sup_right : zpowers v ≤ B) (mem_zpowers v)))
  have hidx := index_strictAnti hlt
  have hdiv := index_dvd_of_le hir
  have hpos : R.index ≠ 0 := index_ne_zero_of_finite
  have hlow := index_antitone hrn
  rw [inner_index] at hidx hdiv
  rw [GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index] at hlow
  have heq : R.index = 2 := by
    obtain ⟨n, hn, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show R.index ∣ 2 ^ 2 from hdiv)
    interval_cases n
    · change R.index = 1 at he
      omega
    · exact he
    · change R.index = 4 at he
      omega
  have hR : R = natural := by
    by_contra hne
    have hbad := index_strictAnti (lt_of_le_of_ne hrn hne)
    rw [heq, GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index] at hbad
    omega
  let q : B ≃* Equiv.Perm (Fin 6) :=
    (B.equivMapOfInjective f hinj).trans
      ((MulEquiv.subgroupCongr hR).trans
        (MonoidHom.ofInjective permutationAction_injective).symm)
  have hq (g : B) : permutationAction (q g) = f g := by
    exact congrArg Subtype.val
      ((MonoidHom.ofInjective permutationAction_injective).apply_symm_apply
        (MulEquiv.subgroupCongr hR (B.equivMapOfInjective f hinj g)))
  refine ⟨q, ?_, ?_⟩
  · intro x
    apply permutationAction_injective
    rw [hq, normalConjThrough_coe, permutationAction_coe]
  · intro g x
    have hh := normalConjThrough_apply K e g x
    rw [← hq] at hh
    exact (congrArg Subtype.val hh).symm
end AlternatingSix.SylowCentralExtension
