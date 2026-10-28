module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Sylow
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Factors.Complement

/-!
# The conjugate factors in the swapped-component alternative

Put K = ⟨L^T⟩ and Q = L/O₂(L). The initial four-model list makes Q simple.
The two actual conjugate components then identify K/O₂(K) with Q × Q.
The odd-prime rank bound forces every odd-prime subgroup of Q to be cyclic,
so the complement P embeds in a product of cyclic groups and is abelian.
Its given elementary/extraspecial alternative therefore identifies P with E_(p²).

Choose t in N_T(P) moving L. Projection to the second quotient factor has
kernel P ∩ L: normality of L in K and coprimality lift factor membership
through O₂(K). This intersection cannot be trivial, since its triviality would
embed the noncyclic P in a cyclic p-group. The two conjugate intersections
are disjoint, commute, and have order at least p. Since |P| = p² they generate P.

The final theorem takes only the given swapped Sylow input and the exact
universal A.3.7/A.3.8 implications already used in Section 1.2. The Chapter 1
assembly owner supplies those earlier results. The later model restrictions
and outer-action argument of Proposition 1.3.4(1) remain with that owner.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Proposition 1.2.1(2)–(3), printed pp.503–504, and
the proof of Proposition 1.3.4(1), printed pp.509–510, especially PDF p.527.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
namespace SwappedFactorsProof

private theorem coordinate_right_eq_one {D : Type*} [Group D]
    (A B : Subgroup D) (e : A × B ≃* D)
    (he : ∀ a b, e (a, b) = (a : D) * b) (x : D) :
    (e.symm x).2 = 1 ↔ x ∈ A := by
  constructor
  · intro hx
    have hex : x = ((e.symm x).1 : D) := by
      calc
        x = e (e.symm x) := (e.apply_symm_apply x).symm
        _ = ((e.symm x).1 : D) * ((e.symm x).2 : D) := he _ _
        _ = ((e.symm x).1 : D) := by rw [hx]; simp
    rw [hex]
    exact (e.symm x).1.property
  · intro hx
    have hex : e (⟨x, hx⟩, 1) = x := by simpa using he ⟨x, hx⟩ 1
    rw [← hex, e.symm_apply_apply]

variable {G : Type u} [Group G] [Finite G]
variable {𝒦 : GroupClass.{u}} {p : ℕ} {T X P H L : Subgroup G}

/-- A zero intersection would embed the noncyclic complement into a cyclic
p-subgroup of the other quotient factor. The kernel calculation uses relative
normality in K and the normal two-core lifting lemma. -/
theorem intersection_ne_bot (h : SwappedInput 𝒦 p T X P H L)
    (hr : primeRank p (XiQuotient L × XiQuotient L) ≤ 2)
    {t : G} (ht : t ∈ T)
    (e : SwappedSylow.imageInOrbit L T L ×
      SwappedSylow.imageInOrbit L T (L.conjBy t) ≃* XiQuotient (componentOrbit L T))
    (he : ∀ a b, e (a, b) = (a : XiQuotient (componentOrbit L T)) * b) :
    P ⊓ L ≠ ⊥ := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  let K := componentOrbit L T
  let A := L.subgroupOf K
  let N := pCore 2 K
  let R := P.subgroupOf K
  let Bbar := SwappedSylow.imageInOrbit L T (L.conjBy t)
  let qP : P →* XiQuotient K := (SwappedSylow.imageInOrbit L T P).subtype.comp
    (SwappedSylow.quotientComplementEquiv h).toMonoidHom
  let f : P →* Bbar := (MonoidHom.snd _ _).comp (e.symm.toMonoidHom.comp qP)
  let _ : A.Normal := (normal_subgroupOf_iff_le_normalizer (le_componentOrbit L T)).mpr
    (cComponentOrbit_le_normalizer h.component (le_sup_right.trans h.overgroup))
  have hker : f.ker = L.subgroupOf P := by
    ext x
    change (e.symm (qP x)).2 = 1 ↔ (x : G) ∈ L
    rw [coordinate_right_eq_one _ _ e he]
    constructor
    · intro hx
      exact mem_normal_factor_of_quotient_mem h.odd A N R pCore_isPGroup
        h.odd_complement.isPGroup.comap_subtype
        (show (⟨x, h.complement_le_orbit x.property⟩ : K) ∈ R from x.property) hx
    · intro hx
      exact mem_map_of_mem (QuotientGroup.mk' N)
        (show (⟨x, h.complement_le_orbit x.property⟩ : K) ∈ A from hx)
  let c : L ≃* L.conjBy t := equivMapOfInjective L (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective
  let cq : XiQuotient L ≃* XiQuotient (L.conjBy t) :=
    QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  let b : XiQuotient L ≃* Bbar := cq.trans (componentImageEquiv h
    (conjugate_component h.component ((le_sup_right.trans h.overgroup) ht))
    (le_iSup (fun s : T => L.conjBy s) ⟨t, ht⟩))
  let g := b.symm.toMonoidHom.comp f
  let _ : IsCyclic g.range := cyclic_pSubgroup_of_product_rank h.odd hr _
    (h.odd_complement.isPGroup.of_surjective g.rangeRestrict g.rangeRestrict_surjective)
  intro hbot
  have hk : f.ker = ⊥ := by
    rw [hker, ← inf_subgroupOf_right L P, inf_comm L P, hbot, bot_subgroupOf]
  have hg : Function.Injective g := b.symm.injective.comp ((MonoidHom.ker_eq_bot_iff f).mp hk)
  exact h.complement_not_cyclic (isCyclic_of_injective g.rangeRestrict
    (fun x y hh => hg (congrArg Subtype.val hh)))

omit [Finite G] in
/-- Disjointness of the quotient images lifts on the odd complement, where
the quotient by the two-core is injective. -/
theorem intersections_disjoint (h : SwappedInput 𝒦 p T X P H L)
    {B : Subgroup G}
    (hd : Disjoint (SwappedSylow.imageInOrbit L T L) (SwappedSylow.imageInOrbit L T B)) :
    Disjoint (P ⊓ L) (P ⊓ B) := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  let K := componentOrbit L T
  let q := QuotientGroup.mk' (pCore 2 K)
  have hPN : Disjoint (P.subgroupOf K) (pCore 2 K) :=
    h.odd_complement.isPGroup.comap_subtype.disjoint_of_coprime pCore_isPGroup
      (Nat.coprime_two_right.mpr h.odd)
  apply disjoint_def.mpr
  intro x hx hy
  let xK : K := ⟨x, h.complement_le_orbit hx.1⟩
  have hq : q xK = 1 := hd.le_bot
    ⟨mem_map_of_mem q (show xK ∈ L.subgroupOf K from hx.2),
      mem_map_of_mem q (show xK ∈ B.subgroupOf K from hy.2)⟩
  exact congrArg Subtype.val (hPN.le_bot
    ⟨show xK ∈ P.subgroupOf K from hx.1, (QuotientGroup.eq_one_iff xK).mp hq⟩)

/-- The specified moving conjugate gives the actual internal direct product
of P, including generation, disjointness and commutation. -/
theorem factors_of_index_simple
    (hA37 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK 𝒦 D → pCore 2 D = ⊥ →
      ∀ B C : Subgroup D, B.IsCComponent → C.IsCComponent → B ≠ C → ⁅B, C⁆ = ⊥)
    (h : SwappedInput 𝒦 p T X P H L)
    (hi : (normalizer (L.subgroupOf H : Set H)).index = 2)
    (hs : IsSimpleGroup (XiQuotient L))
    (eqv : XiQuotient (componentOrbit L T) ≃* XiQuotient L × XiQuotient L) :
    Nonempty (P ≃* Plane p) ∧ SwappedFactors T P L := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  have hc := complement_commutative h eqv
  let _ := hc
  have hpCard := (h.toLocalInput.complement_elementary_of_commutative hc).2
  refine ⟨h.toLocalInput.complement_plane_of_commutative hc, h.not_invariant, ?_⟩
  obtain ⟨t, ht, hm⟩ := h.exists_swap
  obtain ⟨e, he⟩ := quotient_product_coordinates hA37 h hi hs ht.1 hm
  have hr : primeRank p (XiQuotient L × XiQuotient L) ≤ 2 := by
    rw [← primeRank_congr p eqv]
    exact (SwappedSylow.orbit_quotient_sqtk h).stronglyQuasithin p h.prime h.odd
  have hne := intersection_ne_bot h hr ht.1 e he
  have hconj : (P ⊓ L).conjBy t = P ⊓ L.conjBy t := by
    change (P ⊓ L).map (MulAut.conj t).toMonoidHom = _
    rw [map_inf _ _ _ (MulAut.conj t).injective]
    change P.conjBy t ⊓ L.conjBy t = P ⊓ L.conjBy t
    rw [show P.conjBy t = P from mem_normalizer_iff_map_conj_eq.mp ht.2]
  have hd : Disjoint (P ⊓ L) ((P ⊓ L).conjBy t) := by
    rw [hconj]
    exact intersections_disjoint h (quotient_factors_disjoint h hs
      (quotient_factors_commute hA37 h ht.1 hm))
  have hBP : (P ⊓ L).conjBy t ≤ P := hconj ▸ inf_le_left
  have hcentral : P ⊓ L ≤ centralizer ((P ⊓ L).conjBy t : Set G) := by
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨b, hBP hb⟩ : P) (⟨a, ha.1⟩ : P))
  have hsizeA : p ≤ Nat.card (P ⊓ L : Subgroup G) := by
    obtain ⟨n, hn⟩ := (h.odd_complement.isPGroup.to_le (show P ⊓ L ≤ P from inf_le_left)).exists_card_eq
    have hn0 : n ≠ 0 := by
      intro hz
      exact hne (card_eq_one.mp (by simpa [hz] using hn))
    rw [hn]
    exact (pow_one p).symm.trans_le (Nat.pow_le_pow_right h.prime.pos (by omega))
  have hsizeB : Nat.card ((P ⊓ L).conjBy t) = Nat.card (P ⊓ L : Subgroup G) :=
    (Nat.card_congr (equivMapOfInjective (P ⊓ L) (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).toEquiv).symm
  obtain ⟨ep, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd hcentral
  have hsize : Nat.card ((P ⊓ L) ⊔ (P ⊓ L).conjBy t : Subgroup G) =
      Nat.card (P ⊓ L : Subgroup G) * Nat.card (P ⊓ L : Subgroup G) := by
    rw [← Nat.card_congr ep.toEquiv, Nat.card_prod, hsizeB]
  have hgen : P = (P ⊓ L) ⊔ (P ⊓ L).conjBy t := by
    apply (eq_of_le_of_card_ge (sup_le inf_le_left hBP) ?_).symm
    rw [hpCard, hsize, pow_two]
    exact Nat.mul_le_mul hsizeA hsizeA
  exact ⟨t, ht, hm, hgen, hd, commutator_eq_bot_iff_le_centralizer.mpr hcentral⟩

end SwappedFactorsProof

namespace SwappedSylow

variable {G : Type u} [Group G] [Finite G]
variable {𝒦 : GroupClass.{u}} {p : ℕ} {T X P H L : Subgroup G}

/-- The complete conjugate-factor and orbit-product conclusions from the
intrinsic swapped Sylow input and the exact universal earlier A.3 inputs. -/
theorem factors_of_A_3_7_A_3_8
    (hA37 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK 𝒦 D → pCore 2 D = ⊥ →
      ∀ B C : Subgroup D, B.IsCComponent → C.IsCComponent → B ≠ C → ⁅B, C⁆ = ⊥)
    (hA38 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK 𝒦 D → pCore 2 D = ⊥ → ∀ B : Subgroup D, B.IsCComponent →
      B.Normal ∨ (normalizer (B : Set D)).index = 2 ∧ Section02.NonnormalCComponentModel B)
    (h : SwappedSylowInput 𝒦 p T X P H L) :
    Nonempty (P ≃* Plane p) ∧ SwappedFactors T P L ∧
      IsSimpleGroup (XiQuotient L) ∧
      Nonempty (XiQuotient (componentOrbit L T) ≃* XiQuotient L × XiQuotient L) := by
  obtain ⟨hi, hm⟩ := nonnormal_model_of_A_3_8 hA38 h.toSwappedInput
  have hs := SwappedFactorsProof.quotient_simple h.toSwappedInput hm
  obtain ⟨eqv⟩ := SwappedFactorsProof.quotient_product hA37 h.toSwappedInput hi hs
  obtain ⟨hp, hf⟩ := SwappedFactorsProof.factors_of_index_simple hA37 h.toSwappedInput hi hs eqv
  exact ⟨hp, hf, hs, ⟨eqv⟩⟩

end SwappedSylow
end CFSG.Quasithin.Chapter1.XiEmbedding
