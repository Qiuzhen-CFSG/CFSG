module
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Simplicity.NormalExclusion
public import BenderSuzuki.SE.StrongEmbeddingConjugacy

/-!
# The proper involution-supplement branch of GLS Lemma 4.9

Let A be a normal simple subgroup and let H = A⟨z⟩. Its distinguished
closure L is normal in H. Simplicity of A makes the inverse image of L
in A either trivial or all of A. The first case makes z centralize A;
single-class generation and the trivial solvable radical exclude it.
Thus L=H. If H were proper, the supplied local strong embedding would
give one involution class in L. An involution of the even-order subgroup A
would then be conjugate to z, placing z in A and forcing A=G.

This route uses the local strong-embedding premise already available to
the source consumer. It avoids a separate analysis of the smaller-group
rank-one and structural alternatives, without assuming either outcome.
The normal-subgroup exclusion is an independent input, discharged by
NormalExclusion in the final Lemma 4.9 assembly.
Source: GLS, Volume 4, Chapter 2, Lemma 4.9, proper A⟨z⟩ branch.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
private theorem normal_eq_top_of_class_mem
    (hgen : closure Z = ⊤) (hclass : ∀ x ∈ Z, ∀ z ∈ Z, IsConj x z)
    {z : G} (hz : z ∈ Z) (N : Subgroup G) [N.Normal] (hzN : z ∈ N) : N = ⊤ := by
  apply top_unique
  rw [← hgen]
  apply (closure_le _).mpr
  intro x hx
  obtain ⟨g, hg⟩ := isConj_iff.mp (hclass z hz x hx)
  rw [← hg]
  exact (inferInstance : N.Normal).conj_mem z hzN g

omit [Finite G] in
private theorem not_centralizes_normal_simple
    (hgen : closure Z = ⊤) (hclass : ∀ x ∈ Z, ∀ z ∈ Z, IsConj x z)
    (hrad : solvableRadical G = ⊥) {z : G} (hz : z ∈ Z)
    (A : Subgroup G) [A.Normal] [IsSimpleGroup A] :
    z ∉ centralizer (A : Set G) := by
  intro hzc
  have hC := normal_eq_top_of_class_mem hgen hclass hz (centralizer (A : Set G)) hzc
  have hs : Group.IsSolvable A := Group.isSolvable_of_comm fun a b => Subtype.ext
    ((mem_centralizer_iff.mp (show (a : G) ∈ centralizer (A : Set G) by rw [hC]; trivial)
      (b : G) b.property).symm)
  have hA : A = ⊥ := bot_unique (hrad ▸ le_solvableRadical A inferInstance hs)
  exact (A.nontrivial_iff_ne_bot.mp inferInstance) hA

omit [Finite G] in
private theorem distinguished_closure_in_sup_eq_top
    (h : IsProductDisconnected Z M) (hgen : closure Z = ⊤)
    (hclass : ∀ x ∈ Z, ∀ z ∈ Z, IsConj x z) (hrad : solvableRadical G = ⊥)
    {z : G} (hz : z ∈ Z) (A : Subgroup G) [A.Normal] [IsSimpleGroup A] :
    let H := A ⊔ zpowers z
    closure (H.subtype ⁻¹' Z) = ⊤ := by
  let H := A ⊔ zpowers z
  let L := closure (H.subtype ⁻¹' Z)
  let i : A →* H := inclusion (show A ≤ H from le_sup_left)
  let zH : H := ⟨z, (show zpowers z ≤ H from le_sup_right) (mem_zpowers z)⟩
  have hzL : zH ∈ L := subset_closure hz
  let : L.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    apply le_normalizer_closure_iff.mpr
    intro g _ x hx
    exact subset_closure (h.invariant (g : G) (x : G) hx)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L.comap i) inferInstance with hb | ht
  · exfalso
    apply not_centralizes_normal_simple hgen hclass hrad hz A
    rw [mem_centralizer_iff]
    intro a ha
    let c : A := ⟨z * a * z⁻¹ * a⁻¹,
      A.mul_mem ((inferInstance : A.Normal).conj_mem a ha z) (A.inv_mem ha)⟩
    have hc : c ∈ L.comap i := by
      change i c ∈ L
      have hm := L.mul_mem hzL ((inferInstance : L.Normal).conj_mem
        zH⁻¹ (L.inv_mem hzL) (i ⟨a, ha⟩))
      have he : i c = zH * (i ⟨a, ha⟩ * zH⁻¹ * (i ⟨a, ha⟩)⁻¹) := by
        apply Subtype.ext
        change z * a * z⁻¹ * a⁻¹ = z * (a * z⁻¹ * a⁻¹)
        group
      rw [he]
      exact hm
    have hc1 : c = 1 := mem_bot.mp (hb ▸ hc)
    have he : z * a * z⁻¹ * a⁻¹ = 1 := congrArg Subtype.val hc1
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp he)).symm
  · have hAL : A ≤ L.map H.subtype := by
      intro a ha
      refine ⟨i ⟨a, ha⟩, ?_, rfl⟩
      change (⟨a, ha⟩ : A) ∈ L.comap i
      rw [ht]
      trivial
    have hZL : zpowers z ≤ L.map H.subtype :=
      zpowers_le.mpr ⟨zH, hzL, rfl⟩
    have hmap : L.map H.subtype = H :=
      le_antisymm (map_subtype_le _) (sup_le hAL hZL)
    apply map_injective H.subtype_injective
    rw [← MonoidHom.range_eq_map, range_subtype]
    exact hmap

/-- A normal simple subgroup, together with a distinguished involution,
generates G under the source local-embedding hypotheses. -/
public theorem simple_normal_sup_zpowers_eq_top
    (h : IsProductDisconnected Z M) (hgen : closure Z = ⊤)
    (hclass : ∀ x ∈ Z, ∀ z ∈ Z, IsConj x z) (hrad : solvableRadical G = ⊥)
    (hnormal : ∀ N : Subgroup G, N.Normal → N ≤ M → N = ⊥)
    (hlocal : ∀ H : Subgroup G, H ≠ ⊤ → ¬ H ≤ M →
      (∃ s ∈ Z, s ∈ H ∧ s ∈ M) →
      IsStronglyEmbedded ((M.comap H.subtype).comap
        (closure (H.subtype ⁻¹' Z)).subtype))
    {z : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (A : Subgroup G) [A.Normal] [IsSimpleGroup A] : A ⊔ zpowers z = ⊤ := by
  by_contra hproper
  let H := A ⊔ zpowers z
  let L := closure (H.subtype ⁻¹' Z)
  have hAH : A ≤ H := le_sup_left
  have hzH : z ∈ H := (show zpowers z ≤ H from le_sup_right) (mem_zpowers z)
  have hAne : A ≠ ⊥ := A.nontrivial_iff_ne_bot.mp inferInstance
  have hnotM : ¬ H ≤ M := fun hh => hAne (hnormal A inferInstance (hAH.trans hh))
  have hL : L = ⊤ := distinguished_closure_in_sup_eq_top h hgen hclass hrad hz A
  have hs := hlocal H hproper hnotM ⟨z, hz, hzH, hzM⟩
  have hAeven := even_card_of_nontrivial_normal_of_radicalFree hrad A hAne
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 hAeven.two_dvd
  have hai : PFAppendixIII.IsInvolution a := by
    obtain ⟨ha2, hane⟩ := (orderOf_eq_prime_iff (p := 2)).mp ha
    exact ⟨hane, ha2⟩
  let aH : H := ⟨a, hAH a.property⟩
  let aL : L := ⟨aH, by rw [hL]; trivial⟩
  let zL : L := ⟨⟨z, hzH⟩, subset_closure hz⟩
  have haL : PFAppendixIII.IsInvolution aL := by
    refine ⟨?_, ?_⟩
    · intro he
      apply hai.ne_one
      apply Subtype.ext
      exact congrArg (fun x : L => ((x : H) : G)) he
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : A => (x : G)) hai.sq_eq_one
  have hzL : PFAppendixIII.IsInvolution zL := by
    refine ⟨fun he => (h.involutions z hz).ne_one
      (congrArg (fun x : L => ((x : H) : G)) he), ?_⟩
    exact Subtype.ext (Subtype.ext (h.involutions z hz).sq_eq_one)
  obtain ⟨g, hg⟩ := hs.involutions_conjugate haL hzL
  have he : ((g : H) : G)⁻¹ * (a : G) * ((g : H) : G) = z :=
    congrArg (fun x : L => ((x : H) : G)) hg
  have hzA : z ∈ A := by
    rw [← he]
    simpa only [inv_inv] using (inferInstance : A.Normal).conj_mem
      (a : G) a.property (((g : H) : G)⁻¹)
  have hAtop := normal_eq_top_of_class_mem hgen hclass hz A hzA
  exact hproper (by rw [hAtop, top_sup_eq])

end BenderSuzuki.ZD
