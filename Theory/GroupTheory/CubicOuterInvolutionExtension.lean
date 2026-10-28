module
public import Theory.GroupTheory.GeneralizedFitting.CoprimeOuterSupplement
public import Theory.GroupTheory.PerfectCentralCoverOuter

/-!
# Involutions in proper extensions with cubic diagonal outer image

Suppose the outer group of a finite model is the union of a three-subgroup
and its coset by a specified involution. That involution generates an outer
Sylow two-subgroup. Sylow conjugacy aligns every proper two-extension above
Inn with the literal inner-and-involution join. A faithful generalized
Fitting action then pulls the specified involution back into the original
group, retaining its exact action after a change of model equivalence.

The argument abstracts the checked PSL₃ proof in
`Theory.SpecificGroups.PSL3.OddPrimeGraphExtension` for reuse with PSU₃.
Source: GLS3 2.5.12 and Aschbacher–Smith F.6.18(11), printed p.310.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.CubicOuterInvolutionExtension
theorem twoSylow_of_cubic_normal_form {Q : Type*} [Group Q]
    (D : Subgroup Q) (hD : IsPGroup 3 D) (b : Q) (hb : b ^ 2 = 1)
    (hnf : ∀ x : Q, ∃ d ∈ D, x = d ∨ x = d * b) :
    ∃ S : Sylow 2 Q, (S : Subgroup Q) = zpowers b := by
  have hC : IsPGroup 2 (zpowers b) := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hb)
  refine ⟨{ toSubgroup := zpowers b, isPGroup' := hC, is_maximal' := ?_ }, rfl⟩
  intro P hP hCP
  apply le_antisymm _ hCP
  intro x hx
  have hdis : ∀ {d : Q}, d ∈ D → d ∈ P → d = 1 := Subgroup.disjoint_def.mp (hD.disjoint_of_coprime hP (by decide))
  obtain ⟨d, hd, h | h⟩ := hnf x
  · have hd1 : d = 1 := hdis hd (h ▸ hx)
    simp [h, hd1]
  · have hbP : b ∈ P := hCP (mem_zpowers b)
    have hdP : d ∈ P := by
      have := P.mul_mem hx (P.inv_mem hbP)
      simpa only [h, mul_inv_cancel_right] using this
    have hd1 : d = 1 := hdis hd hdP
    simpa only [h, hd1, one_mul] using mem_zpowers b


variable {L : Type*} [Group L] [Finite L]

@[expose] def involutionExtension (γ : MulAut L) : Subgroup (MulAut L) :=
  MulAut.innerSubgroup L ⊔ zpowers γ

lemma eq_one_or_eq_of_mem_zpowers {Q : Type*} [Group Q] [Finite Q]
    {b x : Q} (hb : b ^ 2 = 1) (hx : x ∈ zpowers b) : x = 1 ∨ x = b := by
  obtain ⟨n, rfl⟩ := (isOfFinOrder_of_finite b).mem_powers_iff_mem_zpowers.mpr hx
  clear hx
  induction n with
  | zero => exact Or.inl (pow_zero b)
  | succ n ih =>
    change b ^ n = 1 ∨ b ^ n = b at ih
    change b ^ (n + 1) = 1 ∨ b ^ (n + 1) = b
    rcases ih with h | h
    · exact Or.inr (by rw [pow_succ, h, one_mul])
    · exact Or.inl (by rw [pow_succ, h, ← pow_two, hb])

lemma eq_extension_of_inner_lt (γ : MulAut L) (hγ : γ ^ 2 = 1)
    {H : Subgroup (MulAut L)} (hinner : MulAut.innerSubgroup L < H)
    (hH : H ≤ involutionExtension γ) : H = involutionExtension γ := by
  apply le_antisymm hH
  apply sup_le hinner.le
  apply zpowers_le.mpr
  obtain ⟨x, hx, hxi⟩ := SetLike.exists_of_lt hinner
  obtain ⟨i, hi, c, hc, he⟩ := mem_sup_of_normal_left.mp (hH hx)
  rcases eq_one_or_eq_of_mem_zpowers hγ hc with h | h
  · have : x = i := by simpa [h] using he.symm
    exact (hxi (this ▸ hi)).elim
  · have hic : i * γ ∈ H := by
      rw [← he, h] at hx
      exact hx
    have := H.mul_mem (H.inv_mem (hinner.le hi)) hic
    simpa only [inv_mul_cancel_left] using this

lemma exists_conjugate_eq_extension (γ : MulAut L) (hγ : γ ^ 2 = 1)
    (D : Subgroup (MulAut.Outer L)) (hD : IsPGroup 3 D)
    (hnf : ∀ x : MulAut.Outer L, ∃ d ∈ D, x = d ∨
      x = d * QuotientGroup.mk' (MulAut.innerSubgroup L) γ)
    (H : Subgroup (MulAut L)) (hinner : MulAut.innerSubgroup L < H)
    (hH : IsPGroup 2 (H.map (QuotientGroup.mk' (MulAut.innerSubgroup L)))) :
    ∃ a : MulAut L, H.map (MulAut.conj a).toMonoidHom = involutionExtension γ := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup L)
  obtain ⟨S, hS⟩ := twoSylow_of_cubic_normal_form D hD (q γ)
    (by rw [← map_pow, hγ, map_one]) hnf
  obtain ⟨P, hP⟩ := hH.exists_le_sylow
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq (MulAut.Outer L) P S
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup L) b
  change q a = b at ha
  have hm : (H.map (MulAut.conj a).toMonoidHom).map q ≤ zpowers (q γ) := by
    calc
      _ = (H.map q).map (MulAut.conj b).toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
        ext x
        simp [ha]
      _ ≤ (P : Subgroup _).map (MulAut.conj b).toMonoidHom := map_mono hP
      _ = (S : Subgroup _) := congrArg Sylow.toSubgroup hb
      _ = _ := hS
  have hc : (zpowers (q γ)).comap q = involutionExtension γ := by
    rw [← MonoidHom.map_zpowers, comap_map_eq, QuotientGroup.ker_mk', sup_comm]
    rfl
  refine ⟨a, eq_extension_of_inner_lt γ hγ ?_ (hc ▸ map_le_iff_le_comap.mp hm)⟩
  have hn := normal_iff_map_conj_eq.mp (inferInstance : (MulAut.innerSubgroup L).Normal) a
  rw [← hn]
  refine lt_iff_le_not_ge.mpr ⟨map_mono hinner.le, ?_⟩
  intro he
  apply hinner.not_ge
  have he' := Subgroup.map_le_map_iff.mp he
  simpa only [(MulAut.conj a).toMonoidHom.ker_eq_bot (MulAut.conj a).injective,
    sup_bot_eq] using he'

/-- An actual proper extension with cubic diagonal outer image contains a
marked outside involution, after changing the model equivalence. -/
theorem exists_marked_involution {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (hZ : center K = ⊥)
    (hF : generalizedFitting G = K) (T : Sylow 2 G)
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hproper : K ≠ ⊤)
    (e : K ≃* L) (γ : MulAut L) (hγ : γ ^ 2 = 1)
    (D : Subgroup (MulAut.Outer L)) (hD : IsPGroup 3 D)
    (hnf : ∀ x : MulAut.Outer L, ∃ d ∈ D, x = d ∨
      x = d * QuotientGroup.mk' (MulAut.innerSubgroup L) γ) :
    ∃ t : G, orderOf t = 2 ∧ t ∉ K ∧ K ⊔ zpowers t = ⊤ ∧
      ∃ j : K ≃* L, ∀ x : K, j (MulAut.conjNormal t x) = γ (j x) := by
  have hc : centralizer (K : Set G) = ⊥ := by
    subst K
    exact centralizer_generalizedFitting_eq_bot_of_centerless_supplement T hgen hZ
  let f : G →* MulAut L :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : G →* MulAut K)
  have hf : Function.Injective f := (MulAut.congr e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot K hc)
  have hmap : K.map f = MulAut.innerSubgroup L := by
    have hn : K.map (MulAut.conjNormal : G →* MulAut K) = MulAut.innerSubgroup K := by
      ext a
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, MulAut.conjNormal_val.symm⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.property, MulAut.conjNormal_val⟩
    dsimp only [f]
    rw [← Subgroup.map_map, hn, MulAut.map_innerSubgroup_congr]
  let H := f.range
  have hinner : MulAut.innerSubgroup L < H := by
    refine lt_iff_le_not_ge.mpr ⟨?_, ?_⟩
    · rw [← hmap]
      exact K.map_le_range f
    · intro h
      apply hproper
      apply top_unique
      have hm : (⊤ : Subgroup G).map f ≤ K.map f := by
        rw [← MonoidHom.range_eq_map, hmap]
        exact h
      have ht := Subgroup.map_le_map_iff.mp hm
      simpa only [f.ker_eq_bot hf, sup_bot_eq] using ht
  have hH : H = MulAut.innerSubgroup L ⊔ (T : Subgroup G).map f := by
    have hm := congrArg (Subgroup.map f) hgen
    rw [Subgroup.map_sup, hmap, ← MonoidHom.range_eq_map] at hm
    exact hm.symm
  have htwo : IsPGroup 2 (H.map (QuotientGroup.mk' (MulAut.innerSubgroup L))) := by
    rw [hH, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq, Subgroup.map_map]
    exact T.isPGroup'.map _
  obtain ⟨a, ha⟩ := exists_conjugate_eq_extension γ hγ D hD hnf H hinner htwo
  let f' : G →* MulAut L := (MulAut.conj a).toMonoidHom.comp f
  have hf' : Function.Injective f' := (MulAut.conj a).injective.comp hf
  have hr : f'.range = involutionExtension γ := by
    dsimp only [f']
    rw [MonoidHom.range_comp]
    exact ha
  have hmap' : K.map f' = MulAut.innerSubgroup L := by
    dsimp only [f']
    rw [← Subgroup.map_map, hmap]
    exact normal_iff_map_conj_eq.mp inferInstance a
  obtain ⟨t, ht⟩ : ∃ t : G, f' t = γ := by
    have hm : γ ∈ f'.range := hr ▸ mem_sup_right (mem_zpowers γ)
    exact hm
  have htgen : K ⊔ zpowers t = ⊤ := by
    apply (Subgroup.map_injective hf')
    rw [Subgroup.map_sup, hmap', MonoidHom.map_zpowers, ht,
      ← MonoidHom.range_eq_map, hr]
    rfl
  have htout : t ∉ K := by
    intro htK
    exact hproper ((sup_eq_left.mpr (zpowers_le.mpr htK)).symm.trans htgen)
  have ht2 : t ^ 2 = 1 := hf' (by rw [map_pow, ht, hγ, map_one])
  refine ⟨t, orderOf_eq_prime_iff.mpr ⟨ht2, fun h => htout (h ▸ one_mem _)⟩,
    htout, htgen, e.trans a, ?_⟩
  intro x
  have hh := congrArg (fun b : MulAut L => b (a (e x))) ht
  change a (e (MulAut.conjNormal t (e.symm (a.symm (a (e x)))))) = γ (a (e x)) at hh
  simpa only [MulEquiv.trans_apply, a.symm_apply_apply, e.symm_apply_apply] using hh

end Theory.GroupTheory.CubicOuterInvolutionExtension
