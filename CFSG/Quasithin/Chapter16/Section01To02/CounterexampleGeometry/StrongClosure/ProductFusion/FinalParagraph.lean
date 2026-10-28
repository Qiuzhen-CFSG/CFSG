module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.LocalFusion
public import Theory.GroupAction.SubgroupConjugation

/-!
# Product fusion after the mixed-involution centralizer bound

This module proves the final paragraph of Aschbacher's Lemma 3.4 from source
(e), global strong closure, and source (g), the centralizer bound for nonidentity
products of factor involutions. Both earlier assertions remain explicit inputs;
no minimal-counterexample result is asserted here.

An outside transporter gives an involution t whose centralizer lies in an
outside conjugate of H. Unique membership for factor elements makes C_A(t)
trivial, so t exchanges the factors. On an elementary four-subgroup of A,
the map x ↦ x xᵗ is then an injective homomorphism into C(t). Its nonidentity
images have centralizers in H by (g). After Sylow conjugacy inside H, a
nonidentity member of this four-group normalizes a conjugate factor and fixes
a nonidentity element there. This contradicts unique membership for that factor.

The injectivity argument uses C_A(t) = 1 directly, so it does not need a
separate identification of the full diagonal centralizer.

Source: M. Aschbacher, *On finite groups of component type*, Illinois J. Math.
19 (1975), Lemma 3.4, final paragraph on p.96, DOI 10.1215/ijm/1256050927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

private theorem fixed_element {A : Subgroup G} (hp : IsPGroup 2 A) (hne : A ≠ ⊥)
    {t : G} (ht : orderOf t = 2) (hn : t ∈ normalizer (A : Set G)) :
    ∃ a ∈ A, a ≠ 1 ∧ a * t = t * a := by
  let T := zpowers t
  have hT : IsPGroup 2 T := IsPGroup.of_card (n := 1) (by simp [T, Nat.card_zpowers, ht])
  let : MulDistribMulAction T A :=
    conjMulDistribMulActionOfLeNormalizer T A (zpowers_le.mpr hn)
  have hd : 2 ∣ Nat.card A := hp.card_eq_or_dvd.resolve_left
    (fun hc => hne (Subgroup.card_eq_one.mp hc))
  obtain ⟨a, ha, hane⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := A) hd
    (show (1 : A) ∈ MulAction.fixedPoints T A by simp [MulAction.mem_fixedPoints])
  refine ⟨a, a.property, fun he => hane (Subtype.ext he.symm), ?_⟩
  have hf := congrArg A.subtype ((MulAction.mem_fixedPoints.mp ha) (⟨t, mem_zpowers t⟩ : T))
  change t * (a : G) * t⁻¹ = (a : G) at hf
  exact (mul_inv_eq_iff_eq_mul.mp hf).symm

omit [Finite G] in
private theorem conjugate_card (A : Subgroup G) (g : G) :
    Nat.card (conjugate A g) = Nat.card A :=
  card_map_of_injective (MulAut.conj g⁻¹).injective

omit [Finite G] in
private theorem conjugate_mono {A B : Subgroup G} (h : A ≤ B) (g : G) :
    conjugate A g ≤ conjugate B g := map_mono h

private theorem factor_permuted {S : Sylow 2 G} {A B : Subgroup G}
    (hA : A ≤ S) (hB : B ≤ S) (hAB : ¬ A ≤ B)
    (hc : IsStronglyClosedSet ((A : Set G) ∪ B) (S : Subgroup G) ⊤)
    {s : G} (hs : s ∈ S) : conjugate A s = A ∨ conjugate A s = B := by
  have hcover (C : Subgroup G) (hC : C ≤ A ∨ C ≤ B) (g : G) (hg : g ∈ S) :
      conjugate C g ≤ A ∨ conjugate C g ≤ B := by
    apply SubgroupClass.subset_union.mp
    rintro _ ⟨c, hcC, rfl⟩
    have hcu : c ∈ (A : Set G) ∪ B := hC.elim (fun h => Or.inl (h hcC)) (fun h => Or.inr (h hcC))
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv] using hc.2 c hcu g (mem_top _) ((S : Subgroup G).mul_mem
      ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hg)
        (hcu.elim (fun h => hA h) (fun h => hB h))) hg)
  rcases hcover A (Or.inl le_rfl) s hs with h | h
  · exact Or.inl (eq_of_le_of_card_ge h (by rw [conjugate_card]))
  · rcases hcover B (Or.inr le_rfl) s⁻¹ ((S : Subgroup G).inv_mem hs) with hk | hk
    · apply Or.inr
      apply le_antisymm h
      have hh := conjugate_mono hk s
      simpa only [conjugate_conjugate, inv_mul_cancel, conjugate_one] using hh
    · have he : conjugate B s⁻¹ = B := eq_of_le_of_card_ge hk (by rw [conjugate_card])
      exfalso
      apply hAB
      have hh := conjugate_mono h s⁻¹
      simpa only [conjugate_conjugate, mul_inv_cancel, conjugate_one, he] using hh

omit [Finite G] in
private theorem four_normalizes {A B E : Subgroup G} (hE : Nat.card E = 4)
    (hp : ∀ v ∈ E, conjugate A v = A ∨ conjugate A v = B) :
    ∃ v ∈ E, v ≠ 1 ∧ v ∈ normalizer (A : Set G) := by
  classical
  by_contra hn
  have htriv (v : E) (hv : conjugate A (v : G) = A) : v = 1 := by
    by_contra hv1
    exact hn ⟨v, v.property, fun he => hv1 (Subtype.ext he),
      (mem_normalizer_iff_conjugate_eq A v).mpr hv⟩
  have hswap (v : E) (hv : v ≠ 1) : conjugate A (v : G) = B :=
    (hp v v.property).resolve_left (fun he => hv (htriv v he))
  have hi : Function.Injective (fun v : E => decide (v = 1)) := by
    intro v w he
    by_cases hv : v = 1
    · have hw : w = 1 := by simpa [hv] using he.symm
      exact hv.trans hw.symm
    · have hw : w ≠ 1 := by simpa [hv] using he.symm
      have hn' : conjugate A ((v : G) * (w : G)⁻¹) = A := by
        rw [← conjugate_conjugate, hswap v hv, ← hswap w hw,
          conjugate_conjugate, mul_inv_cancel, conjugate_one]
      have hh : v * w⁻¹ = 1 := htriv (v * w⁻¹) hn'
      exact mul_inv_eq_one.mp hh
  have hb := Nat.card_le_card_of_injective _ hi
  rw [hE] at hb
  norm_num at hb

omit [Finite G] in
private theorem conjugate_mem {A : Subgroup G} {a g : G} :
    a ∈ conjugate A g ↔ g * a * g⁻¹ ∈ A := by
  constructor
  · rintro ⟨b, hb, he⟩
    have he : g⁻¹ * b * g = a := by simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv] using he
    rw [← he]
    have hh : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
    rw [hh]
    exact hb
  · intro ha
    exact mem_map.mpr ⟨g * a * g⁻¹, ha, by simp [mul_assoc]⟩

private theorem into_sylow {S : Sylow 2 G} {H E : Subgroup G}
    (hSH : (S : Subgroup G) ≤ H) (hE : IsPGroup 2 E) (hEH : E ≤ H) :
    ∃ k ∈ H, conjugate E k ≤ (S : Subgroup G) := by
  have hp : IsPGroup 2 (E.subgroupOf H) :=
    hE.of_equiv (subgroupOfEquivOfLe hEH).symm
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq H Q (S.subtype hSH)
  refine ⟨(k : G)⁻¹, H.inv_mem k.property, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hy : MulAut.conj k (⟨x, hEH hx⟩ : H) ∈ S.subtype hSH := by
    rw [← hk]
    change MulAut.conj k (⟨x, hEH hx⟩ : H) ∈
      (Q : Subgroup H).map (MulAut.conj k).toMonoidHom
    exact mem_map_of_mem _ (hQ hx)
  change (k : G) * x * (k : G)⁻¹ ∈ S at hy
  change (k : G) * x * (k : G)⁻¹ ∈ (S : Subgroup G) at hy
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv] using hy

private theorem four_not_in_conjugate {S : Sylow 2 G} {A B E : Subgroup G}
    (h : Hypotheses S A B)
    (hc : IsStronglyClosedSet ((A : Set G) ∪ B) (S : Subgroup G) ⊤)
    (hAB : ¬ A ≤ B) (hE : Nat.card E = 4)
    (hEsq : ∀ v ∈ E, v ^ 2 = 1)
    (hEC : ∀ v ∈ E, v ≠ 1 → centralizer ({v} : Set G) ≤ intersectionGenerated A B)
    {g : G} (hg : g ∉ intersectionGenerated A B)
    (hEg : E ≤ conjugate (intersectionGenerated A B) g) : False := by
  let H := intersectionGenerated A B
  have hSH : (S : Subgroup G) ≤ H := h.sylow_le_generated_of_closed hc
  have hEp : IsPGroup 2 E := IsPGroup.of_card (hE.trans (by norm_num : 4 = 2 ^ 2))
  have hEgp : IsPGroup 2 (conjugate E g⁻¹) := by
    rw [conjugate, inv_inv]
    exact hEp.map (MulAut.conj g).toMonoidHom
  have hEgH : conjugate E g⁻¹ ≤ H := by
    have hh := conjugate_mono hEg g⁻¹
    simpa only [conjugate_conjugate, mul_inv_cancel, conjugate_one] using hh
  obtain ⟨k, hk, hEk⟩ := into_sylow hSH hEgp hEgH
  let z := k⁻¹ * g
  have hz : z ∉ H := by
    intro hz
    apply hg
    simpa [z] using H.mul_mem hk hz
  have hES : ∀ v ∈ E, z * v * z⁻¹ ∈ S := by
    intro v hv
    have hv' : MulAut.conj g v ∈ conjugate E g⁻¹ := by
      rw [conjugate, inv_inv]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom hv
    have hm := hEk (mem_map_of_mem (MulAut.conj k⁻¹).toMonoidHom hv')
    change z * v * z⁻¹ ∈ (S : Subgroup G)
    simpa [z, MulAut.conj_apply, mul_assoc] using hm
  have hperm : ∀ v ∈ E,
      conjugate (conjugate A z) v = conjugate A z ∨
        conjugate (conjugate A z) v = conjugate B z := by
    intro v hv
    have hh := factor_permuted h.left_le h.right_le hAB hc (hES v hv)
    have he : conjugate (conjugate A (z * v * z⁻¹)) z = conjugate (conjugate A z) v := by
      simp only [conjugate_conjugate]
      congr 1
      group
    rcases hh with hh | hh
    · exact Or.inl (he.symm.trans (congrArg (fun K => conjugate K z) hh))
    · exact Or.inr (he.symm.trans (congrArg (fun K => conjugate K z) hh))
  obtain ⟨v, hv, hv1, hvN⟩ := four_normalizes hE hperm
  have hv2 : orderOf v = 2 := orderOf_eq_prime_iff.mpr ⟨hEsq v hv, hv1⟩
  have hAp : IsPGroup 2 (conjugate A z) := (S.isPGroup'.to_le h.left_le).map _
  have hAne : conjugate A z ≠ ⊥ := by
    intro he
    have hh := congrArg (fun K => conjugate K z⁻¹) he
    simp only [conjugate_conjugate, mul_inv_cancel, conjugate_one] at hh
    exact h.left_ne_bot (by simpa [conjugate] using hh)
  obtain ⟨a, ha, ha1, hav⟩ := fixed_element hAp hAne hv2 hvN
  have haH : a ∈ H := hEC v hv hv1 (mem_centralizer_singleton_iff.mpr hav)
  obtain ⟨b, hb, he⟩ := ha
  have hb1 : b ≠ 1 := by
    intro hb1
    apply ha1
    simpa [hb1] using he.symm
  apply hz
  apply ((h.unique_of_closed hc (Or.inl hb) hb1).2 z).mp
  have hbH : (MulAut.conj z⁻¹).toMonoidHom b ∈ H := he.symm ▸ haH
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv] using hbH


/-- The centralizer assertion (g), before the final fusion argument. -/
def ProductCentralizerInput (A B : Subgroup G) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, orderOf a = 2 → orderOf b = 2 → a * b ≠ 1 →
    centralizer ({a * b} : Set G) ≤ intersectionGenerated A B

/-- Source (e) and (g) imply the final product-fusion assertion. -/
theorem Hypotheses.productFusion_of_closed_of_centralizers {S : Sylow 2 G} {A B : Subgroup G}
    (h : Hypotheses S A B)
    (hc : IsStronglyClosedSet ((A : Set G) ∪ B) (S : Subgroup G) ⊤)
    (hC : ProductCentralizerInput A B) : ProductFusionInput A B := by
  intro a ha b hb ha2 hb2 hab1
  by_cases hAB : A ≤ B
  · exact h.unique_of_closed hc (Or.inr (B.mul_mem (hAB ha) hb)) hab1
  by_cases hBA : B ≤ A
  · exact h.unique_of_closed hc (Or.inl (A.mul_mem ha (hBA hb))) hab1
  have hcomm (x : G) (hx : x ∈ A) (y : G) (hy : y ∈ B) : x * y = y * x :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h.commute hx) y hy).symm
  apply (uniqueConjugateMembership_iff_sylow_transporters
    (h.sylow_le_generated_of_closed hc)
    ((S : Subgroup G).mul_mem (h.left_le ha) (h.right_le hb))).mpr
  intro g htg
  by_contra hg
  let t := g⁻¹ * (a * b) * g
  have hu2 : (a * b) ^ 2 = 1 := by
    rw [(show Commute a b from hcomm a ha b hb).mul_pow]
    simp only [(orderOf_eq_prime_iff.mp ha2).1, (orderOf_eq_prime_iff.mp hb2).1, one_mul]
  have ht2 : orderOf t = 2 := by
    calc
      orderOf t = orderOf (a * b) := by
        simpa only [t, MulAut.conj_apply, inv_inv] using (MulAut.conj g⁻¹).orderOf_eq (a * b)
      _ = 2 := orderOf_eq_prime_iff.mpr ⟨hu2, hab1⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp ht2).1)
  have hCt : centralizer ({t} : Set G) ≤ conjugate (intersectionGenerated A B) g := by
    intro x hx
    apply conjugate_mem.mpr
    apply hC a ha b hb ha2 hb2 hab1
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun y => g * y * g⁻¹) (mem_centralizer_singleton_iff.mp hx)
    calc
      (g * x * g⁻¹) * (a * b) = g * (x * t) * g⁻¹ := by dsimp [t]; group
      _ = g * (t * x) * g⁻¹ := hh
      _ = (a * b) * (g * x * g⁻¹) := by dsimp [t]; group
  have hfixed (x : G) (hx : x ∈ A) (hxt : x * t = t * x) : x = 1 := by
    by_contra hx1
    have hxg := conjugate_mem.mp (hCt (mem_centralizer_singleton_iff.mpr hxt))
    have hh := ((h.unique_of_closed hc (Or.inl hx) hx1).2 g⁻¹).mp (by
      simpa only [inv_inv] using hxg)
    exact hg ((intersectionGenerated A B).inv_mem_iff.mp hh)
  have hswap : conjugate A t = B := by
    rcases factor_permuted h.left_le h.right_le hAB hc htg with hn | hs
    · obtain ⟨x, hx, hx1, hxt⟩ := fixed_element (S.isPGroup'.to_le h.left_le)
        h.left_ne_bot ht2 ((mem_normalizer_iff_conjugate_eq A t).mpr hn)
      exact (hx1 (hfixed x hx hxt)).elim
    · exact hs
  obtain ⟨E, hE, hEsq⟩ := h.left_rank
  let i : E →* G := A.subtype.comp E.subtype
  let j : E →* G := (MulAut.conj t⁻¹).toMonoidHom.comp i
  have hiA (x : E) : i x ∈ A := x.val.property
  have hjB (x : E) : j x ∈ B := by
    rw [← hswap]
    exact mem_map_of_mem _ (hiA x)
  have hisq (x : E) : i x ^ 2 = 1 := by
    rw [← map_pow, hEsq, map_one]
  have hjsq (x : E) : j x ^ 2 = 1 := by
    rw [← map_pow, hEsq, map_one]
  let d : E →* G :=
    { toFun := fun x => i x * j x
      map_one' := by simp only [map_one, one_mul]
      map_mul' := by
        intro x y
        rw [map_mul, map_mul]
        calc
          (i x * i y) * (j x * j y) = i x * (i y * j x) * j y := by group
          _ = i x * (j x * i y) * j y := by rw [hcomm _ (hiA y) _ (hjB x)]
          _ = (i x * j x) * (i y * j y) := by group }
  have hdi : Function.Injective d := by
    apply (injective_iff_map_eq_one d).mpr
    intro x hx
    have hix : (i x)⁻¹ = i x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hisq x)
    have hjx : j x = i x := (eq_inv_of_mul_eq_one_right hx).trans hix
    have hxt : i x * t = t * i x := by
      have hh := congrArg (fun y => t * y) hjx
      simpa only [j, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe, MulAut.conj_apply, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul] using hh
    have hix1 : i x = 1 := hfixed _ (hiA x) hxt
    apply Subtype.ext
    apply Subtype.ext
    exact hix1
  have hdC (x : E) : d x ∈ centralizer ({t} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    change (i x * (t⁻¹ * i x * (t⁻¹)⁻¹)) * t = t * (i x * (t⁻¹ * i x * (t⁻¹)⁻¹))
    simp only [htinv]
    have htt : t * t = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp ht2).1
    calc
      (i x * (t * i x * t)) * t = i x * t * i x := by simp only [mul_assoc, htt, mul_one]
      _ = (t * i x * t) * i x * t := by
        have hh := hcomm _ (hiA x) _ (hjB x)
        change i x * (t⁻¹ * i x * (t⁻¹)⁻¹) = (t⁻¹ * i x * (t⁻¹)⁻¹) * i x at hh
        simpa only [inv_inv, htinv, mul_assoc, htt, mul_one] using congrArg (fun y => y * t) hh
      _ = t * (i x * (t * i x * t)) := by group
  apply four_not_in_conjugate h hc hAB (E := d.range)
      (by
        change Nat.card (Set.range d) = 4
        exact (Nat.card_range_of_injective hdi).trans hE) ?_ ?_ hg ?_
  · rintro v ⟨x, rfl⟩
    rw [← map_pow, hEsq, map_one]
  · rintro v ⟨x, rfl⟩ hv1
    have hx1 : x ≠ 1 := by intro he; subst x; exact hv1 d.map_one
    have hi1 : i x ≠ 1 := by
      intro he
      apply hx1
      apply Subtype.ext
      apply Subtype.ext
      exact he
    have hj1 : j x ≠ 1 := by
      intro he
      apply hi1
      change (MulAut.conj t⁻¹) (i x) = 1 at he
      exact (MulAut.conj t⁻¹).injective (he.trans (map_one _).symm)
    exact hC (i x) (hiA x) (j x) (hjB x)
      (orderOf_eq_prime_iff.mpr ⟨hisq x, hi1⟩)
      (orderOf_eq_prime_iff.mpr ⟨hjsq x, hj1⟩) hv1
  · rintro v ⟨x, rfl⟩
    exact hCt (hdC x)


/-- Apply the final product paragraph to the actual local-fusion consumer.
The minimal-counterexample argument must still establish source (e) and (g). -/
theorem Hypotheses.fusionConclusion_of_closed_of_productCentralizers
    {S : Sylow 2 G} {A B : Subgroup G} (h : Hypotheses S A B)
    (hc : IsStronglyClosedSet ((A : Set G) ∪ B) (S : Subgroup G) ⊤)
    (hC : ProductCentralizerInput A B) : FusionConclusion S A B :=
  fusionConclusion_of_productFusion h hc (h.productFusion_of_closed_of_centralizers hc hC)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
