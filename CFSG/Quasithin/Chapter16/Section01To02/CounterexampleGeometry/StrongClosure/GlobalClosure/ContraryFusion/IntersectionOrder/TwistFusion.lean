module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.IntersectionOrder.Structure

/-!
# The twist and the order-two intersection

With the outside involution v supplied explicitly, put t = aᵍ, choose the
unique fixed involution z of A₁ ∩ A₂, and put x = vvᵗ. The four-group
⟨v,z⟩ cannot lie in an outside conjugate of the intersection-generated H.
Sylow conjugacy inside H places the two-subgroup ⟨t,x,z⟩ in S after a
coordinate change q outside H; strong closure inside H keeps tᑫ in the
union of the two factors. This implements the source's placement in a
conjugate Sylow without selecting a preferred factor for a.

In these coordinates, both x and z exchange the factors, while xz normalizes
them. The identity (txz)ᵛ = tz and the normalizer clause of (*) exclude all
fusion of tz into either factor. Both possible memberships of txz are
handled using the fact that t belongs to the factor intersection.

Finally the intersection is abelian. The displacement homomorphism c ↦ c⁻¹cᵗ
has nontrivial two-group image if the intersection exceeds its fixed subgroup.
The action of t inverts that image, so its involution is fixed and must be z.
Thus t would be conjugate to tz, contradicting the preceding nonfusion.
This proves the final step without additional facts about the standard models.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, from “So we may choose v to be an involution” through
“A₁ ∩ A₂ = ⟨z⟩”. DOI: 10.1215/ijm/1256050927.
-/

@[expose] public section
open scoped Pointwise
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

private theorem into_sylow {H E : Subgroup G}
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
  change (k : G) * x * (k : G)⁻¹ ∈ (S : Subgroup G) at hy
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.conj_apply, inv_inv] using hy

omit [Finite G] in
private theorem commute_factors (h : Hypotheses S A₁ A₂) {a b : G}
    (ha : a ∈ A₁) (hb : b ∈ A₂) : Commute a b :=
  (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h.commute ha) b hb).symm

omit [Finite G] in
private theorem normalizes_of_union (h : Hypotheses S A₁ A₂) {a : G}
    (ha : a ∈ (A₁ : Set G) ∪ A₂) : a ∈ normalizer (A₁ : Set G) := by
  rcases ha with ha | ha
  · exact A₁.le_normalizer ha
  · apply Subgroup.centralizer_le_normalizer
    intro b hb
    exact (commute_factors h hb ha).eq

/-- The pair action forces the twist outside both factors and excludes all its fusion. -/
private theorem twist_nonfusion (h : Hypotheses S A₁ A₂) (l : LocalControl S A₁ A₂)
    {t v x z : G} (htU : t ∈ (A₁ : Set G) ∪ A₂) (ht1 : t ≠ 1)
    (hxS : x ∈ S) (hzS : z ∈ S) (hz1 : z ≠ 1)
    (hvH : v ∉ intersectionGenerated A₁ A₂)
    (hvz : Commute v z) (hzt : Commute z t)
    (hvxz : Commute v (x * z)) (hxz1 : x * z ≠ 1)
    (hzf : ∃ b ∈ (A₁ : Set G) ∪ A₂, ∃ q : G, q⁻¹ * b * q = z)
    (htv : v⁻¹ * t * v = t * x)
    (hyv : v⁻¹ * (t * x * z) * v = t * z) :
    ∀ b ∈ (A₁ : Set G) ∪ A₂, ∀ q : G, q⁻¹ * b * q ≠ t * z := by
  let N := normalizer (A₁ : Set G)
  have htS : t ∈ S := htU.elim (fun ht => h.left_le ht) (fun ht => h.right_le ht)
  have htN : t ∈ N := normalizes_of_union h htU
  have hzN : z ∉ N := by
    intro hzN
    obtain ⟨b, hb, q, hq⟩ := hzf
    have hzU : z ∈ (A₁ : Set G) ∪ A₂ := by
      rw [← hq]
      apply h.closed_in_left_normalizer.2 b hb q (mem_top _)
      change _ ∈ (S : Subgroup G) ∧ _ ∈ normalizer (A₁ : Set G)
      rw [hq]
      exact ⟨hzS, hzN⟩
    exact hvH (h.centralizer_le_generated hzU hz1
      (mem_centralizer_singleton_iff.mpr hvz.eq))
  have hxN : x ∉ N := by
    intro hxN
    apply hvH
    apply h.transporter_mem_of_left_normalizer htU ht1
    rw [htv]
    exact ⟨(S : Subgroup G).mul_mem htS hxS, N.mul_mem htN hxN⟩
  have hzswap : conjugate A₁ z = A₂ ∧ conjugate A₂ z = A₁ := by
    rcases l.permutes_pair z hzS with hn | hs
    · exact (hzN ((mem_normalizer_iff_conjugate_eq _ _).mpr hn.1)).elim
    · exact hs
  have hxswap : conjugate A₁ x = A₂ ∧ conjugate A₂ x = A₁ := by
    rcases l.permutes_pair x hxS with hn | hs
    · exact (hxN ((mem_normalizer_iff_conjugate_eq _ _).mpr hn.1)).elim
    · exact hs
  have hxzN : x * z ∈ N := by
    apply (mem_normalizer_iff_conjugate_eq _ _).mpr
    rw [← conjugate_conjugate, hxswap.1, hzswap.2]
  have htcap : t ∈ A₁ ⊓ A₂ := by
    have he : z⁻¹ * t * z = t := by rw [mul_assoc, ← hzt.eq, inv_mul_cancel_left]
    rcases htU with ht | ht
    · refine ⟨ht, ?_⟩
      rw [← hzswap.1]
      exact mem_map.mpr ⟨t, ht, by simpa using he⟩
    · refine ⟨?_, ht⟩
      rw [← hzswap.2]
      exact mem_map.mpr ⟨t, ht, by simpa using he⟩
  have hyN : t * x * z ∈ N := by
    rw [mul_assoc]
    exact N.mul_mem htN hxzN
  have hyS : t * x * z ∈ S :=
    (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem htS hxS) hzS
  have hyU : t * x * z ∉ (A₁ : Set G) ∪ A₂ := by
    intro hy
    have hxzU : x * z ∈ (A₁ : Set G) ∪ A₂ := by
      rcases hy with hy | hy
      · left
        simpa only [SetLike.mem_coe, mul_assoc, inv_mul_cancel_left] using
          A₁.mul_mem (A₁.inv_mem htcap.1) hy
      · right
        simpa only [SetLike.mem_coe, mul_assoc, inv_mul_cancel_left] using
          A₂.mul_mem (A₂.inv_mem htcap.2) hy
    exact hvH (h.centralizer_le_generated hxzU hxz1
      (mem_centralizer_singleton_iff.mpr hvxz.eq))
  intro b hb q hq
  apply hyU
  have he : (q * v⁻¹)⁻¹ * b * (q * v⁻¹) = t * x * z := by
    calc
      _ = v * (q⁻¹ * b * q) * v⁻¹ := by group
      _ = v * (t * z) * v⁻¹ := by rw [hq]
      _ = t * x * z := by rw [← hyv]; group
  have hy := h.closed_in_left_normalizer.2 b hb (q * v⁻¹) (mem_top _) (by
    rw [he]
    exact ⟨hyS, hyN⟩)
  rwa [he] at hy

private theorem eq_one_or_eq_of_mem_zpowers_two {z u : G}
    (hz : orderOf z = 2) (hu : u ∈ zpowers z) : u = 1 ∨ u = z := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hz] at hu
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hu
  have hn2 := Finset.mem_range.mp hn
  have hh : n = 0 ∨ n = 1 := by omega
  rcases hh with rfl | rfl
  · exact Or.inl (by simpa using he.symm)
  · exact Or.inr (by simpa using he.symm)

/-- A nontrivial involutory action with a unique fixed involution produces its twist. -/
private theorem fixed_involution_fused (C : Subgroup G) (hP : IsPGroup 2 C)
    (hcomm : ∀ c ∈ C, ∀ d ∈ C, Commute c d) {t z : G}
    (ht2 : orderOf t = 2) (hz2 : orderOf z = 2)
    (hn : ∀ c ∈ C, t⁻¹ * c * t ∈ C)
    (hfix : C ⊓ centralizer ({t} : Set G) = zpowers z)
    (hne : C ≠ zpowers z) :
    ∃ c ∈ C, c⁻¹ * t * c = t * z := by
  let : CommGroup C := { (inferInstance : Group C) with
    mul_comm := fun c d => Subtype.ext (hcomm c c.property d d.property).eq }
  let f : C →* C := {
    toFun c := ⟨t⁻¹ * (c : G) * t, hn c c.property⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' c d := by apply Subtype.ext; simp [mul_assoc] }
  have htt : t * t = 1 := by simpa only [pow_two, ht2] using pow_orderOf_eq_one t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  have hff (c : C) : f (f c) = c := by
    apply Subtype.ext
    change t⁻¹ * (t⁻¹ * (c : G) * t) * t = (c : G)
    rw [hti]
    calc
      _ = (t * t) * (c : G) * (t * t) := by group
      _ = c := by rw [htt]; simp
  let d : C →* C := {
    toFun c := c⁻¹ * f c
    map_one' := by simp
    map_mul' c e := by simp only [map_mul, mul_inv_rev]; ac_rfl }
  have hdne : d.range ≠ ⊥ := by
    intro hd
    apply hne
    apply le_antisymm ?_ (by rw [← hfix]; exact inf_le_left)
    intro c hc
    have hd1 : d (⟨c, hc⟩ : C) = 1 := by
      have hh : d (⟨c, hc⟩ : C) ∈ d.range := ⟨_, rfl⟩
      rwa [hd, mem_bot] at hh
    have hfc : f (⟨c, hc⟩ : C) = ⟨c, hc⟩ := by
      change (⟨c, hc⟩ : C)⁻¹ * f ⟨c, hc⟩ = 1 at hd1
      exact (inv_mul_eq_one.mp hd1).symm
    rw [← hfix]
    refine ⟨hc, mem_centralizer_singleton_iff.mpr ?_⟩
    have he : t⁻¹ * c * t = c := congrArg Subtype.val hfc
    have hh := congrArg (fun y => t * y) he
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh
  let : Nontrivial d.range := (nontrivial_iff_ne_bot _).mpr hdne
  have hdp : IsPGroup 2 d.range := hP.to_subgroup _
  obtain ⟨n, hnpos, hncard⟩ := hdp.nontrivial_iff_card.mp inferInstance
  obtain ⟨u, hu2⟩ := exists_prime_orderOf_dvd_card' (G := d.range) 2 (by
    rw [hncard]
    exact dvd_pow_self 2 (Nat.ne_of_gt hnpos))
  obtain ⟨c, hc⟩ := u.property
  have hfu : f (u : C) = (u : C)⁻¹ := by
    rw [← hc]
    change f (c⁻¹ * f c) = (c⁻¹ * f c)⁻¹
    rw [map_mul, map_inv, hff]
    simp only [mul_inv_rev, inv_inv]
  have huinv : (u : C)⁻¹ = u := by
    have husq : (u : C) * (u : C) = 1 := by
      have hh := pow_orderOf_eq_one u
      rw [hu2, pow_two] at hh
      exact congrArg Subtype.val hh
    exact inv_eq_of_mul_eq_one_left husq
  have huG2 : orderOf ((u : C) : G) = 2 := by
    simpa only [Subgroup.orderOf_coe] using hu2
  have huZ : ((u : C) : G) ∈ zpowers z := by
    rw [← hfix]
    refine ⟨(u : C).property, mem_centralizer_singleton_iff.mpr ?_⟩
    have he : t⁻¹ * ((u : C) : G) * t = ((u : C) : G) :=
      congrArg Subtype.val (hfu.trans huinv)
    have hh := congrArg (fun y => t * y) he
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh
  have huz : ((u : C) : G) = z := by
    rcases eq_one_or_eq_of_mem_zpowers_two hz2 huZ with hu | hu
    · rw [hu, orderOf_one] at huG2
      omega
    · exact hu
  have hzct : Commute z t := mem_centralizer_singleton_iff.mp
    ((show z ∈ C ⊓ centralizer ({t} : Set G) by rw [hfix]; exact mem_zpowers z).2)
  refine ⟨c, c.property, ?_⟩
  have he : (c : G)⁻¹ * (t⁻¹ * (c : G) * t) = z :=
    (congrArg (fun y : C => (y : G)) hc).trans huz
  have hh := congrArg (fun y => y * t) he
  rw [hti] at hh
  have hfinal : (c : G)⁻¹ * t * c = z * t := by
    simpa only [mul_assoc, htt, mul_one] using hh
  exact hfinal.trans hzct.eq

/-- The last intersection calculation on printed p.95, with its outside involution explicit. -/
theorem MinimalCounterexample.intersection_card_two_of_contrary_of_left_involution
    (m : MinimalCounterexample S A₁ A₂) (l : LocalControl S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha2 : orderOf a = 2)
    (hg : g ∉ intersectionGenerated A₁ A₂) (ht : g⁻¹ * a * g ∈ S)
    (hcap : A₁ ⊓ A₂ ≠ ⊥) (v : G) (hv : v ∈ A₁) (hvout : v ∉ A₂)
    (hv2 : orderOf v = 2) : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2 := by
  let h := m.setup
  let H := intersectionGenerated A₁ A₂
  let C := A₁ ⊓ A₂
  let t := g⁻¹ * a * g
  have ha1 : a ≠ 1 := by intro he; simp [he] at ha2
  have ht2 : orderOf t = 2 := by
    simpa only [t, MulAut.conj_apply, inv_inv] using (MulAut.conj g⁻¹).orderOf_eq a |>.trans ha2
  have htt : t * t = 1 := by simpa only [pow_two, ht2] using pow_orderOf_eq_one t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  have hvv : v * v = 1 := by simpa only [pow_two, hv2] using pow_orderOf_eq_one v
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_left hvv
  obtain ⟨z, hz2, hzC, hzt, hfix⟩ := l.exists_intersection_fixed_involution h ha ha2 hg ht hcap
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz2
  have hs := l.swap_of_outside_transporter h ha ha1 hg ht
  have hvt : t⁻¹ * v * t ∈ A₂ := by
    rw [← hs.1]
    exact mem_map.mpr ⟨v, hv, by simp [t, mul_assoc]⟩
  let x := v * (t⁻¹ * v * t)
  have hvvt := commute_factors h hv hvt
  have hvz := commute_factors h hv hzC.2
  have hvx : Commute v x := (Commute.refl v).mul_right hvvt
  have htv : v⁻¹ * t * v = t * x := by
    have hh := congrArg (fun y => t * y) hvvt.symm.eq
    dsimp [x]
    rw [hti, hvi]
    simpa only [hti, ← mul_assoc, htt, one_mul] using hh
  have hxt : Commute x t := by
    change x * t = t * x
    rw [← htv]
    dsimp [x]
    rw [hti, hvi]
    simp only [mul_assoc, htt, mul_one]
  have hyv : v⁻¹ * (t * x * z) * v = t * z := by
    rw [← htv]
    calc
      _ = (v⁻¹ * v⁻¹) * t * (v * z * v) := by group
      _ = t * z := by
        rw [hvi, hvv, one_mul]
        rw [hvz.eq]
        simp only [mul_assoc, hvv, mul_one]
  have hxz1 : x * z ≠ 1 := by
    intro he
    have hxA₂ : x ∈ A₂ := by
      have hxe : x = z⁻¹ := by
        calc
          x = (x * z) * z⁻¹ := by group
          _ = z⁻¹ := by rw [he]; simp
      rw [hxe]
      exact A₂.inv_mem hzC.2
    apply hvout
    have hh := A₂.mul_mem hxA₂ (A₂.inv_mem hvt)
    simpa only [x, mul_assoc, mul_inv_cancel, mul_one] using hh
  -- Clause (c) will exclude the image of this four-group from H.
  let W := zpowers v ⊔ zpowers z
  have hWA : W ≤ A₁ := sup_le (zpowers_le.mpr hv) (zpowers_le.mpr hzC.1)
  have hzout : z ∉ zpowers v := by
    intro hh
    rcases eq_one_or_eq_of_mem_zpowers_two hv2 hh with he | he
    · exact hz1 he
    · exact hvout (he ▸ hzC.2)
  have hW4 : Nat.card W = 4 := by
    have hzn : z ∈ normalizer (zpowers v : Set G) := by
      apply Subgroup.centralizer_le_normalizer
      rintro y ⟨n, rfl⟩
      exact (hvz.zpow_left n).eq
    rw [card_sup_zpowers_of_normalizing_involution (zpowers v) z
      (hz2 ▸ pow_orderOf_eq_one z) hzout hzn, Nat.card_zpowers, hv2]
  -- Place the commuting configuration in S via H, keeping q outside H.
  let E := (zpowers t ⊔ zpowers x) ⊔ zpowers z
  have htE : t ∈ E := (le_sup_left : zpowers t ⊔ zpowers x ≤ E)
    ((le_sup_left : zpowers t ≤ zpowers t ⊔ zpowers x) (mem_zpowers t))
  have hxE : x ∈ E := (le_sup_left : zpowers t ⊔ zpowers x ≤ E)
    ((le_sup_right : zpowers x ≤ zpowers t ⊔ zpowers x) (mem_zpowers x))
  have hzE : z ∈ E := (le_sup_right : zpowers z ≤ E) (mem_zpowers z)
  have hxS : x ∈ S := (S : Subgroup G).mul_mem (h.left_le hv) (h.right_le hvt)
  have hES : E ≤ (S : Subgroup G) :=
    sup_le (sup_le (zpowers_le.mpr ht) (zpowers_le.mpr hxS)) (zpowers_le.mpr (h.left_le hzC.1))
  have hEC : E ≤ centralizer ({t} : Set G) :=
    sup_le (sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxt.eq)))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hzt.eq))
  have hEgH : conjugate E g⁻¹ ≤ H := by
    rintro _ ⟨u, hu, rfl⟩
    apply h.centralizer_le_generated ha ha1
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp (hEC hu))
    simpa [t, MulAut.conj_apply, mul_assoc] using hh
  have hEgP : IsPGroup 2 (conjugate E g⁻¹) :=
    (S.isPGroup'.to_le hES).map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
  obtain ⟨k, hk, hEk⟩ := into_sylow (l.sylow_le_generated h) hEgP hEgH
  let q := g⁻¹ * k
  let e := MulAut.conj q⁻¹
  have hq : q ∉ H := by
    intro hq
    have hgi : g⁻¹ ∈ H := by
      simpa only [q, mul_assoc, mul_inv_cancel, mul_one] using H.mul_mem hq (H.inv_mem hk)
    exact hg (H.inv_mem_iff.mp hgi)
  have hEq : conjugate E q ≤ (S : Subgroup G) := by
    simpa only [conjugate_conjugate] using hEk
  have heS (u : G) (hu : u ∈ E) : e u ∈ S :=
    hEq (mem_map.mpr ⟨u, hu, rfl⟩)
  have hte : e t = k⁻¹ * a * k := by simp [e, q, t, MulAut.conj_apply, mul_assoc]
  have htU : e t ∈ (A₁ : Set G) ∪ A₂ := by
    rw [hte]
    apply h.closed_in_generated.2 a ha k hk
    exact ⟨H.mul_mem (H.mul_mem (H.inv_mem hk) (h.union_subset_generated ha)) hk,
      hte ▸ heS t htE⟩
  have hvnot : e v ∉ H := by
    intro hvH
    have hzH : e z ∈ H := l.sylow_le_generated h (heS z hzE)
    have hWq : conjugate W q ≤ H := by
      change W.map e.toMonoidHom ≤ H
      apply map_le_iff_le_comap.mpr
      exact sup_le (zpowers_le.mpr hvH) (zpowers_le.mpr hzH)
    exact hq ((l.unique_large W (Or.inl hWA) (by rw [hW4]; decide)).2 q |>.mp hWq)
  have hnf := twist_nonfusion h l htU
    (by intro he; have hh := e.injective (he.trans e.map_one.symm); simp [hh] at ht2)
    (heS x hxE) (heS z hzE)
    (by intro he; exact hz1 (e.injective (he.trans e.map_one.symm))) hvnot
    (hvz.map e.toMonoidHom) (hzt.map e.toMonoidHom)
    (by simpa only [map_mul, MulEquiv.coe_toMonoidHom] using (hvx.mul_right hvz).map e.toMonoidHom)
    (by intro he; exact hxz1 (e.injective ((e.map_mul x z).trans he |>.trans e.map_one.symm)))
    (by exact ⟨z, Or.inl hzC.1, q, by simp [e]⟩)
    (by simpa only [map_mul, map_inv] using congrArg e htv)
    (by simpa only [map_mul, map_inv] using congrArg e hyv)
  -- A larger abelian intersection would supply the forbidden fusion t ∼ tz.
  have hCeq : C = zpowers z := by
    by_contra hne
    have hcomm : ∀ c ∈ C, ∀ d ∈ C, Commute c d :=
      fun _ hc _ hd => commute_factors h hc.1 hd.2
    have hn : ∀ c ∈ C, t⁻¹ * c * t ∈ C := by
      intro c hc
      constructor
      · rw [← hs.2]
        exact mem_map.mpr ⟨c, hc.2, by simp [t, mul_assoc]⟩
      · rw [← hs.1]
        exact mem_map.mpr ⟨c, hc.1, by simp [t, mul_assoc]⟩
    obtain ⟨c, _, hc⟩ := fixed_involution_fused C (S.isPGroup'.to_le (inf_le_left.trans h.left_le))
      hcomm ht2 hz2 hn hfix hne
    exact hnf (e t) htU (e c) (by simpa only [map_mul, map_inv] using congrArg e hc)
  change Nat.card C = 2
  rw [hCeq, Nat.card_zpowers, hz2]

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
