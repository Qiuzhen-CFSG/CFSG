module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.QuotientAction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.FactorActors
public import Theory.SpecificGroups.SymmetricFourSylow
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The actual dihedral quotient action in 15.4.20

An independent inversion and an arbitrary exchange of two order-three
factors give a noncommutative action image. Preservation of the factor pair
makes that image act faithfully on their four nonidentity elements. It is
therefore a noncommutative two-subgroup of S₄, hence a Sylow subgroup and
isomorphic to the actual `DihedralGroup 4`.

The source adapter obtains the inversion from the full S₃ × S₃ quotient
and the exchange from failure to normalize the chosen factor. All actions
are the actual conjugation action on X/O₂(X). The exchanger may have order
four; no pure-swap coordinates are assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
p.1164, the embedding step in the proof of Lemma 15.4.20.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup

private theorem noncommutative_two_group_four_point
    {D : Type*} [Group D] [Finite D] (hD : IsPGroup 2 D)
    (hn : ¬ IsMulCommutative D)
    (f : D →* Equiv.Perm (Fin 4)) (hf : Function.Injective f) :
    Nonempty (D ≃* DihedralGroup 4) := by
  have hp := hD.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨eP⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four P
  have hcardP : Nat.card P = 8 := by
    rw [Nat.card_congr eP.toEquiv, DihedralGroup.nat_card]
  have hcD : Nat.card D = Nat.card f.range := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
  have hbound : Nat.card D ≤ 8 := hcD ▸ (hcardP ▸ card_le_of_le hP)
  obtain ⟨n, hncard⟩ := IsPGroup.iff_card.mp hD
  have hn3 : n ≤ 3 := by
    by_contra h
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ n)
    omega
  have hc : Nat.card D = 8 := by
    interval_cases n
    · have h1 : Nat.card D = 1 := hncard
      let : Subsingleton D := (Nat.card_eq_one_iff_unique.mp h1).1
      exact (hn ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩).elim
    · let : IsCyclic D := isCyclic_of_prime_card (p := 2) hncard
      exact (hn inferInstance).elim
    · exact (hn (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hncard)).elim
    · exact hncard
  have heq : f.range = (P : Subgroup (Equiv.Perm (Fin 4))) :=
    eq_of_le_of_card_ge hP (by omega)
  exact ⟨((MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr heq)).trans eP⟩

private theorem faithful_action_on_four_points
    {A D : Type*} [Group A] [Group D] [Finite D] [Finite A]
    (hD : IsPGroup 2 D) (hn : ¬ IsMulCommutative D)
    (α : D →* MulAut A) (hinj : Function.Injective α)
    (s : Set A) (hcard : Nat.card s = 4) (hgen : closure s = ⊤)
    (hstable : ∀ d : D, ∀ x ∈ s, α d x ∈ s) :
    Nonempty (D ≃* DihedralGroup 4) := by
  classical
  let f : D →* Equiv.Perm s := {
    toFun := fun d => {
      toFun := fun x => ⟨α d x, hstable d x x.property⟩
      invFun := fun x => ⟨α d⁻¹ x, hstable d⁻¹ x x.property⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
    map_one' := by
      apply Equiv.ext
      intro x
      apply Subtype.ext
      change α 1 x = x
      rw [map_one]
      rfl
    map_mul' := by
      intro d e
      apply Equiv.ext
      intro x
      apply Subtype.ext
      change α (d*e) x = α d (α e x)
      rw [map_mul]
      rfl }
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro d hd
    have hfix : ∀ x ∈ s, α d x = x := by
      intro x hx
      exact congrArg Subtype.val (DFunLike.congr_fun (MonoidHom.mem_ker.mp hd) ⟨x,hx⟩)
    have heq : α d = 1 := by
      apply MulEquiv.ext
      intro x
      have hx : x ∈ closure s := hgen ▸ mem_top x
      exact closure_induction (fun x hx => hfix x hx) (by simp)
        (fun x y _ _ hx hy => by simp [hx,hy])
        (fun x _ hx => by simp [hx]) hx
    exact hinj (heq.trans (map_one α).symm)
  let e : s ≃ Fin 4 := Classical.choice (Finite.card_eq.mp (hcard.trans (Nat.card_fin 4).symm))
  exact noncommutative_two_group_four_point hD hn
    ((Equiv.permCongrHom e).toMonoidHom.comp f) ((Equiv.permCongrHom e).injective.comp hf)

/-- The factor action image is the dihedral group of order eight. -/
theorem dihedral_image_of_factor_exchange {A U : Type*}
    [Group A] [Finite A] [IsMulCommutative A] [Group U] [Finite U]
    (hU : IsPGroup 2 U) (α : U →* MulAut A)
    (A1 A2 : Subgroup A) (hgen : A1 ⊔ A2 = ⊤)
    (hcard1 : Nat.card A1 = 3) (hcard2 : Nat.card A2 = 3) (a b : U)
    (hinvert : ∀ x ∈ A1, α a x = x⁻¹) (hfix : ∀ x ∈ A2, α a x = x)
    (hexchange1 : A1.map (α b).toMonoidHom = A2)
    (hexchange2 : A2.map (α b).toMonoidHom = A1)
    (hperm : ∀ u : U, ∀ B ∈ ({A1,A2} : Set (Subgroup A)),
      B.map (α u).toMonoidHom ∈ ({A1,A2} : Set (Subgroup A))) :
    Nonempty (α.range ≃* DihedralGroup 4) := by
  classical
  let s1 : Set A := (A1 : Set A) \ {1}
  let s2 : Set A := (A2 : Set A) \ {1}
  let s := s1 ∪ s2
  have hs1 : s1.ncard = 2 := by
    rw [Set.ncard_sdiff (by simp : ({1} : Set A) ⊆ A1), Set.ncard_singleton]
    change Nat.card A1 - 1 = 2
    omega
  have hs2 : s2.ncard = 2 := by
    rw [Set.ncard_sdiff (by simp : ({1} : Set A) ⊆ A2), Set.ncard_singleton]
    change Nat.card A2 - 1 = 2
    omega
  have hdis : Disjoint s1 s2 := by
    apply Set.disjoint_left.mpr
    intro x hx1 hx2
    have hx2pow : x*x = 1 := eq_inv_iff_mul_eq_one.mp ((hfix x hx2.1).symm.trans (hinvert x hx1.1))
    have hx3pow : x ^ 3 = 1 := by
      have hh := pow_card_eq_one' (x := (⟨x,hx1.1⟩ : A1))
      rw [hcard1] at hh
      exact congrArg Subtype.val hh
    exact hx1.2 (by simpa only [pow_succ, pow_zero, one_mul, hx2pow, Set.mem_singleton_iff] using hx3pow)
  have hcard : Nat.card s = 4 := by
    change s.ncard = 4
    rw [Set.ncard_union_eq hdis, hs1,hs2]
  have hgens : closure s = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply sup_le
    · intro x hx
      by_cases he : x = 1
      · exact he ▸ (closure s).one_mem
      · exact subset_closure (Or.inl ⟨hx,he⟩)
    · intro x hx
      by_cases he : x = 1
      · exact he ▸ (closure s).one_mem
      · exact subset_closure (Or.inr ⟨hx,he⟩)
  have hstable : ∀ u : U, ∀ x ∈ s, α u x ∈ s := by
    intro u x hx
    have hn : α u x ≠ 1 := fun h => (hx.elim (fun h => h.2) (fun h => h.2)) ((α u).map_eq_one_iff.mp h)
    have hmem (B : Subgroup A) (hB : B ∈ ({A1,A2} : Set (Subgroup A))) (hxB : x ∈ B) :
        α u x ∈ A1 ∨ α u x ∈ A2 := by
      have hh := hperm u B hB
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
      have hxmap : α u x ∈ B.map (α u).toMonoidHom := ⟨x,hxB,rfl⟩
      exact hh.elim (fun h => Or.inl (h ▸ hxmap)) (fun h => Or.inr (h ▸ hxmap))
    have hh : α u x ∈ A1 ∨ α u x ∈ A2 := hx.elim
      (fun h => hmem A1 (by simp) h.1) (fun h => hmem A2 (by simp) h.1)
    exact hh.elim (fun h => Or.inl ⟨h,hn⟩) (fun h => Or.inr ⟨h,hn⟩)
  exact faithful_action_on_four_points
    (hU.of_surjective α.rangeRestrict α.rangeRestrict_surjective)
    (not_commutative_image_of_factor_exchange α A1 A2 hgen hcard1 a b hinvert hfix hexchange1 hexchange2)
    α.range.subtype α.range.subtype_injective s hcard hgens
    (fun d x hx => by
      obtain ⟨u,hu⟩ := d.property
      change (d : MulAut A) x ∈ s
      rw [← hu]
      exact hstable u x hx)

/-- The full source quotient and the moved factor construct the actual D₈ action. -/
theorem contrary_dihedral_from_full_product
    {G : Type*} [Group G] [Finite G]
    (X S U : Subgroup G) (hU : IsPGroup 2 U) (hSU : S ≤ U)
    (hn : U ≤ normalizer (X : Set G))
    (e : (X ⧸ pCore 2 X) ≃* Multiplicative (ZMod 3 × ZMod 3))
    (L : Bool → Subgroup G) (hL : L false ⊔ L true = X)
    (f : (X ⊔ S : Subgroup G) →* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hf : Function.Surjective f) (hker : f.ker = pCore 2 (X ⊔ S : Subgroup G))
    (hf1 : ((L false).subgroupOf (X ⊔ S)).map f = (alternatingGroup (Fin 3)).prod ⊥)
    (hf2 : ((L true).subgroupOf (X ⊔ S)).map f =
      (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3)))
    (hp : ∀ u ∈ U, ∀ V ∈ ({L false, L true} : Set (Subgroup G)),
      V.map (MulAut.conj u).toMonoidHom ∈ ({L false, L true} : Set (Subgroup G)))
    (i : Bool) (hmove : ¬ U ≤ normalizer (L i : Set G)) :
    let α := (quotientAut (pCore 2 X)).comp (X.normalizerMonoidHom.comp (inclusion hn))
    Nonempty (α.range ≃* DihedralGroup 4) := by
  let A1 := ((L false).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
  let A2 := ((L true).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
  let α := (quotientAut (pCore 2 X)).comp (X.normalizerMonoidHom.comp (inclusion hn))
  let : IsElementaryAbelian 3 (X ⧸ pCore 2 X) := (order_nine_quotient_structure e).1
  obtain ⟨hgen,hcard1,hcard2,a,hinv,hfix⟩ :=
    independent_inverter_from_product X S U hSU hn L hL f hf hker hf1 hf2
  obtain ⟨b,hb1,hb2⟩ := quotient_factor_exchange_of_movement X U hn L hL hp i hmove
  have hLX (j : Bool) : L j ≤ X := by cases j <;> simp [← hL]
  have hperm : ∀ u : U, ∀ B ∈ ({A1,A2} : Set (Subgroup (X ⧸ pCore 2 X))),
      B.map (α u).toMonoidHom ∈ ({A1,A2} : Set (Subgroup (X ⧸ pCore 2 X))) := by
    intro u B hB
    have haux (j : Bool) :
        ((((L j).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map (α u).toMonoidHom)
          ∈ ({A1,A2} : Set (Subgroup (X ⧸ pCore 2 X))) := by
      have hh := hp u u.property (L j) (by cases j <;> simp)
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hh ⊢
      rcases hh with hh | hh
      · exact Or.inl (map_quotient_factor X _ _ (hLX j) (hLX false) (inclusion hn u) hh)
      · exact Or.inr (map_quotient_factor X _ _ (hLX j) (hLX true) (inclusion hn u) hh)
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hB
    rcases hB with rfl | rfl
    · exact haux false
    · exact haux true
  exact dihedral_image_of_factor_exchange hU α A1 A2 hgen hcard1 hcard2 a b hinv hfix hb1 hb2 hperm

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
