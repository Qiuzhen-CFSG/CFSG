module
public import Theory.GroupTheory.PushingUp.BaumannBinary.NaturalQuotient
public import Stellmacher.PushingUp.SL2TwoModule
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner
/-!
# The marked Baumann natural quotient at every binary degree

For a field of order two, a maximum abelian subgroup outside the two-core
has nontrivial action on the original Sylow-center closure. Its fixed index
is at least two, so maximum abelian replacement forces the full Sylow fixed
index to be two. The proved degree-one pushing-up module lemma recognizes
the central quotient. Every automorphism of SL₂(2) is inner; correcting its
coordinates therefore retains the originally supplied quotient marking.
Transport along the prime-field isomorphism treats any field of order two.
Together with `NaturalQuotient`, this gives natural coordinates for every
positive binary degree, with kernel exactly V ∩ Z(L).

Source: Delgado–Goldschmidt–Stellmacher, *Groups and Graphs* (1985), (6.3),
printed p.120, and Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (2.1)
in degree one. The independent-universe quadratic-action proof follows
`Stellmacher.PushingUp.SL2TwoNaturalSylow`. The separate assertion
[O₂(L),L] ≤ V remains open; this module proves only the natural-module clause.
The literal adjacent-core application is in
`CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.BaumannApplication.NaturalAll`.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace Theory.GroupTheory.BaumannBinary
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2
private theorem sylow_fixed_index_one (P : Sylow 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hVQ : V ≤ pCore 2 G)
    (q : G →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 G) (hker : q.ker = centralizer (V : Set G))
    (hF : Nat.card F = 2) :
    (centralizer (P : Set G)).relIndex V = Nat.card F := by
  have hQS : pCore 2 G ≤ (P : Subgroup G) := pCore_isPGroup.le_sylow_of_normal P
  have hVc : V ≤ centralizer (pCore 2 G : Set G) :=
    le_centralizer_iff.mp (hk.symm.trans hker).le
  have hindex := Matrix.SpecialLinearGroup.sylow_core_relIndex q hq hk P
  have hSne : (P : Subgroup G) ≠ ⊥ := by
    intro he
    rw [he,relIndex_bot_right,hF] at hindex
    omega
  have hJ := Glauberman.allAbelianThompson_not_le_normal (P : Subgroup G)
    (pCore 2 G) hQS hSne hP
  have hex : ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups (P : Subgroup G) ∧
      ¬ A ≤ pCore 2 G := by
    by_contra! hh
    exact hJ (sSup_le hh)
  obtain ⟨A,hA,hout⟩ := hex
  have hlower : Nat.card F ≤ (centralizer (A : Set G)).relIndex V := by
    have hnz : (centralizer (A : Set G)).relIndex V ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    have hne : (centralizer (A : Set G)).relIndex V ≠ 1 := by
      intro he
      have hc := le_centralizer_iff.mp (relIndex_eq_one.mp he)
      exact hout (hc.trans (hker.symm.trans hk).le)
    omega
  have hlower' : (pCore 2 G).relIndex (P : Subgroup G) ≤
      (V ⊓ centralizer (A : Set G)).relIndex V := by
    rw [hindex,inf_relIndex_left]
    exact hlower
  have hi := (Glauberman.maximum_abelian_saturation hA hQS hVQ inferInstance hVc hlower').1
  have hgen := Glauberman.maximum_abelian_supplements_normal hA hQS hVQ inferInstance hVc
    le_normalizer_of_normal hlower'
  have he : V ⊓ centralizer (P : Set G) = V ⊓ centralizer (A : Set G) := by
    change V ⊓ centralizer ((P : Subgroup G) : Set G) = _
    apply le_antisymm (inf_le_inf_left _ (centralizer_le hA.1))
    intro v hv
    refine ⟨hv.1,?_⟩
    have hh : (P : Subgroup G) ≤ centralizer ({v} : Set G) := by
      rw [←hgen]
      apply sup_le
      · intro a ha z hz
        have hzv : z = v := Set.mem_singleton_iff.mp hz
        subst z
        exact (hv.2 a ha).symm
      · intro a ha z hz
        have hzv : z = v := Set.mem_singleton_iff.mp hz
        subst z
        exact (hVc hv.1 a ha).symm
    intro a ha
    exact (hh ha v (Set.mem_singleton v)).symm
  rw [←inf_relIndex_left,he,hi,hindex]


private theorem sl2_two_aut_inner (α : MulAut SL(2,ZMod 2)) :
    ∃ k, α = MulAut.conj k := by
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  obtain ⟨k,hk⟩ := NormalSymmetricThreePairRank.symmetricThree_aut_inner
    (e.symm.trans (α.trans e))
  refine ⟨e.symm k,?_⟩
  apply MulEquiv.ext
  intro g
  apply e.injective
  have h := DFunLike.congr_fun hk (e g)
  simpa only [MulEquiv.trans_apply,MulEquiv.symm_apply_apply,MulAut.conj_apply,
    map_mul,map_inv,MulEquiv.apply_symm_apply] using h

private theorem nested_two
    {H : Type*} [Group H] [Finite H]
    (e : H ≃* SL(2,ZMod 2)) (hc : pCore 2 H = ⊥)
    (S : Sylow 2 H) (hS : Nat.card S = 2) :
    Stellmacher.IsSL2Two ((H ⧸ pCore 2 H) ⧸ frattini (H ⧸ pCore 2 H)) := by
  have hcard : Nat.card H = 6 :=
    Stellmacher.SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨e⟩
  have hiS : (S : Subgroup H).index = 3 := by
    have hh := (S : Subgroup H).card_mul_index
    rw [hS,hcard] at hh
    omega
  have hPhi : frattini H = ⊥ := by
    have hl := frattini_le_coatom (isCoatom_of_index_three (S : Subgroup H) hiS)
    have hp := S.isPGroup'.to_le hl
    have he : frattini H ≤ pCore 2 H := le_sSup ⟨inferInstance,hp⟩
    exact bot_unique (he.trans hc.le)
  let e₁ : (H ⧸ pCore 2 H) ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hPhi₁ : frattini (H ⧸ pCore 2 H) = ⊥ := by
    apply bot_unique
    have hh := frattini_le_comap_frattini_of_surjective (φ := e₁.toMonoidHom) e₁.surjective
    rw [hPhi] at hh
    exact hh.trans (by simpa using (e₁.toMonoidHom.ker_eq_bot_iff.mpr e₁.injective).le)
  exact show Stellmacher.IsSL2Two
      ((H ⧸ pCore 2 H) ⧸ frattini (H ⧸ pCore 2 H)) from
    ⟨((QuotientGroup.quotientMulEquivOfEq hPhi₁).trans QuotientGroup.quotientBot).trans
      (e₁.trans e)⟩

private theorem quadratic_of_fixed
    {A W : Type*} [Group A] [Group W]
    [MulDistribMulAction A W]
    (hle : commutatorAction A W ≤ FixedPoints.subgroup A W) :
    commutatorAction₂ A W = ⊥ := by
  apply le_antisymm
  · change Subgroup.closure
      {d : W | ∃ a : A, ∃ w : W, w ∈ commutatorAction A W ∧
        d = w⁻¹ * a • w} ≤ ⊥
    apply (Subgroup.closure_le (K := ⊥)).2
    rintro x ⟨a, w, hw, rfl⟩
    have hfix := (FixedPoints.mem_subgroup (M := A) (a := w)).mp
      (hle hw) a
    simp [hfix]
  · exact bot_le

private theorem quadratic_two
    {A W : Type*}
    [Group A] [Finite A] [Group W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction A W]
    (hAcard : Nat.card A = 2) :
    commutatorAction₂ A W = ⊥ := by
  have hfirst : commutatorAction A W ≤ FixedPoints.subgroup A W := by
    rw [commutatorAction_eq_closure]
    refine (Subgroup.closure_le (K := FixedPoints.subgroup A W)).2 ?_
    rintro d ⟨a, w, rfl⟩
    change ∀ b : A, b • (w⁻¹ * a • w) = w⁻¹ * a • w
    intro b
    obtain ⟨t, ht_ne, ht⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hAcard
    have ha : a = 1 ∨ a = t := by
      by_cases ha : a = 1
      · exact Or.inl ha
      · exact Or.inr (ht a ha)
    have hb : b = 1 ∨ b = t := by
      by_cases hb : b = 1
      · exact Or.inl hb
      · exact Or.inr (ht b hb)
    have ht2 : t * t = 1 := by
      by_cases htt_one : t * t = 1
      · exact htt_one
      · have htt := ht (t * t) htt_one
        have ht_one : t = 1 := by
          have heq := congrArg (fun z : A => t⁻¹ * z) htt
          simpa [mul_assoc] using heq
        exact (ht_ne ht_one).elim
    have hw_inv : w⁻¹ = w := by
      apply inv_eq_of_mul_eq_one_left
      simpa [pow_two] using
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 W) w)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · simp
    · simp
    · simp
    · simp only [smul_mul', smul_smul, ht2, one_smul]
      rw [hw_inv]
      exact IsMulCommutative.is_comm.comm _ _
  exact quadratic_of_fixed hfirst

private theorem marked_projection_two
    {H W : Type*} [Group H] [Finite H] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction H W]
    (e : H ≃* SL(2,ZMod 2)) (hc : pCore 2 H = ⊥)
    (S : Sylow 2 H) (hS : Nat.card S = 2)
    (hf : fixingSubgroup H (Set.univ : Set W) = ⊥)
    (hi : Nat.card (W ⧸ FixedPoints.subgroup (S : Subgroup H) W) ≤ 2) :
    ∃ f : Additive W →ₗ[ZMod 2] (Fin 2 → ZMod 2), Function.Surjective f ∧
      (∀ w, f w = 0 ↔ w.toMul ∈ FixedPoints.subgroup H W) ∧
      ∀ g w, f (Additive.ofMul (g • w)) = Matrix.mulVec (e g).val (f (Additive.ofMul w)) := by
  have hcard : Nat.card H = 6 :=
    Stellmacher.SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨e⟩
  have hA := nested_two e hc S hS
  have hne : (S : Subgroup H) ≠ ⊥ := by
    intro he
    have hh : Nat.card (S : Subgroup H) = 1 := Subgroup.card_eq_one.mpr he
    omega
  have hnp : ¬ IsPGroup 2 H := by
    intro hp
    have ht : (⊤ : Subgroup H) ≤ pCore 2 H := le_sSup ⟨inferInstance,hp.to_subgroup ⊤⟩
    have he := le_antisymm (ht.trans hc.le) bot_le
    have hh := Subgroup.card_eq_one.mpr he
    rw [card_top,hcard] at hh
    omega
  have hquad : commutatorAction₂ (S : Subgroup H) W = ⊥ :=
    quadratic_two hS
  obtain ⟨_,_,⟨e',hC,hNat⟩,_⟩ := Stellmacher.PushingUp.sl2Two_module S (S : Subgroup H)
    hf hc hA le_rfl hne hnp hquad (by simpa only [hS] using hi)
  let C := FixedPoints.subgroup H W
  let := quotientMulDistribMulAction C hC
  obtain ⟨E,hE⟩ := hNat
  obtain ⟨k,hk⟩ := sl2_two_aut_inner (e.symm.trans e')
  have he' (g : H) : e' g = k * e g * k⁻¹ := by
    have hh := DFunLike.congr_fun hk (e g)
    simpa only [MulEquiv.trans_apply,MulEquiv.symm_apply_apply,MulAut.conj_apply] using hh
  let f₀ : Additive W →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    (E.toAddMonoidHom.comp (QuotientGroup.mk' C).toAdditive).toZModLinearMap 2
  let K := (Matrix.SpecialLinearGroup.toLin' k⁻¹)
  let f := K.toLinearMap.comp f₀
  have hsur : Function.Surjective f₀ := E.surjective.comp (QuotientGroup.mk'_surjective C)
  refine ⟨f,K.surjective.comp hsur,?_,?_⟩
  · intro w
    change K (E (Additive.ofMul (QuotientGroup.mk' C w.toMul))) = 0 ↔ _
    rw [map_eq_zero_iff K K.injective,map_eq_zero_iff E E.injective]
    exact QuotientGroup.eq_one_iff w.toMul
  · intro g w
    have hh := hE g (QuotientGroup.mk' C w)
    change E (Additive.ofMul (QuotientGroup.mk' C (g • w))) = _ at hh
    change Matrix.mulVec k⁻¹.val (E (Additive.ofMul (QuotientGroup.mk' C (g • w)))) = _
    rw [hh,he']
    change Matrix.mulVec k⁻¹.val (Matrix.mulVec (k * e g * k⁻¹).val _) =
      Matrix.mulVec (e g).val (Matrix.mulVec k⁻¹.val _)
    change Matrix.mulVec k⁻¹.val (Matrix.mulVec (k * e g * k⁻¹).val _) =
      Matrix.mulVec (e g).val (Matrix.mulVec k⁻¹.val (E (Additive.ofMul (QuotientGroup.mk' C w))))
    simp only [Matrix.mulVec_mulVec,←Matrix.SpecialLinearGroup.coe_mul]
    rw [show k⁻¹ * (k * e g * k⁻¹) = e g * k⁻¹ by group]

/-- The degree-one quotient retains the original marking and central kernel. -/
private theorem centerClosure_natural_projection_two (P : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (q : G →* SL(2,ZMod 2)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G) :
    let := (centerClosure_reduced P hc).elementary
    ∃ f : Additive (centerClosure (P : Subgroup G)) →ₗ[ZMod 2] (Fin 2 → ZMod 2),
      Function.Surjective f ∧
      LinearMap.ker f = NormalElementaryQuotient.subspace (centerClosure (P : Subgroup G))
        (((centerClosure (P : Subgroup G)) ⊓ center G).subgroupOf
          (centerClosure (P : Subgroup G))) ∧
      ∀ g v, f (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
        Matrix.mulVec (q g).val (f v) := by
  let := (centerClosure_reduced P hc).elementary
  let V := centerClosure (P : Subgroup G)
  have hker := hk.trans
    (centerClosure_centralizer P hc hP q hq hk (n := 1) (by decide) (by simp)).symm
  let ρ := NormalElementaryQuotient.representation V q hq hker
  let act := MulDistribMulAction.compHom V (NormalElementaryQuotient.conjugationAut V q hq hker)
  let : MulDistribMulAction SL(2,ZMod 2) V := act
  let S := P.mapSurjective hq
  have hS : Nat.card S = 2 := by
    have hh := Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive (ZMod 2) 2 S).toEquiv
    exact hh.symm.trans ((Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 2))
  have hf : fixingSubgroup SL(2,ZMod 2) (Set.univ : Set V) = ⊥ := by
    apply bot_unique
    intro a ha
    have hfix := (mem_fixingSubgroup_iff (M := SL(2,ZMod 2)) (s := Set.univ)).mp ha
    apply (NormalElementaryQuotient.representation_injective V q hq hker)
    rw [map_one]
    apply LinearMap.ext
    intro v
    exact congrArg Additive.ofMul (hfix v.toMul (Set.mem_univ _))
  have hfixed : FixedPoints.subgroup (S : Subgroup SL(2,ZMod 2)) V =
      (centralizer (P : Set G)).subgroupOf V := by
    ext v
    exact NormalElementaryQuotient.mem_fixedSpace_image V q hq hker
      (P : Subgroup G) (Additive.ofMul v)
  have hi : Nat.card (V ⧸ FixedPoints.subgroup (S : Subgroup SL(2,ZMod 2)) V) = 2 := by
    rw [hfixed]
    change (centralizer (P : Set G)).relIndex V = 2
    simpa only [Nat.card_zmod] using sylow_fixed_index_one P hP V
      (centerClosure_reduced P hc).le_pCore q hq hk hker (by simp)
  obtain ⟨f,hsur,hzero,he⟩ := marked_projection_two (MulEquiv.refl _) (Matrix.SL2.twoCore_eq_bot _)
    S hS hf hi.le
  refine ⟨f,hsur,?_,?_⟩
  · rw [←fixedSpace_eq_center P q hq hker]
    ext v
    exact (hzero v).trans (by
      change (∀ a : SL(2,ZMod 2), a • v.toMul = v.toMul) ↔
        ∀ a : (⊤ : Subgroup SL(2,ZMod 2)), ρ a v = v
      constructor
      · intro h a; exact congrArg Additive.ofMul (h a)
      · intro h a; exact congrArg Additive.toMul (h ⟨a,mem_top a⟩))
  · intro g v
    have hact : (q g) • v.toMul = MulAut.conjNormal g v.toMul := by
      apply Subtype.ext
      exact NormalElementaryQuotient.conjugationAut_apply V q hq hker g v.toMul
    rw [←hact]
    exact he (q g) v.toMul

/-- Degree one over the originally supplied field, with the original q. -/
private theorem centerClosure_natural_projection_one (P : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G)
    (hF : Nat.card F = 2) :
    let := (centerClosure_reduced P hc).elementary
    ∃ f : Additive (centerClosure (P : Subgroup G)) →ₗ[ZMod 2] (Fin 2 → F),
      Function.Surjective f ∧
      LinearMap.ker f = NormalElementaryQuotient.subspace (centerClosure (P : Subgroup G))
        (((centerClosure (P : Subgroup G)) ⊓ center G).subgroupOf
          (centerClosure (P : Subgroup G))) ∧
      ∀ g v, f (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
        Matrix.mulVec (q g).val (f v) := by
  let := (centerClosure_reduced P hc).elementary
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let e : SL(2,F) ≃* SL(2,ZMod 2) :=
    { toFun := Matrix.SpecialLinearGroup.map eF.toRingHom
      invFun := Matrix.SpecialLinearGroup.map eF.symm.toRingHom
      left_inv := by intro g; ext i j; exact eF.symm_apply_apply (g i j)
      right_inv := by intro g; ext i j; exact eF.apply_symm_apply (g i j)
      map_mul' := (Matrix.SpecialLinearGroup.map eF.toRingHom).map_mul }
  let q₂ := e.toMonoidHom.comp q
  have hq₂ : Function.Surjective q₂ := e.surjective.comp hq
  have hk₂ : q₂.ker = pCore 2 G := by
    exact (MonoidHom.ker_comp_of_injective q e.toMonoidHom e.injective).trans hk
  obtain ⟨f,hsur,hkernel,he⟩ := centerClosure_natural_projection_two P hc hP q₂ hq₂ hk₂
  let C₀ : (Fin 2 → ZMod 2) →+ (Fin 2 → F) :=
    { toFun := fun v i => eF.symm (v i)
      map_zero' := by ext i; exact map_zero eF.symm
      map_add' := by intro v w; ext i; exact map_add eF.symm (v i) (w i) }
  let C := C₀.toZModLinearMap 2
  have hCi : Function.Injective C := by
    intro v w hh
    ext i
    exact eF.symm.injective (congrFun hh i)
  have hCs : Function.Surjective C := by
    intro v
    refine ⟨fun i => eF (v i),?_⟩
    ext i
    exact eF.symm_apply_apply (v i)
  have hC (g : SL(2,F)) (v : Fin 2 → ZMod 2) :
      C (Matrix.mulVec (e g).val v) = Matrix.mulVec g.val (C v) := by
    ext i
    change eF.symm (∑ j : Fin 2, eF (g i j) * v j) =
      ∑ j : Fin 2, g i j * eF.symm (v j)
    simp only [Fin.sum_univ_two,map_add,map_mul,eF.symm_apply_apply]
  refine ⟨C.comp f,hCs.comp hsur,?_,?_⟩
  · calc
      LinearMap.ker (C.comp f) = LinearMap.ker f := by
        ext v
        exact map_eq_zero_iff C hCi
      _ = _ := hkernel
  · intro g v
    change C (f (Additive.ofMul (MulAut.conjNormal g v.toMul))) = _
    rw [he]
    exact hC (q g) (f v)

/-- Naturality at every positive binary field degree, including one. -/
theorem centerClosure_natural_projection_all (P : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    let := (centerClosure_reduced P hc).elementary
    ∃ f : Additive (centerClosure (P : Subgroup G)) →ₗ[ZMod 2] (Fin 2 → F),
      Function.Surjective f ∧
      LinearMap.ker f = NormalElementaryQuotient.subspace (centerClosure (P : Subgroup G))
        (((centerClosure (P : Subgroup G)) ⊓ center G).subgroupOf
          (centerClosure (P : Subgroup G))) ∧
      ∀ g v, f (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
        Matrix.mulVec (q g).val (f v) := by
  by_cases hn1 : n = 1
  · exact centerClosure_natural_projection_one P hc hP q hq hk (by simpa only [hn1,pow_one] using hF)
  · exact centerClosure_natural_projection P hc hP q hq hk (by omega) hF


/-- The actual quotient by the whole fixed space is natural for the same q. -/
theorem centerClosure_natural_quotient_all (P : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    letI := (centerClosure_reduced P hc).elementary
    let hker := hk.trans (centerClosure_centralizer P hc hP q hq hk hn hF).symm
    let ρ := NormalElementaryQuotient.representation (centerClosure (P : Subgroup G)) q hq hker
    ∃ E : (Additive (centerClosure (P : Subgroup G)) ⧸ fixedSpace ρ ⊤)
        ≃ₗ[ZMod 2] (Fin 2 → F),
      ∀ g v, E (SL2SylowFixedRecognition.centralQuotient ρ g v) = Matrix.mulVec g.val (E v) := by
  let := (centerClosure_reduced P hc).elementary
  let V := centerClosure (P : Subgroup G)
  have hker := hk.trans (centerClosure_centralizer P hc hP q hq hk hn hF).symm
  let ρ := NormalElementaryQuotient.representation V q hq hker
  obtain ⟨f,hsur,hkernel,he⟩ := centerClosure_natural_projection_all P hc hP q hq hk hn hF
  have hK : LinearMap.ker f = fixedSpace ρ ⊤ :=
    hkernel.trans (fixedSpace_eq_center P q hq hker).symm
  let E := (Submodule.quotEquivOfEq _ _ hK.symm).trans (f.quotKerEquivOfSurjective hsur)
  refine ⟨E,?_⟩
  intro g v
  obtain ⟨w,rfl⟩ := (fixedSpace ρ ⊤).mkQ_surjective v
  change f (ρ g w) = Matrix.mulVec g.val (f w)
  obtain ⟨a,rfl⟩ := hq g
  have hact : ρ (q a) w = Additive.ofMul (MulAut.conjNormal a w.toMul) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact NormalElementaryQuotient.representation_apply V q hq hker a w
  rw [hact]
  exact he a w

end Theory.GroupTheory.BaumannBinary
