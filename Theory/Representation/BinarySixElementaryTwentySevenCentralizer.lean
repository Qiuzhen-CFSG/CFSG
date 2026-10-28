module
public import Theory.Representation.BinarySixThreeRank
public import Theory.GroupTheory.Perm.PrimeDegreeNormalizer
public import Theory.ElementaryAbelian.Join
public import Theory.GroupAction.AbelianCoprimeFixedGeneration
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The centralizer of an elementary 27-group in a binary six-space

An elementary abelian subgroup of order 27 in a faithful binary action of
degree at most six is self-centralizing. Coprime fixed-point splitting and
small general-linear orders show that its common fixed space is zero and
that every cyclic-quotient fixed factor has order at most four. These factors
generate the module. On a four-element factor, a nontrivial cubic action
permutes the three nonidentity elements regularly, so every commuting
automorphism has cube one. Adjoining a centralizing element to the original
27-group would therefore contradict the binary degree-six three-rank bound.

This is the elementary-core centralizer input in Aschbacher--Smith G.9.4,
printed p.355. It needs neither normality nor irreducibility.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Representation.BinarySixElementaryTwentySevenCentralizer

private instance elementary_subgroup
    {E : Type*} [Group E] [IsElementaryAbelian 2 E] (D : Subgroup E) :
    IsElementaryAbelian 2 D where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom D.subtype D.subtype_injective).trans
    (IsElementaryAbelian.exponent_dvd_p 2 E)

private theorem not_nine_dvd_small_binary_aut
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 8) : ¬ 9 ∣ Nat.card (MulAut E) := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hnle : n ≤ 3 := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    rw [←hn] at hp
    norm_num at hp
    omega
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E n hn]
  interval_cases n <;> decide

private theorem not_twentyseven_dvd_small_binary_aut
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 32) : ¬ 27 ∣ Nat.card (MulAut E) := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hnle : n ≤ 5 := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    rw [←hn] at hp
    norm_num at hp
    omega
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E n hn]
  interval_cases n <;> decide

private theorem faithful_on_commutator
    {E A : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    [Group A] [Finite A] [MulDistribMulAction A E] [FaithfulSMul A E]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card E)) :
    letI : IsInvariant A E (commutatorAction A E) := commutatorAction_isInvariant
    Function.Injective (MulDistribMulAction.toMulAut A (commutatorAction A E)) := by
  let : IsInvariant A E (commutatorAction A E) := commutatorAction_isInvariant
  let f := MulDistribMulAction.toMulAut A (commutatorAction A E)
  have hcompl := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (Group.isSolvable_of_comm (fun a b : E => mul_comm a b)) hcop inferInstance
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply eq_bot_iff.mpr
  intro a ha
  apply mem_bot.mpr
  apply eq_of_smul_eq_smul (M := A) (α := E)
  intro x
  obtain ⟨y,hy,z,hz,rfl⟩ := Subgroup.mem_sup.mp
    (show x ∈ FixedPoints.subgroup A E ⊔ commutatorAction A E by
      rw [hcompl.sup_eq_top]; trivial)
  have hzfix : a • z = z :=
    congrArg Subtype.val (MulEquiv.congr_fun (MonoidHom.mem_ker.mp ha) ⟨z,hz⟩)
  simp only [smul_mul',hy a,hzfix,one_smul]

private theorem fixed_times_moved
    {E A : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    [Group A] [Finite A] [MulDistribMulAction A E]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card E)) :
    Nat.card (FixedPoints.subgroup A E) * Nat.card (commutatorAction A E) = Nat.card E := by
  have hcompl := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (Group.isSolvable_of_comm (fun a b : E => mul_comm a b)) hcop inferInstance
  have hh := card_sup_eq_mul_of_normalizes_of_disjoint
    (FixedPoints.subgroup A E) (commutatorAction A E)
    (by rw [normalizer_eq_top]; exact le_top) hcompl.disjoint
  rw [hcompl.sup_eq_top,card_top] at hh
  exact hh.symm

private theorem common_fixed_eq_bot
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 64) (A : Subgroup (MulAut E))
    [IsElementaryAbelian 3 A] (hA : Nat.card A = 27) :
    FixedPoints.subgroup A E = ⊥ := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (Nat.card E) := by
    rw [hA,hn]
    exact ((by decide : Nat.Coprime (3^3) 2).pow_right n)
  have hprod := fixed_times_moved hcop
  by_contra hne
  have hlo : 2 ≤ Nat.card (FixedPoints.subgroup A E) := by
    have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    omega
  have hC : Nat.card (commutatorAction A E) ≤ 32 := by nlinarith
  let : IsInvariant A E (commutatorAction A E) := commutatorAction_isInvariant
  have hd := card_dvd_of_injective (MulDistribMulAction.toMulAut A (commutatorAction A E))
    (faithful_on_commutator hcop)
  rw [hA] at hd
  exact not_twentyseven_dvd_small_binary_aut hC hd

private theorem hyperplane_fixed_card_le_four
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 64) (A : Subgroup (MulAut E))
    [IsElementaryAbelian 3 A] (hA : Nat.card A = 27)
    (K : Subgroup A) (hK : IsCyclic (A ⧸ K)) :
    Nat.card (FixedPoints.subgroup K E) ≤ 4 := by
  have hquot : Nat.card (A ⧸ K) ≤ 3 := by
    apply Nat.le_of_dvd (by decide)
    rw [← hK.exponent_eq_card]
    exact (Group.exponent_quotient_dvd K).trans
      (IsElementaryAbelian.exponent_dvd_p 3 A)
  have hKbound : 9 ≤ Nat.card K := by
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    rw [hA] at hh
    nlinarith
  have hpK := (IsElementaryAbelian.isPGroup 3 A).to_subgroup K
  obtain ⟨k,hk⟩ := hpK.exists_card_eq
  have h9 : 9 ∣ Nat.card K := by
    have hkle : 2 ≤ k := by
      by_contra! hh
      have hp := Nat.pow_le_pow_right (by decide : 0 < 3) (show k ≤ 1 by omega)
      rw [←hk] at hp
      norm_num at hp
      omega
    rw [hk]
    exact pow_dvd_pow 3 hkle
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hcop : Nat.Coprime (Nat.card K) (Nat.card E) := by
    rw [hk,hn]
    exact ((by decide : Nat.Coprime 3 2).pow_left k).pow_right n
  obtain ⟨d,hd⟩ := (IsElementaryAbelian.isPGroup 2 (FixedPoints.subgroup K E)).exists_card_eq
  have hprod := fixed_times_moved hcop
  by_contra hlarge
  have hdl : 3 ≤ d := by
    by_contra hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show d ≤ 2 by omega)
    rw [←hd] at hp
    exact hlarge hp
  have hlo : 8 ≤ Nat.card (FixedPoints.subgroup K E) := by
    rw [hd]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hdl
  have hC : Nat.card (commutatorAction K E) ≤ 8 := by nlinarith
  let : IsInvariant K E (commutatorAction K E) := commutatorAction_isInvariant
  exact not_nine_dvd_small_binary_aut hC
    (h9.trans (card_dvd_of_injective (MulDistribMulAction.toMulAut K (commutatorAction K E))
      (faithful_on_commutator hcop)))


private def nonidentityPerm {E : Type*} [Group E] :
    MulAut E →* Equiv.Perm {x : E // x ≠ 1} where
  toFun a := a.toEquiv.subtypeEquiv (fun x => by simp)
  map_one' := by ext x; rfl
  map_mul' := by intro a b; ext x; rfl

private theorem nonidentityPerm_injective {E : Type*} [Group E] :
    Function.Injective (nonidentityPerm (E := E)) := by
  intro a b he
  ext x
  by_cases hx : x = 1
  · simp [hx]
  · exact congrArg Subtype.val (DFunLike.congr_fun he ⟨x,hx⟩)

private theorem four_commuting_cubic_pow
    {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 4)
    (a r : MulAut E) (hr : r^3=1) (hrne : r≠1) (hc : Commute a r) : a^3=1 := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let X := {x : E // x ≠ 1}
  have hX : Nat.card X = 3 := by
    have hh := Fintype.card_subtype_compl (fun x : E => x=1)
    simp only [Fintype.card_unique] at hh
    simpa only [Nat.card_eq_fintype_card,X,←Nat.card_eq_fintype_card,hE] using hh
  let e : X ≃ Fin 3 := (Finite.equivFin X).trans (Equiv.cast (congrArg Fin hX))
  let f : MulAut E →* Equiv.Perm (Fin 3) :=
    (Equiv.permCongrHom e).toMonoidHom.comp nonidentityPerm
  have hf : Function.Injective f := (Equiv.permCongrHom e).injective.comp nonidentityPerm_injective
  have hrc : orderOf r = 3 := orderOf_eq_prime hr hrne
  have ha : a ∈ zpowers r := by
    rw [←Theory.GroupTheory.centralizer_eq_zpowers_of_prime_degree Nat.prime_three f hf r hrc]
    exact mem_centralizer_singleton_iff.mpr hc.eq
  have hdiv : orderOf a ∣ 3 := by
    simpa only [Nat.card_zpowers,hrc] using (zpowers r).orderOf_dvd_natCard ha
  exact orderOf_dvd_iff_pow_eq_one.mp hdiv

private theorem centralizer_cube
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 64) (A : Subgroup (MulAut E))
    [IsElementaryAbelian 3 A] (hA : Nat.card A = 27)
    (c : MulAut E) (hc : c ∈ centralizer (A : Set (MulAut E))) : c^3=1 := by
  classical
  let : CommGroup A := IsMulCommutative.instCommGroup
  let : Fact (IsPGroup 2 E) := ⟨IsElementaryAbelian.isPGroup 2 E⟩
  have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup
    (G := E) (A := A) (q := 2)
    (show Nat.Coprime (Nat.card A) 2 by rw [hA]; decide)
  have hfix (K : Subgroup A) (hK : IsCyclic (A ⧸ K))
      (x : E) (hx : x ∈ FixedPoints.subgroup K E) : (c^3) x=x := by
    let F := FixedPoints.subgroup K E
    have hsmall := hyperplane_fixed_card_le_four hE A hA K hK
    change Nat.card F ≤ 4 at hsmall
    have hstable (a : A) (x : E) (hx : x ∈ F) : a • x ∈ F := by
      intro k
      change (k : A) • (a • x) = a • x
      rw [←mul_smul,mul_comm (k : A),mul_smul]
      exact congrArg (fun y : E => a • y) (hx k)
    let : IsInvariant A E F := ⟨fun a x => ⟨hstable a x, fun hh => by
      have hh := hstable a⁻¹ (a • x) hh
      simpa only [inv_smul_smul] using hh⟩⟩
    have hstableC (b : MulAut E) (hb : b ∈ centralizer (A : Set (MulAut E)))
        (x : E) (hx : x ∈ F) : b x ∈ F := by
      intro k
      have he := MulEquiv.congr_fun ((mem_centralizer_iff.mp hb) k.val k.val.property) x
      change (k.val.val : MulAut E) (b x) = b x
      exact he.trans (congrArg b (hx k))
    let a : MulAut F := {
      toFun := fun x => ⟨c x,hstableC c hc x x.property⟩
      invFun := fun x => ⟨c⁻¹ x,hstableC c⁻¹ (inv_mem hc) x x.property⟩
      left_inv := fun x => Subtype.ext (c.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (c.apply_symm_apply x)
      map_mul' := fun x y => Subtype.ext (c.map_mul x y) }
    have ha : a^3=1 := by
      obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 F).exists_card_eq
      have hnle : n ≤ 2 := by
        by_contra! hh
        have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
        rw [←hn] at hp
        norm_num at hp
        omega
      by_cases hn2 : n=2
      · have hF : Nat.card F = 4 := by rw [hn,hn2]; decide
        let f := MulDistribMulAction.toMulAut A F
        have hex : ∃ r : A, f r≠1 := by
          by_contra! hh
          have hbot : F=⊥ := by
            apply le_bot_iff.mp
            rw [←common_fixed_eq_bot hE A hA]
            intro y hy r
            exact congrArg Subtype.val (MulEquiv.congr_fun (hh r) ⟨y,hy⟩)
          rw [hbot,card_bot] at hF
          omega
        obtain ⟨r,hr⟩ := hex
        refine four_commuting_cubic_pow hF a (f r) ?_ hr ?_
        · have hr3 : r^3=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 3 A) r
          rw [←map_pow,hr3,map_one]
        · apply MulEquiv.ext
          intro y
          apply Subtype.ext
          exact (MulEquiv.congr_fun ((mem_centralizer_iff.mp hc) r r.property) y).symm
      · have hAut : Nat.card (MulAut F) = 1 := by
          rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow F n hn]
          interval_cases n <;> first | decide | omega
        let : Subsingleton (MulAut F) := (Nat.card_eq_one_iff_unique.mp hAut).1
        exact Subsingleton.elim _ _
    have hh := congrArg Subtype.val (MulEquiv.congr_fun ha ⟨x,hx⟩)
    change c (c (c x)) = x at hh
    simpa only [pow_succ,pow_zero,MulAut.mul_apply,MulAut.one_apply] using hh
  let D := (c^3).toMonoidHom.eqLocus (MonoidHom.id E)
  have htop : D=⊤ := by
    apply top_unique
    rw [←hgen]
    exact iSup₂_le fun K hK x hx => hfix K hK x hx
  apply MulEquiv.ext
  intro x
  exact (show x ∈ D from htop ▸ mem_top x)


/-- An elementary abelian subgroup of order 27 is self-centralizing in any
faithful binary representation of dimension at most six. -/
theorem centralizer_le
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V ≤ 6)
    (B : Subgroup G) [IsElementaryAbelian 3 B] (hB : Nat.card B = 27) :
    centralizer (B : Set G) ≤ B := by
  let E := Multiplicative V
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 E := BinaryGroupAction.elementary
  have hE : Nat.card E ≤ 64 := by
    change Nat.card V ≤ 64
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hd
  let := BinaryGroupAction.action ρ
  let f : G →* MulAut E := MulDistribMulAction.toMulAut G E
  have hf' : Function.Injective f := by
    intro g k he
    apply hf
    ext v
    exact congrArg Multiplicative.toAdd
      (MulEquiv.congr_fun he (Multiplicative.ofAdd v))
  let : IsElementaryAbelian 3 (B.map f) := IsElementaryAbelian.map (A := B) f
  have hBf : Nat.card (B.map f) = 27 := by rw [card_map_of_injective hf',hB]
  have hrank := BinarySixThreeRank.primeRank_three_le_three ρ hf hd
  intro g hg
  have hgcentral : f g ∈ centralizer (B.map f : Set (MulAut E)) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨b,hb,rfl⟩
    simpa only [map_mul] using congrArg f ((mem_centralizer_iff.mp hg) b hb)
  have hg3 : g^3=1 := by
    apply hf'
    rw [map_pow,map_one]
    exact centralizer_cube hE (B.map f) hBf (f g) hgcentral
  let : IsElementaryAbelian 3 (zpowers g) := IsElementaryAbelian.zpowers_of_pow_eq_one hg3
  let : IsElementaryAbelian 3 (B ⊔ zpowers g : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hg)
  have hcard := (primeRank_le_iff_elementary_card_le G).mp hrank
    (B ⊔ zpowers g) inferInstance
  have heq : B = B ⊔ zpowers g := eq_of_le_of_card_ge le_sup_left (by
    rw [hB]
    exact hcard)
  rw [heq]
  exact (show zpowers g ≤ B ⊔ zpowers g from le_sup_right) (mem_zpowers g)

end Representation.BinarySixElementaryTwentySevenCentralizer
