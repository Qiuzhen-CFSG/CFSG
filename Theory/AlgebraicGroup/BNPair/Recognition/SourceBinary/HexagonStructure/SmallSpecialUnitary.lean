module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SmallProjectiveUnitary
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiCartanAction
public import Theory.SpecificGroups.SU3.SmallSpecialExtraspecial

/-!
# The scalar section of the small special-unitary hexagon

The center of the actual root actor lies in the full Cartan and is exactly
its panel kernel. For SU3(2) the Cartan intersection has order three, so
it is the same scalar center. The corresponding simple reflection fixes
the whole odd Cartan: its displacement is simultaneously fixed and inverted.

The literal centralizer C = C_{U_sj}(Z(R_j)) is an invariant root section.
Its action factors through the faithful projective nine-point group. Root
separation prevents a two-group image, primitivity proves faithfulness,
and coprime Frattini faithfulness gives binary degree at least eight.
When N normalizes the scalar subgroup, the crossed root and its nontrivial
square lie in C and its Frattini subgroup. Both successive Frattini
quotients therefore have order at least 256.

For two SU3(2) endpoints, both simple reflections fix H. The actual Weyl
lifts generate N modulo H, proving scalar normality and discharging the
section's extra premise. Thus |C| is at least 2^16, while the exact
five-root radical containing it has order 2^15, a contradiction. The
companion CFSG module constructs the actors from the original markings
and includes both projective/special scalar conventions at both endpoints.

For a linear opposite, its two-layer bound and the source square profile
force field order two or eight. The corresponding Borel has order two or
fifty-six, prime to three. The other reflection's displacement of a scalar
cubic belongs to that Borel and is again cubic, hence trivial. Thus N
normalizes the same scalar subgroup and the same contradiction applies.
Together with the retained exclusions this removes SU3(2) against the full
original catalogue.

Source: Fong--Seitz I (6D), printed pp.41--42, using (3G), (4D), and (5D).
The argument retains full B, literal right-conjugation words, and the
original scalar kernel. No endpoint perfectness is assumed. Regular unitary
exclusions and the exhaustive (6E) assembly remain.
-/

public noncomputable section
open Subgroup MulAction BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates UnitarySource ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (j : Fin 2)

private theorem center_le_cartan
    (hK : simpleRemainder Q split j ≤ localKernel Q j) :
    center (rankOne Q split j) ≤ (Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j) := by
  intro z hz
  have hB : (z : X ⧸ Q.D) ∈ Q.tits.B := by
    apply (rankOne_borel_iff_root_normalizer Q split j hK z).mpr
    exact center_le_normalizer _ hz
  let s := actorReflection Q split j
  have hs : (s.val : X ⧸ Q.D)*z*(s.val : X ⧸ Q.D)⁻¹ = z := by
    have hc := congrArg Subtype.val (mem_center_iff.mp hz (⟨s.val,s.mem_rankOne⟩ : rankOne Q split j))
    change (s.val : X ⧸ Q.D)*z = (z : X ⧸ Q.D)*s.val at hc
    rw [hc,mul_inv_cancel_right]
  apply oppositeLevi_inf_two_borels_le_torus Q split j
  refine ⟨rootActor_le_oppositeLevi Q split j z.property,hB,?_⟩
  rw [borelConjugate_eq _ s.val s.class_eq]
  change (s.val : X ⧸ Q.D)*z*(s.val : X ⧸ Q.D)⁻¹ ∈ Q.tits.B
  rwa [hs]

private theorem small_special_cartan
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 4) (hconj : ∀ x, J.conj x=x^2)
    (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split j ≃* J.specialSubgroup)
    (hroot : Nat.card (simpleRoot Q split j) = 8) :
    (Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j) = center (rankOne Q split j) ∧
      Nat.card (center (rankOne Q split j)) = 3 := by
  let R := rankOne Q split j
  let T := (Q.tits.B ⊓ Q.tits.N).subgroupOf R
  have hR : Nat.card R = 216 := (Nat.card_congr μ.toEquiv).trans
    (HermitianForm.SmallThreeCore.special_group_card J hc hconj)
  have hZ : Nat.card (center R) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr μ).toEquiv]
    rw [←J.specialToProjective_ker_eq_center
      (HermitianForm.EvenProjectiveComparison.center_eq_bot J (n := 1) (by decide)
        (by simpa using hc) (by simpa using hconj))]
    exact HermitianForm.SmallThreeCore.special_scalar_kernel_card J hc hconj
  have hp : Nat.card (Panel Q j) = 9 := by
    have hh := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at hh
    omega
  have hB := (Q.tits.B.subgroupOf R).index_mul_card
  rw [rankOne_borel_index Q split j,hp,hR] at hB
  have hBc : Nat.card (Q.tits.B.subgroupOf R) = 24 := by omega
  have hd : Nat.card T ∣ 24 := hBc ▸ card_dvd_of_le
    (show T ≤ Q.tits.B.subgroupOf R from subgroupOf_mono _ inf_le_left)
  let f : T →* (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) :=
    (R.subtype.comp T.subtype).codRestrict _ (fun t => t.property)
  have hf : Function.Injective f := by
    intro a b he
    have he' : (a.val : X ⧸ Q.D) = (b.val : X ⧸ Q.D) :=
      congrArg (fun z : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) => (z : X ⧸ Q.D)) he
    exact Subtype.ext (Subtype.ext he')
  have ho : Nat.Coprime 2 (Nat.card T) := split.odd.of_dvd_right (card_dvd_of_injective f hf)
  have hd3 : Nat.card T ∣ 3 := (ho.symm.pow_right 3).dvd_of_dvd_mul_left (by simpa using hd)
  exact ⟨(eq_of_le_of_card_ge (center_le_cartan Q split j hK)
    (hZ ▸ Nat.le_of_dvd (by decide) hd3)).symm,hZ⟩


private theorem center_eq_panel_kernel
    (hK : simpleRemainder Q split j ≤ localKernel Q j) :
    center (rankOne Q split j) = (rootImageProjection Q split j).ker := by
  have he : (rootImageProjection Q split j).ker = (RootLocalCover.projection Q split j).ker := by
    change ((panelAction Q j _ (rankOne_le_parabolic Q split j)).rangeRestrict).ker = _
    rw [MonoidHom.ker_rangeRestrict,panelAction_ker,RootLocalCover.projection_ker]
  rw [he]
  apply le_antisymm ?_ (RootLocalCover.projection_ker_central Q split j)
  intro z hz
  rw [RootLocalCover.projection_ker]
  have hzH := center_le_cartan Q split j hK hz
  have hzc : (z : X ⧸ Q.D) ∈ centralizer (simpleRoot Q split j : Set (X ⧸ Q.D)) := by
    intro a ha
    exact congrArg Subtype.val (mem_center_iff.mp hz
      (⟨a,(show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left) ha⟩ : rankOne Q split j))
  have hh : (z : X ⧸ Q.D) ∈ (Q.tits.B ⊓ Q.tits.N) ⊓
      centralizer (simpleRoot Q split j : Set (X ⧸ Q.D)) := ⟨hzH,hzc⟩
  rw [cartan_centralizer_simpleRoot Q split j] at hh
  exact hh.2

private theorem central_cartan_reflection
    (hT : (Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j) ≤ center (rankOne Q split j)) :
    simpleCartanAction Q split j = 1 := by
  let H := (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))
  let α := simpleCartanAction Q split j
  let s := actorReflection Q split j
  apply MulEquiv.ext
  intro h
  let c : H := α h * h⁻¹
  have hcR : (c : X ⧸ Q.D) ∈ rankOne Q split j := by
    change (α h : X ⧸ Q.D)*(h : X ⧸ Q.D)⁻¹ ∈ _
    rw [simpleCartanAction_apply Q split j s.val s.class_eq]
    have hn := rankOne_torus_normalizes Q split j h.property
    have hconj : (h : X ⧸ Q.D)*(s.val : X ⧸ Q.D)*(h : X ⧸ Q.D)⁻¹ ∈ rankOne Q split j :=
      (mem_normalizer_iff.mp hn _).mp s.mem_rankOne
    simpa only [mul_assoc] using (rankOne Q split j).mul_mem
      ((rankOne Q split j).inv_mem s.mem_rankOne) hconj
  have hfix : α c = c := by
    apply Subtype.ext
    rw [simpleCartanAction_apply Q split j s.val s.class_eq]
    have hh := congrArg Subtype.val (mem_center_iff.mp (hT (show (⟨c,hcR⟩ : rankOne Q split j) ∈ (Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j) from c.property))
      (⟨s.val,s.mem_rankOne⟩ : rankOne Q split j))
    change (s.val : X ⧸ Q.D)*(c : X ⧸ Q.D) = (c : X ⧸ Q.D)*s.val at hh
    calc
      (s.val : X ⧸ Q.D)⁻¹*(c : X ⧸ Q.D)*s.val =
        (s.val : X ⧸ Q.D)⁻¹*((c : X ⧸ Q.D)*s.val) := by group
      _ = _ := by rw [←hh,inv_mul_cancel_left]
  have hinv : α c = c⁻¹ := by
    dsimp only [c]
    rw [map_mul,map_inv,simpleCartanAction_involutive,mul_inv_rev,inv_inv]
  have hc2 : c^2 = 1 := by
    rw [pow_two]
    calc c*c = c⁻¹*c := congrArg (·*c) (hfix.symm.trans hinv)
         _ = 1 := inv_mul_cancel c
  have hc1 : c = 1 := split.odd.symm.pow_left_bijective.injective (hc2.trans (one_pow 2).symm)
  exact mul_inv_eq_one.mp hc1



private theorem central_nine_panel_structure
    (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (hR : Nat.card (rankOne Q split j) = 216)
    (hZ : Nat.card (center (rankOne Q split j)) = 3)
    (hroot : Nat.card (simpleRoot Q split j) = 8) :
    Group.IsSolvable (rootPanelImage Q split j) ∧
      Nat.card (rootPanelImage Q split j) = 72 ∧
      (∀ g : stabilizer (rootPanelImage Q split j) (panelBase Q j),
        ∀ x : Panel Q j, x ≠ panelBase Q j → (g : rootPanelImage Q split j) • x = x → g = 1) := by
  let f := rootImageProjection Q split j
  have hf : Function.Surjective f :=
    (panelAction Q j _ (rankOne_le_parabolic Q split j)).rangeRestrict_surjective
  have hc : Nat.card (rootPanelImage Q split j) = 72 := by
    have hh := f.ker.index_mul_card
    rw [index_eq_card,Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
      ←center_eq_panel_kernel Q split j hK,hZ,hR] at hh
    omega
  have hsol : Group.IsSolvable (rootPanelImage Q split j) := by
    apply Theory.GroupTheory.isSolvable_of_prime_dvd_card_eq_two_or_three
    intro p hp hd
    rw [hc,show 72 = 2^3*3^2 by decide] at hd
    obtain hh | hh := hp.dvd_mul.mp hd
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hh))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hh))
  have hp : Nat.card (Panel Q j) = 9 := by
    have hh := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at hh
    omega
  let := isPreprimitive_of_is_two_pretransitive (rootPanelImage_two_pretransitive Q split j)
  have hs := (stabilizer (rootPanelImage Q split j) (panelBase Q j)).index_mul_card
  rw [index_stabilizer_of_transitive,hp,hc] at hs
  let r : simpleRoot Q split j →* stabilizer (rootPanelImage Q split j) (panelBase Q j) :=
    (f.comp (inclusion (show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left))).codRestrict _
      (fun a => panelRoot_fixes_base Q split j a)
  have hi : Function.Injective r := by
    intro a b he
    apply simpleRoot_panelAction_injective Q split j
    exact congrArg (fun z => z.val.val) he
  have hr : Function.Surjective r := (Nat.bijective_iff_injective_and_card r).mpr ⟨hi,by omega⟩ |>.2
  refine ⟨hsol,hc,?_⟩
  intro g x hx hfix
  obtain ⟨a,rfl⟩ := hr g
  have ha : a=1 := (exists_unique_root_transport Q split j x x hx hx).unique hfix
    (by change (1 : panelActor Q split j) • x = x; exact one_smul _ _)
  rw [ha,map_one]

/-- The literal scalar subgroup in the ambient marked quotient. -/
@[expose] def rankOneScalar : Subgroup (X ⧸ Q.D) :=
  (center (rankOne Q split j)).map (rankOne Q split j).subtype

/-- The ambient image of the actual center centralizes the same root actor. -/
theorem scalar_centralizes_rankOne :
    rankOneScalar Q split j ≤ centralizer (rankOne Q split j : Set (X ⧸ Q.D)) := by
  rintro z ⟨r,hr,rfl⟩ x hx
  exact congrArg Subtype.val (mem_center_iff.mp hr (⟨x,hx⟩ : rankOne Q split j))

/-- The source C_{U_sj}(Z(R_j)), with its actual conjugation action. -/
@[expose] def scalarFixedSection (hK : simpleRemainder Q split j ≤ localKernel Q j) :
    RootSection Q split j :=
  centralizerSection Q split j hK (rankOneScalar Q split j) (scalar_centralizes_rankOne Q split j)

private theorem scalar_section_kernel (d : RootSection Q split j)
    (hd : d.numerator ≤ centralizer (rankOneScalar Q split j : Set (X ⧸ Q.D))) :
    center (rankOne Q split j) ≤ d.numeratorAction.ker := by
  intro r hr
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [d.numeratorAction_apply]
  have hh := mem_centralizer_iff.mp (hd x.property) r (mem_map_of_mem _ hr)
  rw [hh,mul_inv_cancel_right]
  rfl

private theorem central_nine_section_not_two
    (hT : (Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j) ≤ center (rankOne Q split j))
    (hroot : Nat.card (simpleRoot Q split j) = 8)
    (hm : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
    (s : RootReflection Q split j) (d : RootSection Q split j) (hden : d.denominator = ⊥)
    (hd : d.numerator ≤ centralizer (rankOneScalar Q split j : Set (X ⧸ Q.D)))
    (a : rootAt Q split j (Q.simple i)) (ha : a ≠ 1)
    (hax : (a : X ⧸ Q.D) ∈ d.numerator) : ¬ IsPGroup 2 d.numeratorAction.range := by
  let f := d.numeratorAction.rangeRestrict
  let R := rankOne Q split j
  let B := Q.tits.B.subgroupOf R
  let A := (simpleRoot Q split j).subgroupOf R
  have hAB : A.map f = B.map f := by
    apply le_antisymm (map_mono (subgroupOf_mono _ ((simpleRoot_le Q split j).trans split.U_le)))
    rintro _ ⟨r,hr,rfl⟩
    obtain ⟨u,hu,t,ht,he⟩ := rootActor_borel_factorization Q split j r.property hr
    let u' : R := ⟨u,(show simpleRoot Q split j ≤ R from le_sup_left) hu⟩
    let t' : R := ⟨t,ht.1⟩
    have he' : r = u'*t' := Subtype.ext he
    refine ⟨u',hu,?_⟩
    rw [he',map_mul,show f t' = 1 from Subtype.ext
      (scalar_section_kernel Q split j d hd (hT ht.2)),mul_one]
  intro htwo
  have hp : Nat.card (Panel Q j) = 9 := by
    have hh := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at hh
    omega
  have hind : (B.map f).index ∣ 9 := by
    have hh := B.index_map_dvd d.numeratorAction.rangeRestrict_surjective
    rwa [rankOne_borel_index Q split j,hp] at hh
  obtain ⟨n,hn⟩ := htwo.exists_card_eq
  have hidx : (B.map f).index = 1 := Nat.eq_one_of_dvd_coprimes
    (by simpa using (by decide : Nat.Coprime 9 2).pow_right n)
    hind (hn ▸ (B.map f).index_dvd_card)
  have htop : A.map f = ⊤ := hAB.trans (index_eq_one.mp hidx)
  have hr : f ⟨s.val,s.mem_rankOne⟩ ∈ A.map f := htop ▸ mem_top _
  obtain ⟨u,hu,he⟩ := hr
  apply ownRoot_oddProduct_moves_section Q split hm i j hij s u⁻¹
    ((simpleRoot Q split j).inv_mem hu) d hden a ha hax
  have he' : d.numeratorAction u = d.numeratorAction ⟨s.val,s.mem_rankOne⟩ := congrArg Subtype.val he
  have hz : d.numeratorAction ((⟨s.val,s.mem_rankOne⟩ : R)*u⁻¹) = 1 := by
    rw [map_mul,map_inv,←he',mul_inv_cancel]
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H x => rw [d.action_mk,hz]; rfl

/-- A section centralized by the actual scalar kernel has projective
binary degree at least eight. The crossed root proves its action is nontrivial. -/
theorem small_special_scalar_section_bound
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 4) (hconj : ∀ x, J.conj x=x^2)
    (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split j ≃* J.specialSubgroup)
    (hroot : Nat.card (simpleRoot Q split j) = 8)
    (hm : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
    (s : RootReflection Q split j) (d : RootSection Q split j) (hden : d.denominator = ⊥)
    (hd : d.numerator ≤ centralizer (rankOneScalar Q split j : Set (X ⧸ Q.D)))
    (a : rootAt Q split j (Q.simple i)) (ha : a ≠ 1)
    (hax : (a : X ⧸ Q.D) ∈ d.numerator) :
    256 ≤ Nat.card (d.numerator ⧸ frattini d.numerator) := by
  obtain ⟨hT,hZ⟩ := small_special_cartan Q split j J hc hconj hK μ hroot
  have hR : Nat.card (rankOne Q split j) = 216 := (Nat.card_congr μ.toEquiv).trans
    (HermitianForm.SmallThreeCore.special_group_card J hc hconj)
  let f := rootImageProjection Q split j
  have hf : Function.Surjective f :=
    (panelAction Q j _ (rankOne_le_parabolic Q split j)).rangeRestrict_surjective
  have hk : f.ker ≤ d.numeratorAction.ker :=
    (center_eq_panel_kernel Q split j hK) ▸ scalar_section_kernel Q split j d hd
  let β : rootPanelImage Q split j →* MulAut d.numerator :=
    f.liftOfSurjective hf ⟨d.numeratorAction,hk⟩
  have hb (r : rankOne Q split j) : β (f r) = d.numeratorAction r :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hbrange : β.range = d.numeratorAction.range := by
    have he : β.comp f = d.numeratorAction := MonoidHom.ext hb
    rw [←he,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hf,←MonoidHom.range_eq_map]
  obtain ⟨hsol,hcard,hfree⟩ := central_nine_panel_structure Q split j hK hR hZ hroot
  let := hsol
  have hp : Nat.card (Panel Q j) = 9 := by
    have hh := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at hh
    omega
  have hβ : Function.Injective β := BinaryPanel.injective_of_non_two_image
    (rootPanelImage_two_pretransitive Q split j) hp hcard (panelBase Q j) β
    (hbrange ▸ central_nine_section_not_two Q split j hT.le hroot hm i hij s d hden hd a ha hax)
  let γ := (quotientAut (frattini d.numerator)).comp β
  have hkγ : IsPGroup 2 γ.ker :=
    (isPGroup_quotientAut_frattini_kernel d.isTwo).comap_of_injective β hβ
  have hγ : Function.Injective γ := BinaryPanel.injective_of_two_kernel
    (rootPanelImage_two_pretransitive Q split j) hp (panelBase Q j) γ hkγ
  let : Fact (IsPGroup 2 d.numerator) := ⟨d.isTwo⟩
  let : IsElementaryAbelian 2 (d.numerator ⧸ frattini d.numerator) := isElementaryAbelian_quotient_frattini
  let ρ := Representation.FrattiniAction.ofAutomorphismHom γ
  have hρ : Function.Injective ρ := by
    intro r t he
    apply hγ
    ext x
    exact Additive.ofMul.injective (congrArg
      (fun a : Module.End (ZMod 2) (Additive (d.numerator ⧸ frattini d.numerator)) =>
        a (Additive.ofMul x)) he)
  have hdim := BinaryPanel.frobenius_nine_degree
    (rootPanelImage_two_pretransitive Q split j) hp hcard (panelBase Q j) hfree ρ hρ
  have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hdim
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (d.numerator ⧸ frattini d.numerator))
  simp only [Nat.card_zmod] at he
  rw [←he] at hh
  exact hh

private theorem central_nine_root_square
    (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (hR : Nat.card (rankOne Q split j) = 216)
    (hZ : Nat.card (center (rankOne Q split j)) = 3)
    (hroot : Nat.card (simpleRoot Q split j) = 8) :
    ∃ a : simpleRoot Q split j, a^2 ≠ 1 := by
  classical
  obtain ⟨hsol,hcard,hfree⟩ := central_nine_panel_structure Q split j hK hR hZ hroot
  let := hsol
  have hp : Nat.card (Panel Q j) = 9 := by
    have he := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at he
    omega
  let f : simpleRoot Q split j →* stabilizer (rootPanelImage Q split j) (panelBase Q j) :=
    ((rootImageProjection Q split j).comp
      (inclusion (show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left))).codRestrict _
        (fun r => panelRoot_fixes_base Q split j r)
  have hf : Function.Injective f := by
    intro a b he
    apply simpleRoot_panelAction_injective Q split j
    exact congrArg (fun a => a.val.val) he
  by_contra! hn
  have hu (a b : simpleRoot Q split j) (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
    apply hf
    apply BinaryPanel.stabilizer_involution_unique
      (rootPanelImage_two_pretransitive Q split j) hp (panelBase Q j) hfree
    · exact fun he => ha (hf (he.trans f.map_one.symm))
    · exact fun he => hb (hf (he.trans f.map_one.symm))
    · rw [←map_pow,hn,map_one]
    · rw [←map_pow,hn,map_one]
  have hi : Function.Injective (fun a : simpleRoot Q split j => decide (a = 1)) := by
    intro a b he
    by_cases ha : a = 1
    · have hb : b = 1 := by simpa [ha] using he.symm
      exact ha.trans hb.symm
    · have hb : b ≠ 1 := by simpa [ha] using he.symm
      exact hu a b ha hb
  have hc := Nat.card_le_card_of_injective _ hi
  norm_num [hroot] at hc


/-- Both genuine Frattini layers of the scalar centralizer. The required
normality is relative to N and is used to transport the actual crossed root. -/
theorem small_special_scalar_two_layers
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 4) (hconj : ∀ x, J.conj x=x^2)
    (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split j ≃* J.specialSubgroup)
    (hroot : Nat.card (simpleRoot Q split j) = 8)
    (hm : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
    (hTN : Q.tits.N ≤ normalizer (rankOneScalar Q split j : Set (X ⧸ Q.D))) :
    let C := simpleRemainder Q split j ⊓ centralizer (rankOneScalar Q split j : Set (X ⧸ Q.D))
    256 ≤ Nat.card (C ⧸ frattini C) ∧
      256 ≤ Nat.card (frattini C ⧸ frattini (frattini C)) ∧ 65536 ≤ Nat.card C := by
  let T := rankOneScalar Q split j
  let d := scalarFixedSection Q split j hK
  let f := frattiniSection Q split j d
  let s := actorReflection Q split j
  have hR : Nat.card (rankOne Q split j) = 216 := (Nat.card_congr μ.toEquiv).trans
    (HermitianForm.SmallThreeCore.special_group_card J hc hconj)
  have hZ := (small_special_cartan Q split j J hc hconj hK μ hroot).2
  obtain ⟨x,hx⟩ := central_nine_root_square Q split j hK hR hZ hroot
  let e := RootAction.conjugateEquiv (simpleRoot Q split j) (representative (Q.simple i))
  let a : rootAt Q split j (Q.simple i) := e.symm x
  have ha2 : a^2 ≠ 1 := by
    intro he
    apply hx
    have hh := congrArg e (show (e.symm x)^2=1 from he)
    simpa only [map_pow,map_one,MulEquiv.apply_symm_apply] using hh
  have ha : a ≠ 1 := fun he => ha2 (by rw [he,one_pow])
  have hfix : rootAt Q split j (Q.simple i) ≤ centralizer (T : Set (X ⧸ Q.D)) := by
    have hbase : simpleRoot Q split j ≤ centralizer (T : Set (X ⧸ Q.D)) :=
      (show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left).trans
        (le_centralizer_iff.mp (scalar_centralizes_rankOne Q split j))
    let n := representative (Q.simple i)
    have hh := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom) hbase
    change rootAt Q split j (Q.simple i) ≤ rightConjugate (centralizer (T : Set (X ⧸ Q.D))) (n : X ⧸ Q.D) at hh
    rwa [rightConjugate_eq_self _ (normalizer_le_normalizer_centralizer T (hTN n.property))] at hh
  have hA : rootAt Q split j (Q.simple i) ≤ d.numerator :=
    le_inf ((le_sup_left.trans le_sup_left).trans (middleRoots_le_remainder Q split hm i j hij)) hfix
  have h1 := small_special_scalar_section_bound Q split j J hc hconj hK μ hroot hm i hij s d rfl
    inf_le_right a ha (hA a.property)
  let : Fact (IsPGroup 2 d.numerator) := ⟨d.isTwo⟩
  have hfC : f.numerator ≤ centralizer (T : Set (X ⧸ Q.D)) := by
    rintro z ⟨y,hy,rfl⟩
    exact y.property.2
  have h2 := small_special_scalar_section_bound Q split j J hc hconj hK μ hroot hm i hij s f rfl hfC
    (a^2) ha2 ⟨(inclusion hA a)^2,pth_power_mem_frattini_of_isPGroup (p := 2) _,rfl⟩
  let eF : frattini d.numerator ≃* f.numerator :=
    (frattini d.numerator).equivMapOfInjective d.numerator.subtype d.numerator.subtype_injective
  have heF := Nat.card_congr (QuotientGroup.congr _ _ eF (frattini_map_equiv eF)).toEquiv
  have h2' : 256 ≤ Nat.card (frattini d.numerator ⧸ frattini (frattini d.numerator)) := heF ▸ h2
  refine ⟨h1,h2',?_⟩
  have hle := Nat.card_le_card_of_surjective _
    (QuotientGroup.mk'_surjective (frattini (frattini d.numerator)))
  have hmul := (frattini d.numerator).card_mul_index
  rw [index_eq_card] at hmul
  change 65536 ≤ Nat.card d.numerator
  nlinarith

private theorem normalizer_centralizes_cartan
    (hT : ∀ k, (Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split k) ≤ center (rankOne Q split k)) :
    Q.tits.N ≤ centralizer (Q.tits.B ⊓ Q.tits.N : Set (X ⧸ Q.D)) := by
  let H := (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))
  let A := centralizer (H : Set (X ⧸ Q.D))
  let n (k : Fin 2) := (actorReflection Q split k).val
  have hn (k) : QuotientGroup.mk' (H.subgroupOf Q.tits.N) (n k) = Q.simple k :=
    (actorReflection Q split k).class_eq
  have hnA (k) : (n k : X ⧸ Q.D) ∈ A := by
    intro h hh
    have hc := congrArg (fun a : MulAut H => (a (⟨h,hh⟩ : H) : X ⧸ Q.D))
      (central_cartan_reflection Q split k (hT k))
    rw [simpleCartanAction_apply Q split k (n k) (hn k)] at hc
    change (n k : X ⧸ Q.D)⁻¹*h*n k = h at hc
    have he := congrArg ((n k : X ⧸ Q.D)*·) hc
    simpa only [mul_assoc,mul_inv_cancel_left] using he
  have hHA : H ≤ A := by
    let := split.abelian
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hy⟩ : H) (⟨x,hx⟩ : H))
  intro g hg
  let q := QuotientGroup.mk' (H.subgroupOf Q.tits.N)
  let gN : Q.tits.N := ⟨g,hg⟩
  obtain ⟨k,hk,hqk⟩ := exists_weyl_lift_in Q n hn A hnA (q gN)
  have hdiff : gN*k⁻¹ ∈ H.subgroupOf Q.tits.N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (gN*k⁻¹)=1
    rw [map_mul,map_inv,hqk,mul_inv_cancel]
  have hh := A.mul_mem (hHA hdiff) hk
  change (g*(k : X ⧸ Q.D)⁻¹)*(k : X ⧸ Q.D) ∈ A at hh
  change g ∈ A
  simpa only [inv_mul_cancel_right] using hh

/-- The two degree-one special-unitary actors are impossible. Their
Cartan intersections are their scalar centers; both reflections therefore
fix H, giving the N-normal scalar section and its contradictory two layers. -/
theorem small_special_pair_excluded
    {F E : Type*} [Field F] [Finite F] [Field E] [Finite E]
    (J : HermitianForm 3 F) (I : HermitianForm 3 E)
    (hc : Nat.card F = 4) (hconj : ∀ x, J.conj x=x^2)
    (hcE : Nat.card E = 4) (hconjE : ∀ x, I.conj x=x^2)
    (hm : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : rankOne Q split i ≃* I.specialSubgroup)
    (μj : rankOne Q split j ≃* J.specialSubgroup)
    (hi : Nat.card (simpleRoot Q split i) = 8)
    (hj : Nat.card (simpleRoot Q split j) = 8) : False := by
  have hT (k : Fin 2) : (Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split k) ≤ center (rankOne Q split k) := by
    by_cases hk : k=i
    · subst k
      exact (small_special_cartan Q split i I hcE hconjE hKi μi hi).1.le
    · have hkj : k=j := by omega
      subst k
      exact (small_special_cartan Q split j J hc hconj hKj μj hj).1.le
  have hN := normalizer_centralizes_cartan Q split hT
  have hSH : rankOneScalar Q split j ≤ Q.tits.B ⊓ Q.tits.N := by
    rintro z ⟨x,hx,rfl⟩
    exact center_le_cartan Q split j hKj hx
  have hTN : Q.tits.N ≤ normalizer (rankOneScalar Q split j : Set (X ⧸ Q.D)) :=
    (hN.trans (centralizer_le hSH)).trans (Subgroup.centralizer_le_normalizer _)
  have hlarge := (small_special_scalar_two_layers Q split j J hc hconj hKj μj hj hm i hij hTN).2.2
  have hle := Nat.card_le_card_of_injective
    (inclusion (show simpleRemainder Q split j ⊓ centralizer (rankOneScalar Q split j : Set (X ⧸ Q.D)) ≤
      simpleRemainder Q split j from inf_le_left)) (inclusion_injective _)
  have hu := unipotent_card_even Q split 3 hm
  have hprod : Nat.card (simpleRoot Q split 0)*Nat.card (simpleRoot Q split 1) = 64 := by
    have hi' : i=0 ∨ i=1 := by omega
    have hj' : j=0 ∨ j=1 := by omega
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · exact (hij rfl).elim
    · rw [hi,hj]
    · rw [hi,hj]
    · exact (hij rfl).elim
  rw [hprod] at hu
  have hrem := unipotent_card_simple Q split j
  rw [hu,hj] at hrem
  norm_num at hrem
  omega

private theorem cubic_scalar_normalized
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hTj : (Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j) ≤ center (rankOne Q split j))
    (hZ : Nat.card (center (rankOne Q split j)) = 3)
    (i : Fin 2) (hij : i ≠ j)
    (hB : Nat.Coprime 3 (Nat.card (Q.tits.B.subgroupOf (rankOne Q split i)))) :
    Q.tits.N ≤ normalizer (rankOneScalar Q split j : Set (X ⧸ Q.D)) := by
  let H := (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))
  let T := rankOneScalar Q split j
  have hTH : T ≤ H := by
    rintro z ⟨r,hr,rfl⟩
    exact center_le_cartan Q split j hKj hr
  have hcube (t : T) : (t : X ⧸ Q.D)^3 = 1 := by
    obtain ⟨z,hz,he⟩ := t.property
    have hh := pow_card_eq_one' (x := (⟨z,hz⟩ : center (rankOne Q split j)))
    rw [hZ] at hh
    have h := congrArg (fun z : center (rankOne Q split j) => (z.val : X ⧸ Q.D)) hh
    have he' : (z : X ⧸ Q.D) = (t : X ⧸ Q.D) := he
    change (z : X ⧸ Q.D)^3 = 1 at h
    exact he' ▸ h
  have hfix (k : Fin 2) (t : T) : simpleCartanAction Q split k (⟨t,hTH t.property⟩ : H) =
      (⟨t,hTH t.property⟩ : H) := by
    by_cases hk : k=j
    · subst k
      rw [central_cartan_reflection Q split j hTj]
      rfl
    · have hki : k=i := by omega
      subst k
      let h : H := ⟨t,hTH t.property⟩
      let α := simpleCartanAction Q split i
      let s := actorReflection Q split i
      let c : H := α h*h⁻¹
      have hcR : (c : X ⧸ Q.D) ∈ rankOne Q split i := by
        change (α h : X ⧸ Q.D)*(h : X ⧸ Q.D)⁻¹ ∈ _
        rw [simpleCartanAction_apply Q split i s.val s.class_eq]
        have hn := rankOne_torus_normalizes Q split i h.property
        have hconj : (h : X ⧸ Q.D)*(s.val : X ⧸ Q.D)*(h : X ⧸ Q.D)⁻¹ ∈ rankOne Q split i :=
          (mem_normalizer_iff.mp hn _).mp s.mem_rankOne
        simpa only [mul_assoc] using (rankOne Q split i).mul_mem
          ((rankOne Q split i).inv_mem s.mem_rankOne) hconj
      have hc3 : c^3=1 := by
        let := split.abelian
        have ht3 : h^3=1 := Subtype.ext (hcube t)
        dsimp only [c]
        rw [mul_pow,←map_pow,ht3,map_one,inv_pow,ht3,inv_one,mul_one]
      let b : Q.tits.B.subgroupOf (rankOne Q split i) := ⟨⟨c,hcR⟩,c.property.1⟩
      have hb3 : b^3=1 := by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun c : H => (c : X ⧸ Q.D)) hc3
      have hb1 : b=1 := hB.symm.pow_left_bijective.injective (hb3.trans (one_pow 3).symm)
      have hc1 : c=1 := Subtype.ext (congrArg (fun b : Q.tits.B.subgroupOf (rankOne Q split i) =>
        (b.val : X ⧸ Q.D)) hb1)
      exact mul_inv_eq_one.mp hc1
  let A := centralizer (T : Set (X ⧸ Q.D))
  let n (k : Fin 2) := (actorReflection Q split k).val
  have hn (k) : QuotientGroup.mk' (H.subgroupOf Q.tits.N) (n k)=Q.simple k :=
    (actorReflection Q split k).class_eq
  have hnA (k) : (n k : X ⧸ Q.D) ∈ A := by
    intro t ht
    have hh := congrArg Subtype.val (hfix k ⟨t,ht⟩)
    rw [simpleCartanAction_apply Q split k (n k) (hn k)] at hh
    have he := congrArg ((n k : X ⧸ Q.D)*·) hh
    simpa only [mul_assoc,mul_inv_cancel_left] using he
  have hHA : H ≤ A := by
    let := split.abelian
    intro h hh t ht
    exact congrArg Subtype.val (mul_comm (⟨t,hTH ht⟩ : H) (⟨h,hh⟩ : H))
  apply (show Q.tits.N ≤ A from ?_).trans (Subgroup.centralizer_le_normalizer _)
  intro g hg
  let q := QuotientGroup.mk' (H.subgroupOf Q.tits.N)
  let gN : Q.tits.N := ⟨g,hg⟩
  obtain ⟨k,hk,hqk⟩ := exists_weyl_lift_in Q n hn A hnA (q gN)
  have hdiff : gN*k⁻¹ ∈ H.subgroupOf Q.tits.N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (gN*k⁻¹)=1
    rw [map_mul,map_inv,hqk,mul_inv_cancel]
  have hh := A.mul_mem (hHA hdiff) hk
  change (g*(k : X ⧸ Q.D)⁻¹)*(k : X ⧸ Q.D) ∈ A at hh
  simpa only [inv_mul_cancel_right] using hh

private theorem scalar_small_opposite_excluded
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 4) (hconj : ∀ x, J.conj x=x^2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : rankOne Q split j ≃* J.specialSubgroup)
    (hj : Nat.card (simpleRoot Q split j) = 8)
    (hm : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
    (hTN : Q.tits.N ≤ normalizer (rankOneScalar Q split j : Set (X ⧸ Q.D)))
    (hi : Nat.card (simpleRoot Q split i) ≤ 8) : False := by
  have hlarge := (small_special_scalar_two_layers Q split j J hc hconj hKj μj hj hm i hij hTN).2.2
  have hle := Nat.card_le_card_of_injective
    (inclusion (show simpleRemainder Q split j ⊓ centralizer (rankOneScalar Q split j : Set (X ⧸ Q.D)) ≤
      simpleRemainder Q split j from inf_le_left)) (inclusion_injective _)
  have hu := unipotent_card_even Q split 3 hm
  have hp : Nat.card (simpleRoot Q split 0)*Nat.card (simpleRoot Q split 1) ≤ 64 := by
    have hi' : i=0 ∨ i=1 := by omega
    have hj' : j=0 ∨ j=1 := by omega
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · exact (hij rfl).elim
    · rw [hj]; omega
    · rw [hj]; omega
    · exact (hij rfl).elim
  have hu' : Nat.card split.U ≤ 262144 := by
    rw [hu]
    exact Nat.pow_le_pow_left hp 3
  have hrem := unipotent_card_simple Q split j
  rw [hj] at hrem
  omega

/-- The small special-unitary endpoint is excluded against every binary
linear field. The square profile reduces the linear order to two or eight;
its Borel has order prime to three, so N normalizes the literal scalar. -/
theorem small_special_linear_excluded
    {F E : Type*} [Field F] [Finite F] [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 F) (hc : Nat.card F = 4) (hconj : ∀ x, J.conj x=x^2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : rankOne Q split j ≃* J.specialSubgroup)
    (hj : Nat.card (simpleRoot Q split j) = 8)
    (hm : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False := by
  obtain ⟨hT,hZ⟩ := small_special_cartan Q split j J hc hconj hKj μj hj
  have hRj : Nat.card (rankOne Q split j) = 216 := (Nat.card_congr μj.toEquiv).trans
    (HermitianForm.SmallThreeCore.special_group_card J hc hconj)
  have hs := central_nine_root_square Q split j hKj hRj hZ hj
  obtain ⟨a,ha⟩ := (split.isTwo.to_le (simpleRoot_le Q split i)).exists_card_eq
  have hF : Nat.card E = 2^a := (GTwoSource.simpleRoot_card Q split i hKi μi).symm.trans ha
  have ha0 : 0<a := by
    have hh : 1 < Nat.card E := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    rw [hF] at hh
    by_contra h
    have ha0 : a=0 := by omega
    simp [ha0] at hh
  have hpar := mixed_unitary_square_profile_parity (n := 1) (a := a) (by
    simpa only [ha,hj,Nat.reducePow] using hsquare)
  have ha4 : a≤4 := by
    by_contra! hbig
    have hb := linear_two_layer_bound_of_opposite_square Q split hm j i hij.symm hKj hKi μi
      (actorReflection Q split i) (by omega) hF hs
    have hu := unipotent_card_even Q split 3 hm
    have hp : Nat.card (simpleRoot Q split 0)*Nat.card (simpleRoot Q split 1) = 2^a*8 := by
      have hi' : i=0 ∨ i=1 := by omega
      have hj' : j=0 ∨ j=1 := by omega
      rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
      · exact (hij rfl).elim
      · rw [ha,hj]
      · rw [ha,hj,Nat.mul_comm]
      · exact (hij rfl).elim
    rw [hp] at hu
    have hv := unipotent_card_simple Q split i
    rw [ha,hu] at hv
    have hpow : 2^(5*a) ≤ 2^(3*a+9) := by
      calc
        2^(5*a) = 2^a*2^(4*a) := by rw [←pow_add]; congr 1; omega
        _ ≤ 2^a*Nat.card (simpleRemainder Q split i) := Nat.mul_le_mul_left _ hb
        _ = (2^a*8)^3 := hv.symm
        _ = 2^(3*a+9) := by
          rw [show (8 : ℕ)=2^3 from rfl,←pow_add,←pow_mul]
          congr 1
          omega
    have hh := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hpow
    omega
  have hchoices : a=1 ∨ a=3 := by omega
  have hRi : Nat.card (rankOne Q split i) = Nat.card E*(Nat.card E^2-1) :=
    (Nat.card_congr (GTwoSource.rankOneLinearEquiv Q split i hKi μi).toEquiv).trans
      BenderSuzuki.External.huppert614_card_specialLinearGroup
  have hp := singleton_parabolic_root_index Q split i
  change Nat.card (Panel Q i) = 1+Nat.card (simpleRoot Q split i) at hp
  rw [ha] at hp
  have hB := (Q.tits.B.subgroupOf (rankOne Q split i)).index_mul_card
  rw [rankOne_borel_index Q split i,hp,hRi,hF] at hB
  have hB3 : Nat.Coprime 3 (Nat.card (Q.tits.B.subgroupOf (rankOne Q split i))) := by
    rcases hchoices with rfl | rfl
    · have hh : Nat.card (Q.tits.B.subgroupOf (rankOne Q split i))=2 := by norm_num at hB; omega
      rw [hh]; decide
    · have hh : Nat.card (Q.tits.B.subgroupOf (rankOne Q split i))=56 := by norm_num at hB; omega
      rw [hh]; decide
  apply scalar_small_opposite_excluded Q split j J hc hconj hKj μj hj hm i hij
    (cubic_scalar_normalized Q split j hKj hT.le hZ i hij hB3)
  rw [ha]
  rcases hchoices with rfl | rfl <;> decide

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
