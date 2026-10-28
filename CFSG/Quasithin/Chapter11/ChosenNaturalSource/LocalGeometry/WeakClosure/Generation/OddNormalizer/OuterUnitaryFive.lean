module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterSymplectic
public import Theory.Representation.PSL3Four.SmallDegree
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.UnitaryFive

/-!
# Excluding unitary-five component covers in both actions

The remaining outer section has the literal simple quotient PSL₃(4).
A Sylow two-subgroup of PSU₅(4) has an intrinsic Frattini flag with two
order-sixteen factors. The kernels of the two automorphism actions have
two-group intersection, so a nonsolvable simple section survives in one
factor. Its order equals |GL₄(2)|, making the section map an isomorphism.
This would give a faithful binary four-dimensional PSL₃(4) action, whereas
a nontrivial perfect action has an irreducible section of degree at least nine.

Central descent retains the original component cover. Combining this outer
exclusion with the existing inner-placement argument excludes the entire
PSU₅(4) row on the actual moved component. Source applies it to the literal
Hall kernel, retaining the original V and all earlier source alternatives.
The other outer and J₄/Ru configurations remain with this normalizer owner.

The flag kernel calculation follows FrattiniFlagQuotientPair, retaining
the actual quotient actions needed here instead of only their order bounds.
Source: Aschbacher–Smith 4.4.10–12, printed pp.621–622, using I.3.1 and the
PSL₃(4) degree theorem from GLS III §§2.8.6, 2.8.8 and 2.8.10(c).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

private theorem projective_four_small_action_trivial
    {F R W : Type*} [Field F] [Finite F] [Group R] [Group.IsPerfect R]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (hF : Nat.card F = 4) (e : R ≃* PSL(3,F))
    (ρ : Representation (ZMod 2) R W) (hd : Module.finrank (ZMod 2) W ≤ 8) :
    ∀ g, ρ g = 1 := by
  by_contra! hn
  let et : (⊤ : Subgroup R) ≃* R := Subgroup.topEquiv
  let : Group.IsPerfect (⊤ : Subgroup R) := Group.IsPerfect.ofSurjective
    (f := et.symm.toMonoidHom) et.symm.surjective
  have hne : ¬ (⊤ : Subgroup R) ≤ ρ.ker := by
    intro h
    obtain ⟨g,hg⟩ := hn
    exact hg (h (mem_top g))
  obtain ⟨U,N,hi,hN⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect
    (ρ := ρ) ⊤ hne
  let σ := N.quotientRepresentation
  let : σ.IsIrreducible := hi
  have hnσ : ∃ g, σ g ≠ 1 := by
    by_contra! h
    exact hN (fun g _ => h g)
  have h9 := Representation.PSL3Four.finrank_ge_nine_of_equiv hF e σ hnσ
  have h8 := (Submodule.finrank_quotient_le N.toSubmodule).trans
    ((Submodule.finrank_le U.toSubmodule).trans hd)
  omega

private theorem no_projective_four_section_aut_sixteen
    {F R E : Type*} [Field F] [Finite F] [Group R] [Finite R]
    [Group.IsPerfect R] [Nontrivial R] [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hF : Nat.card F = 4) (e : R ≃* PSL(3,F)) (hR : Nat.card R = 20160)
    (hE : Nat.card E = 16) (U : Subgroup (MulAut E))
    (f : U →* R) (hf : Function.Surjective f) : False := by
  have hAut : Nat.card (MulAut E) = 20160 := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E 4 (by simpa using hE)]
    norm_num [Fin.prod_univ_succ]
  have hb : Function.Bijective f := hf.bijective_of_nat_card_le (by
    rw [hR, ←hAut]
    exact Nat.card_le_card_of_injective U.subtype U.subtype_injective)
  let φ : R →* MulAut E := U.subtype.comp (MulEquiv.ofBijective f hb).symm.toMonoidHom
  have hφ : Function.Injective φ := U.subtype_injective.comp (MulEquiv.ofBijective f hb).symm.injective
  let ρ : Representation (ZMod 2) R (Additive E) :=
    { toFun := fun g =>
        { (φ g).toAdditive.toAddMonoidHom with map_smul' := ZMod.map_smul (φ g).toAdditive }
      map_one' := by ext x; change φ 1 x = x; rw [map_one]; rfl
      map_mul' := by intro a b; ext x; change φ (a*b) x = φ a (φ b x); rw [map_mul]; rfl }
  have hdim : Module.finrank (ZMod 2) (Additive E) = 4 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    change Nat.card E = _ at hc
    simpa only [Nat.card_zmod,hE] using hc.symm
  have ht := projective_four_small_action_trivial hF e ρ (by omega)
  obtain ⟨g,hg⟩ := exists_ne (1 : R)
  apply hg
  apply hφ
  rw [map_one]
  ext x
  exact DFunLike.congr_fun (ht g) (Additive.ofMul x)

private theorem section_survives_hom
    {H J R : Type*} [Group H] [Group J] [Group R] [IsSimpleGroup R]
    (hR : ¬ Group.IsSolvable R) (r : H →* J) [Group.IsSolvable r.ker]
    (U : Subgroup H) (f : U →* R) (hf : Function.Surjective f) :
    ∃ W : Subgroup J, ∃ g : W →* R, Function.Surjective g := by
  obtain ⟨W,g,hg⟩ := simple_section_quotient_of_solvable_kernel hR r.ker U f hf
  let e := QuotientGroup.quotientKerEquivRange r
  let j := r.range.subtype.comp e.toMonoidHom
  let a := W.equivMapOfInjective j (r.range.subtype_injective.comp e.injective)
  exact ⟨W.map j,g.comp a.symm.toMonoidHom,hg.comp a.symm.surjective⟩

private theorem no_section_of_two_actions
    {H J₁ J₂ R : Type*} [Group H] [Group J₁] [Group J₂] [Group R] [IsSimpleGroup R]
    (hR : ¬ Group.IsSolvable R) (r : H →* J₁) (q : H →* J₂)
    [Group.IsSolvable (r.ker ⊓ q.ker : Subgroup H)]
    (hr : ∀ (U : Subgroup J₁) (f : U →* R), ¬ Function.Surjective f)
    (hq : ∀ (U : Subgroup J₂) (f : U →* R), ¬ Function.Surjective f)
    (U : Subgroup H) (f : U →* R) (hf : Function.Surjective f) : False := by
  rcases simple_section_normal_or_quotient r.ker U f hf with ⟨W,g,hg⟩ | ⟨W,g,hg⟩
  · let q' := q.comp r.ker.subtype
    let i : q'.ker →* (r.ker ⊓ q.ker : Subgroup H) :=
      { toFun := fun x => ⟨x.val.val,x.val.property,x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hi : Function.Injective i := fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : (r.ker ⊓ q.ker : Subgroup H) => (z : H)) h))
    let : Group.IsSolvable q'.ker := Group.isSolvable_of_isSolvable_injective hi
    obtain ⟨Z,k,hk⟩ := section_survives_hom hR q' W g hg
    exact hq Z k hk
  · let e := QuotientGroup.quotientKerEquivRange r
    let j := r.range.subtype.comp e.toMonoidHom
    let a := W.equivMapOfInjective j (r.range.subtype_injective.comp e.injective)
    exact hr (W.map j) (g.comp a.symm.toMonoidHom) (hg.comp a.symm.surjective)

private def flagRestriction {A V : Type*} [Group A] [Group V]
    (ρ : A →* MulAut V) (Q : Subgroup V)
    (hQ : ∀ a : A, Q.map (ρ a).toMonoidHom = Q) : A →* MulAut Q where
  toFun a := ((ρ a).subgroupMap Q).trans (MulEquiv.subgroupCongr (hQ a))
  map_one' := by ext x; change ρ 1 x = x; rw [map_one]; rfl
  map_mul' a b := by ext x; change ρ (a * b) x = ρ a (ρ b x); rw [map_mul]; rfl

private def flagQuotient {A V : Type*} [Group A] [Group V]
    (ρ : A →* MulAut V) (Q : Subgroup V) [Q.Normal]
    (hQ : ∀ a : A, Q.map (ρ a).toMonoidHom = Q) : A →* MulAut (V ⧸ Q) where
  toFun a := QuotientGroup.congr Q Q (ρ a) (hQ a)
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q x
    change QuotientGroup.mk' Q (ρ 1 x) = QuotientGroup.mk' Q x
    rw [map_one]; rfl
  map_mul' a b := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q x
    change QuotientGroup.mk' Q (ρ (a * b) x) =
      QuotientGroup.mk' Q (ρ a (ρ b x))
    rw [map_mul]; rfl

private theorem flag_kernel_square {A V : Type*} [Group A] [Group V]
    [IsElementaryAbelian 2 V] (ρ : A →* MulAut V) (Q : Subgroup V)
    (hQ : ∀ a : A, Q.map (ρ a).toMonoidHom = Q)
    (a : ((flagRestriction ρ Q hQ).ker ⊓ (flagQuotient ρ Q hQ).ker : Subgroup A)) :
    ρ a.val ^ 2 = 1 := by
  have hinv (x : V) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) x
  have hfix (x : Q) : ρ a.val x = x :=
    congrArg (fun f : MulAut Q => (f x : V)) a.property.1
  ext x
  have he := MulEquiv.congr_fun (MonoidHom.mem_ker.mp a.property.2)
    (QuotientGroup.mk' Q x)
  have hdelta : x⁻¹ * ρ a.val x ∈ Q := QuotientGroup.eq.mp he.symm
  have hh := hfix ⟨_, hdelta⟩
  change ρ a.val (x⁻¹ * ρ a.val x) = x⁻¹ * ρ a.val x at hh
  simp only [map_mul, hinv] at hh
  change ρ a.val (ρ a.val x) = x
  apply mul_left_cancel (a := ρ a.val x)
  exact hh.trans (mul_comm _ _)

private theorem flag_kernel_isPGroup {A V : Type*} [Group A] [Group V]
    [IsElementaryAbelian 2 V] (ρ : A →* MulAut V) (hρ : IsPGroup 2 ρ.ker)
    (Q : Subgroup V) (hQ : ∀ a : A, Q.map (ρ a).toMonoidHom = Q) :
    IsPGroup 2 ((flagRestriction ρ Q hQ).ker ⊓ (flagQuotient ρ Q hQ).ker : Subgroup A) := by
  intro a
  have hsquare : a.val ^ 2 ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact flag_kernel_square ρ Q hQ a
  obtain ⟨n, hn⟩ := hρ ⟨a.val ^ 2, hsquare⟩
  refine ⟨n + 1, ?_⟩
  apply Subtype.ext
  have hn' : (a.val ^ 2) ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  change a.val ^ (2 ^ (n + 1)) = 1
  rw [pow_succ, Nat.mul_comm, pow_mul]
  exact hn'

private theorem no_projective_four_section_of_flag
    {F R P : Type*} [Field F] [Finite F] [Group R] [Finite R]
    [Group.IsPerfect R] [IsSimpleGroup R] [Group P] [Finite P]
    (hF : Nat.card F = 4) (e : R ≃* PSL(3,F)) (hR : Nat.card R = 20160)
    (hP : IsPGroup 2 P) (Q : Subgroup (P ⧸ frattini P))
    (hQ : ∀ a : MulAut P, Q.map (quotientAut (frattini P) a).toMonoidHom = Q)
    (hcardQ : Nat.card Q = 16) (hcardquot : Nat.card ((P ⧸ frattini P) ⧸ Q) = 16)
    (U : Subgroup (MulAut P)) (f : U →* R) (hf : Function.Surjective f) : False := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.of_injective Q.subtype Q.subtype_injective
  let ρ := quotientAut (frattini P)
  let r := flagRestriction ρ Q hQ
  let q := flagQuotient ρ Q hQ
  have hK : IsPGroup 2 (r.ker ⊓ q.ker : Subgroup (MulAut P)) :=
    flag_kernel_isPGroup ρ (isPGroup_quotientAut_frattini_kernel hP) Q hQ
  let : Group.IsNilpotent (r.ker ⊓ q.ker : Subgroup (MulAut P)) := hK.isNilpotent
  exact no_section_of_two_actions (Group.IsPerfect.not_isSolvable R) r q
    (no_projective_four_section_aut_sixteen hF e hR hcardQ)
    (no_projective_four_section_aut_sixteen hF e hR hcardquot) U f hf

private theorem no_outer_section_of_sylow_exclusion
    {Q R : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    [Group R] [Finite R] [IsSimpleGroup R]
    (hR : ¬ Group.IsSolvable R)
    (P : Sylow 2 Q)
    (hP : ∀ (U : Subgroup (MulAut P)) (f : U →* R), ¬ Function.Surjective f)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* R) (hf : Function.Surjective f) : False := by
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  let H := MulAction.stabilizer (MulAut Q) (P : Subgroup Q)
  let F := fixingSubgroup (MulAut Q) (P : Set Q)
  let r : H →* MulAut P :=
    { toFun := fun a => (a.val.subgroupMap (P : Subgroup Q)).trans
        (MulEquiv.subgroupCongr a.property)
      map_one' := by ext x; rfl
      map_mul' := by intro a b; ext x; rfl }
  let i : r.ker →* F :=
    (H.subtype.comp r.ker.subtype).codRestrict F (by
      intro a
      apply (mem_fixingSubgroup_iff (MulAut Q)).mpr
      intro x hx
      change (a.val.val : MulAut Q) x = x
      exact congrArg (fun b : MulAut P => ((b ⟨x,hx⟩ : P) : Q)) a.property)
  have hi : Function.Injective i := by
    intro a b hab
    have hab' : (a.val.val : MulAut Q) = b.val.val :=
      congrArg (fun z : F => (z : MulAut Q)) hab
    exact Subtype.ext (Subtype.ext hab')
  let : Group.IsSolvable r.ker := Group.isSolvable_of_isSolvable_injective hi
  let q := (QuotientGroup.mk' (MulAut.innerSubgroup Q)).comp H.subtype
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup Q) x
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Q (a • P) P
    have hm : MulAut.conj g * a ∈ H := by
      change (MulAut.conj g * a) • (P : Subgroup Q) = (P : Subgroup Q)
      rw [mul_smul]
      exact congrArg Sylow.toSubgroup hg
    refine ⟨⟨MulAut.conj g * a,hm⟩,?_⟩
    change QuotientGroup.mk' (MulAut.innerSubgroup Q) (MulAut.conj g * a) = _
    have hi : QuotientGroup.mk' (MulAut.innerSubgroup Q) (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
    rw [map_mul,hi,one_mul]
  obtain ⟨W,g,hg⟩ := simple_section_quotient_of_solvable_kernel hR r.ker
    (U.comap q) (f.comp (q.subgroupComap U))
    (hf.comp (q.subgroupComap_surjective_of_surjective U hq))
  let e := QuotientGroup.quotientKerEquivRange r
  let j := r.range.subtype.comp e.toMonoidHom
  let a := W.equivMapOfInjective j (r.range.subtype_injective.comp e.injective)
  exact hP (W.map j)
    (g.comp a.symm.toMonoidHom) (hg.comp a.symm.surjective)

open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The remaining linear field-four simple quotient cannot occur in the
actual outer automorphism group of a PSU₅(4) component cover. -/
theorem moved_outer_not_unitary_five_four {A : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 5 4) : False := by
  let := S.source.toHypothesis1221.quasisimple
  let : IsSimpleGroup (coreCentralQuotient L) := IsQuasisimple.simple
  let : Group.IsPerfect (coreCentralQuotient L) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center (L ⧸ pCore 2 L))) (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  have hB : ChapterA.Section02.IsTheoremBModel (K ⧸ center K) :=
    .rank_two 2 (.unitary_five rfl (by simpa using hm))
  obtain ⟨hd,⟨em⟩⟩ := moved_outer_linear_field_four D S K hK hB ho
  have hF : Nat.card S.field.Carrier = 4 := by rw [S.field.card_eq,hd]; decide
  let ec : coreCentralQuotient L ≃* PSL(3,S.field.Carrier) :=
    QuotientGroup.congr _ _ em (FixedElementary.map_center em)
  have hc : Nat.card (coreCentralQuotient L) = 20160 := by
    have hcard := card_eq_card_quotient_mul_card_subgroup (center (L ⧸ pCore 2 L))
    have hz : Nat.card (center (L ⧸ pCore 2 L)) = 3 := by
      rw [Nat.card_congr (centerCongr em).toEquiv,Atlas.ExceptionalSupport.card_sl_center]
      norm_num [hF]
    rw [hz,Nat.card_congr em.toEquiv,linear_three_order,hF] at hcard
    change Nat.card ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) = 20160
    omega
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.UnitaryFive.charP_two_of_card_sixteen hcard
  obtain ⟨a⟩ := Theory.SpecificGroups.UnitaryFive.projective_equiv_identity_four J hcard hconj
  let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
  obtain ⟨Q,hQ,hcardQ,hcardquot⟩ :=
    Theory.SpecificGroups.UnitaryFive.Flag.sylow_invariant_frattini_flag_four
      (BenderSuzuki.MatrixGroups.HermitianForm.IdentityGram.identityGram J)
      hcard hconj rfl (e.trans a) P
  obtain ⟨U,f,hfs⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let b := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  exact no_outer_section_of_sylow_exclusion
    (Group.IsPerfect.not_isSolvable (coreCentralQuotient L)) P
    (no_projective_four_section_of_flag hF ec hc P.isPGroup' Q hQ hcardQ hcardquot)
    (U.map j) (f.comp b.symm.toMonoidHom) (hfs.comp b.symm.surjective)

open Chapter4 Chapter4.Section04
/-- Both inner placement and outer action exclude the entire PSU₅(4) row
for the same full moved component and the original module. -/
theorem moved_component_not_unitary_five_four {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 5 4) : False := by
  rcases moved_component_inner_or_outer_section D S hA hodd K hK with hi | ho
  · obtain ⟨_,_,_,_,himage,_⟩ :=
      moved_component_placement_of_inner D S hA hodd hu hout K hK houtK hi
    exact himage.not_unitary_five_four D S hm
  · exact moved_outer_not_unitary_five_four D S K hK ho hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
