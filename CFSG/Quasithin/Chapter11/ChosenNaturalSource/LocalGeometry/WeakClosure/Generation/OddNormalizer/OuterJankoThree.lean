module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterUnitaryFive
public import Theory.GroupTheory.ElementaryThirtyTwoThirtyOneNormalizer
public import Theory.Representation.NormalInvariants
public import Theory.Representation.TwoDimensionalOddOrder
public import Theory.Representation.Quotient

/-!
# The field-four outer section cannot occur on a J₃ component

The actual J₃ Sylow subgroup has Frattini quotient of order at most 32.
Sylow conjugacy and the solvable pointwise fixer retain a nonsolvable
simple outer section inside its full automorphism group; the Frattini
kernel then transfers that section to GLₙ(2), n ≤ 5.

For n ≤ 4, orders make a PSL₃(4) section map an isomorphism. For n = 5,
its kernel has order dividing 16·31. A nontrivial 31-part would be normal
and place the entire section inside an odd-order Singer normalizer. Thus
the kernel is a two-group. It acts trivially on an irreducible constituent,
which descends to PSL₃(4) and contradicts its minimum binary degree nine.

Central descent retains the full component cover. The inner-placement
case is already excluded by J₃'s two-part; hence this excludes both actions
on the same actual moved component. Source applies this result to the
original elementary odd actor and the literal Hall kernel, retaining V
and the full SL₃(4) cover. The other outer and moved-J₄ cases stay with
qt-d-1222-natural-odd-kernel-normalizer.

Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622, using I.3.1,
the native ATLAS J₃ Sylow certificate, and the PSL₃(4) degree theorem
from GLS III §§2.8.6, 2.8.8 and 2.8.10(c).
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

private theorem characteristic_thirtyone_of_card_dvd
    {N : Type*} [Group N] [Finite N] (hd : Nat.card N ∣ 496)
    (h31 : 31 ∣ Nat.card N) (P : Sylow 31 N) :
    Nat.card P = 31 ∧ (P : Subgroup N).Characteristic := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  have hbound : Nat.card N ≤ 496 := Nat.le_of_dvd (by decide) hd
  have hPbound : Nat.card P ≤ 496 :=
    (Nat.card_le_card_of_injective (P : Subgroup N).subtype
      (P : Subgroup N).subtype_injective).trans hbound
  obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
  have hn1 : n = 1 := by
    have hp := P.dvd_card_of_dvd_card h31
    rw [hn] at hp hPbound
    have hnlt : n < 2 := by
      by_contra hnlt
      have hh := Nat.pow_le_pow_right (by decide : 0 < 31) (by omega : 2 ≤ n)
      norm_num at hh
      omega
    interval_cases n <;> norm_num at *
  have hP : Nat.card P = 31 := by simpa [hn1] using hn
  have hidx : P.index ≤ 16 := by
    have hi := P.index_mul_card
    rw [hP] at hi
    omega
  have hnSylow : Nat.card (Sylow 31 N) ≤ 16 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero P.index_ne_zero_of_finite) P.card_dvd_index).trans hidx
  have hmod := card_sylow_modEq_one 31 N
  have hcard : Nat.card (Sylow 31 N) = 1 := by
    change Nat.card (Sylow 31 N) % 31 = 1 % 31 at hmod
    omega
  let : Subsingleton (Sylow 31 N) := (Nat.card_eq_one_iff_unique.mp hcard).1
  exact ⟨hP,inferInstance⟩

private theorem kernel_two_of_aut_thirtytwo
    {R E : Type*} [Group R] [Finite R] [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hR : Nat.card R = 20160) (hE : Nat.card E = 32)
    (U : Subgroup (MulAut E)) (f : U →* R) (hf : Function.Surjective f) :
    IsPGroup 2 f.ker := by
  have hAut : Nat.card (MulAut E) = 9999360 := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E 5 (by simpa using hE)]
    norm_num [Fin.prod_univ_succ]
  have hN : Nat.card f.ker ∣ 496 := by
    have hdiv := U.card_subgroup_dvd_card
    have hmul := f.ker.card_mul_index
    rw [index_ker] at hmul
    rw [f.range_eq_top.mpr hf,card_top,hR] at hmul
    rw [←hmul,hAut] at hdiv
    exact (Nat.mul_dvd_mul_iff_right (by decide : 0 < 20160)).mp
      (show Nat.card f.ker * 20160 ∣ 496 * 20160 from hdiv)
  have hnot : ¬31 ∣ Nat.card f.ker := by
    intro h31
    let P : Sylow 31 f.ker := default
    obtain ⟨hP,hchar⟩ := characteristic_thirtyone_of_card_dvd hN h31 P
    let : (P : Subgroup f.ker).Characteristic := hchar
    let C : Subgroup U := (P : Subgroup f.ker).map f.ker.subtype
    let : C.Normal := by
      refine ⟨?_⟩
      rintro c ⟨p,hp,rfl⟩ u
      exact ⟨(MulAut.conjNormal u) p,
        characteristic_iff_le_comap.mp hchar (MulAut.conjNormal u) hp,rfl⟩
    have hC : Nat.card C = 31 := by
      rw [card_map_of_injective f.ker.subtype_injective]
      exact hP
    let B : Subgroup (MulAut E) := C.map U.subtype
    have hB : Nat.card B = 31 := by
      rw [card_map_of_injective U.subtype_injective]
      exact hC
    have hnorm : U ≤ normalizer (B : Set (MulAut E)) := by
      have hh := C.le_normalizer_map U.subtype
      simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
    have ho : Odd (Nat.card U) :=
      (odd_card_normalizer_of_elementary_thirtytwo_thirtyone E hE B hB).of_dvd_nat
        (card_dvd_of_le hnorm)
    have hdiv := card_dvd_of_surjective f hf
    rw [hR] at hdiv
    have hodd : Odd 20160 := ho.of_dvd_nat hdiv
    norm_num at hodd
  have h16 : Nat.card f.ker ∣ 16 := by
    have hco : Nat.Coprime (Nat.card f.ker) 31 :=
      ((show Nat.Prime 31 by decide).coprime_iff_not_dvd.mpr hnot).symm
    exact hco.dvd_of_dvd_mul_right (show Nat.card f.ker ∣ 16 * 31 from hN)
  exact IsPGroup.of_card_dvd_pow (n := 4) h16

private theorem normal_two_le_ker
    {H W : Type*} [Group H] [Finite H] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) [ρ.IsIrreducible]
    (N : Subgroup H) [N.Normal] (hN : IsPGroup 2 N) : N ≤ ρ.ker := by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial ρ
  have hchar : ringChar (ZMod 2) ≠ 0 := by norm_num [ZMod.ringChar_zmod_n]
  obtain ⟨v,hv,hfix⟩ := pGroup_fix_nonzero_vector hchar
    (by simpa [ZMod.ringChar_zmod_n] using hN) (ρ.comp N.subtype)
  apply le_ker_of_normal_invariants_ne_bot ρ N
  intro he
  have hm : v ∈ invariants (ρ.comp N.subtype) := hfix
  rw [he,Submodule.mem_bot] at hm
  exact hv hm

private theorem no_projective_four_section_aut_thirtytwo
    {F R E : Type*} [Field F] [Finite F] [Group R] [Finite R]
    [Group.IsPerfect R] [Nontrivial R] [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hF : Nat.card F = 4) (e : R ≃* PSL(3,F)) (hR : Nat.card R = 20160)
    (hE : Nat.card E = 32) (U : Subgroup (MulAut E))
    (f : U →* R) (hf : Function.Surjective f) : False := by
  let ρ : Representation (ZMod 2) U (Additive E) :=
    { toFun := fun g =>
        { (g.val).toAdditive.toAddMonoidHom with map_smul' := ZMod.map_smul g.val.toAdditive }
      map_one' := by ext x; rfl
      map_mul' := by intro a b; ext x; rfl }
  have hρ : Function.Injective ρ := by
    intro a b he
    apply Subtype.ext
    ext x
    exact DFunLike.congr_fun he (Additive.ofMul x)
  have hdim : Module.finrank (ZMod 2) (Additive E) = 5 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    change Nat.card E = _ at hc
    simpa only [Nat.card_zmod,hE] using hc.symm
  have hn : ¬solvableResidual U ≤ ρ.ker := by
    intro hn
    have hp : solvableResidual U = ⊥ := le_bot_iff.mp
      (hn.trans ((MonoidHom.ker_eq_bot_iff ρ).mpr hρ).le)
    have hm := map_solvableResidual_eq f hf
    rw [hp,Subgroup.map_bot,solvableResidual_eq_top] at hm
    exact bot_ne_top hm
  obtain ⟨X,N,hi,hN⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect
    (ρ := ρ) (solvableResidual U) hn
  let σ := N.quotientRepresentation
  let : σ.IsIrreducible := hi
  have hker := normal_two_le_ker σ f.ker (kernel_two_of_aut_thirtytwo hR hE U f hf)
  let a := QuotientGroup.quotientKerEquivOfSurjective f hf
  let τ : Representation (ZMod 2) R (X.toSubmodule ⧸ N.toSubmodule) :=
    (σ.quotientOfLEKer f.ker hker).comp a.symm.toMonoidHom
  have heq : τ.comp f = σ := by
    apply MonoidHom.ext
    intro g
    change (σ.quotientOfLEKer f.ker hker) (a.symm (f g)) = σ g
    have ha : a.symm (f g) = QuotientGroup.mk' f.ker g := by
      apply a.injective
      simp only [MulEquiv.apply_symm_apply]
      rfl
    rw [ha]
    rfl
  let : τ.IsIrreducible := (irreducible_comp_surjective_iff f hf τ).mp (heq ▸ hi)
  have hnt : ∃ g, τ g ≠ 1 := by
    by_contra! ht
    apply hN
    intro g hg
    have hh : τ (f g) = σ g := DFunLike.congr_fun heq g
    exact hh.symm.trans (ht (f g))
  have h9 := Representation.PSL3Four.finrank_ge_nine_of_equiv hF e τ hnt
  have h5 := (Submodule.finrank_quotient_le N.toSubmodule).trans
    (Submodule.finrank_le X.toSubmodule)
  rw [hdim] at h5
  omega

open Theory.GroupTheory
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

private theorem no_projective_four_section_aut_le_thirtytwo
    {F R E : Type*} [Field F] [Finite F] [Group R] [Finite R]
    [Group.IsPerfect R] [Nontrivial R] [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hF : Nat.card F = 4) (e : R ≃* PSL(3,F)) (hR : Nat.card R = 20160)
    (hE : Nat.card E ≤ 32) (U : Subgroup (MulAut E))
    (f : U →* R) (hf : Function.Surjective f) : False := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hn5 : n ≤ 5 := by
    have hp : 2 ^ n < 2 ^ 6 := by rw [←hn]; omega
    have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hp
    omega
  rcases eq_or_lt_of_le hn5 with he | hlt
  · exact no_projective_four_section_aut_thirtytwo hF e hR (by simpa [he] using hn) U f hf
  have hAut : Nat.card (MulAut E) ≤ 20160 := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E n hn]
    interval_cases n <;> norm_num [Fin.prod_univ_succ]
  have hb : Function.Bijective f := hf.bijective_of_nat_card_le (by
    rw [hR]
    exact (Nat.card_le_card_of_injective U.subtype U.subtype_injective).trans hAut)
  let φ : R →* MulAut E := U.subtype.comp (MulEquiv.ofBijective f hb).symm.toMonoidHom
  have hφ : Function.Injective φ := U.subtype_injective.comp (MulEquiv.ofBijective f hb).symm.injective
  let ρ : Representation (ZMod 2) R (Additive E) :=
    { toFun := fun g =>
        { (φ g).toAdditive.toAddMonoidHom with map_smul' := ZMod.map_smul (φ g).toAdditive }
      map_one' := by ext x; change φ 1 x = x; rw [map_one]; rfl
      map_mul' := by intro a b; ext x; change φ (a*b) x = φ a (φ b x); rw [map_mul]; rfl }
  have hdim : Module.finrank (ZMod 2) (Additive E) = n := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    change Nat.card E = _ at hc
    simpa only [Nat.card_zmod,hn] using hc.symm
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

/-- A two-group with Frattini quotient of order at most 32 has no PSL₃(4)
section in its full automorphism group. -/
theorem no_projective_four_section_of_frattini_le_thirtytwo
    {F R P : Type*} [Field F] [Finite F] [Group R] [Finite R]
    [Group.IsPerfect R] [IsSimpleGroup R] [Group P] [Finite P]
    (hF : Nat.card F = 4) (e : R ≃* PSL(3,F)) (hR : Nat.card R = 20160)
    (hP : IsPGroup 2 P) (hcard : Nat.card (P ⧸ frattini P) ≤ 32)
    (U : Subgroup (MulAut P)) (f : U →* R) (hf : Function.Surjective f) : False := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let q := quotientAut (frattini P)
  let : Group.IsNilpotent q.ker := (isPGroup_quotientAut_frattini_kernel hP).isNilpotent
  obtain ⟨W,g,hg⟩ := section_survives_hom (Group.IsPerfect.not_isSolvable R) q U f hf
  exact no_projective_four_section_aut_le_thirtytwo hF e hR hcard W g hg

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

/-- Any actual component with a Sylow Frattini quotient of order at most 32
cannot carry the required outer section. The full component cover is retained. -/
theorem moved_outer_not_of_frattini_le_thirtytwo {A : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f)
    (hB : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (P : Sylow 2 (K ⧸ center K))
    (hbound : Nat.card (P ⧸ frattini P) ≤ 32) : False := by
  let := S.source.toHypothesis1221.quasisimple
  let : IsSimpleGroup (coreCentralQuotient L) := IsQuasisimple.simple
  let : Group.IsPerfect (coreCentralQuotient L) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center (L ⧸ pCore 2 L))) (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
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
  obtain ⟨U,f,hfs⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let b := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  exact no_outer_section_of_sylow_exclusion
    (Group.IsPerfect.not_isSolvable (coreCentralQuotient L)) P
    (no_projective_four_section_of_frattini_le_thirtytwo hF ec hc P.isPGroup' hbound)
    (U.map j) (f.comp b.symm.toMonoidHom) (hfs.comp b.symm.surjective)

/-- The actual J₃ outer group has no section of the required field-four type. -/
theorem moved_outer_not_janko_three {A : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f)
    (e : (K ⧸ center K) ≃* Sporadic.Janko3.Model) : False := by
  let P : Sylow 2 (K ⧸ center K) := default
  exact moved_outer_not_of_frattini_le_thirtytwo D S K hK ho
    (.sporadic (Or.inl ⟨.j3,⟨e⟩⟩)) P
    (Theory.SpecificGroups.FiniteModelSylowFrattini.j3_card_le_thirtytwo e P)

open Chapter4 Chapter4.Section04
/-- The same actual component cannot have J₃ central quotient in either action. -/
theorem moved_component_not_janko_three {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (e : (K ⧸ center K) ≃* Sporadic.Janko3.Model) : False := by
  rcases moved_component_inner_or_outer_section D S hA hodd K hK with hi | ho
  · obtain ⟨_,_,_,_,_,_,hdiv⟩ :=
      moved_component_placement_of_inner D S hA hodd hu hout K hK houtK hi
    rw [Nat.card_congr e.toEquiv,Sporadic.Janko3.model_card] at hdiv
    norm_num at hdiv
  · exact moved_outer_not_janko_three D S K hK ho e

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
