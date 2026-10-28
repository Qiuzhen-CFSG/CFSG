module

public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.SylowActors
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.PairedContainers
public import Theory.SpecificGroups.PSL2.PrimeInvolutionCentralizerMaximal
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.LinearThree
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.Borel
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableRootOrbit
public import Theory.GroupTheory.SylowNormalizerCentralQuotient
public import Theory.GroupTheory.SolvableSylowControl.Marked
public import Theory.GroupTheory.PerfectNormalizerLift

/-!
# Classical containing rows in the local Cartan sieve

Over the fixed Sylow in PSL₃(2ᵐ) or Sp₄(2ᵐ), the proper local C-components
are exactly the two parabolic residuals. An odd automorphism preserving
that Sylow fixes both. The same conclusion lifts to SL₃ through the
central projection because local C-components are perfect. Solvability of the original Cartan--Sylow join
makes its action preserve the containing component's Sylow subgroup.
Applying this to every conjugate of the source seed controls its entire
orbit, which is the original residual, even when the seed is moved.

The proof uses the actual image in Y/O₂(Y), identified with C/O₂(C),
and lifts its normalizer through the original quotient. Normality of C
is derived from the nonnormal-component catalogue: its remaining rows
have two-part at most eight, whereas all three models here have a factor
sixteen. Thus the original escape excludes all three classical
rows for every m > 1, without a cubic or an assumption on the left degree.

The fixed-Sylow placements refine the proofs in Chapter A's
SourceEmbeddings/FiveLocalFF/{LinearThree,Symplectic}.lean. Other source rows remain distinct obligations.
Source: Aschbacher--Smith 5.1.12--13, printed pp.635--636,
using A.3.12 and 1.2.1(3), refs/quasithin.pdf.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

private theorem odd_fixes_two {E : Type*} [Group E] {M : Type*} [MulAction E M]
    (P : M → Prop) (x y : M) (hP : ∀ z, P z → z = x ∨ z = y)
    (a : E) (ha : Odd (orderOf a)) (hmap : ∀ z, P z → P (a • z))
    {z : M} (hz : P z) : a • z = z := by
  have hs : a • (a • z) = z := by
    have h0 := hP z hz
    have h1 := hP (a • z) (hmap z hz)
    have h2 := hP (a • (a • z)) (hmap (a • z) (hmap z hz))
    have hi := MulAction.injective (β := M) a
    rcases h0 with rfl | rfl <;> rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;> grind
  have hm : a ^ 2 ∈ MulAction.stabilizer E z := by
    simpa only [MulAction.mem_stabilizer_iff, pow_two, mul_smul] using hs
  obtain ⟨k,hk⟩ := exists_pow_eq_pow_two_mul (pow_orderOf_eq_one a) ha 1
  rw [pow_one, pow_mul] at hk
  exact MulAction.mem_stabilizer_iff.mp (hk ▸ (MulAction.stabilizer E z).pow_mem hm k)

omit [Finite G] in
private theorem proper_local_join {S B : Subgroup G}
    [IsSimpleGroup G] (hB : B ∈ localCComponents S) (hb : B ≠ ⊤) : B ⊔ S ≠ ⊤ := by
  intro ht
  have hc : B.IsCComponent := by
    change (B.subgroupOf (B ⊔ S)).IsCComponent at hB
    rw [ht] at hB
    simpa only [map_subgroupOf_eq_of_le le_top] using hB.map_subtype (.top)
  exact (hc.subnormal.eq_bot_or_top_of_isSimpleGroup inferInstance).elim hc.ne_bot hb

omit [Finite G] in
private theorem local_perfect {S B : Subgroup G} (hB : B ∈ localCComponents S) :
    Group.IsPerfect B := by
  let := hB.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective

private theorem linear_standard_locals
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (B : Subgroup PSL(3,F))
    (hB : B ∈ localCComponents (Matrix.PSL3.LinearThree.unipotent F)) (hb : B ≠ ⊤) :
    B = Matrix.PSL3.LinearThree.pointLocal F ∨ B = Matrix.PSL3.LinearThree.lineLocal F := by
  open Matrix.PSL3.LinearThree in
  have hlarge : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  let := local_perfect hB
  have hp := Matrix.PSL3.LinearThree.UnipotentOvergroups.overgroup_unipotent F
    (B ⊔ Matrix.PSL3.LinearThree.unipotent F) le_sup_right (proper_local_join hB hb)
  open Matrix.PSL3.LinearThree in
  rcases hp with hp | hp
  · left
    let := pointLocal_isPerfect F hlarge
    apply FiveLocalFF.local_eq_of_sl2_core_quotient (pointLocal F) (by omega)
      (pointLocalCoreQuotientEquiv F) (unipotentSylow F (by omega) hF) B hB
    · rw [← ParabolicResiduals.pointParabolic_residual F hlarge]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hp)
    · exact unipotent_le_pointLocal F
  · right
    let := lineLocal_isPerfect F hlarge
    apply FiveLocalFF.local_eq_of_sl2_core_quotient (lineLocal F) (by omega)
      (lineLocalCoreQuotientEquiv F) (unipotentSylow F (by omega) hF) B hB
    · rw [← ParabolicResiduals.lineParabolic_residual F hlarge]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hp)
    · exact unipotent_le_lineLocal F

private theorem local_map_automorphism {S B : Subgroup G}
    (hB : B ∈ localCComponents S) (a : MulAut G) (ha : S.map a.toMonoidHom = S) :
    B.map a.toMonoidHom ∈ localCComponents S := by
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  simpa only [ha] using Chapter1.Section02.localCComponents_map_of_solvable_ker hB a.toMonoidHom

omit [Finite G] in
private theorem map_aut_congr {E : Type*} [Group E]
    (e : G ≃* E) (a : MulAut G) (B : Subgroup G) :
    (B.map a.toMonoidHom).map e.toMonoidHom =
      (B.map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp [MulAut.congr_apply]

/-- An odd Sylow-preserving automorphism fixes local components when there
are at most two proper local components. -/
theorem odd_local_fixed_of_two {S : Subgroup G}
    (P Q : Subgroup G)
    (hc : ∀ R : Subgroup G, R ∈ localCComponents S → R ≠ ⊤ → R = P ∨ R = Q)
    (a : MulAut G) (ha : Odd (orderOf a)) (hS : S.map a.toMonoidHom = S)
    (R : Subgroup G) (hr : R ∈ localCComponents S) : R.map a.toMonoidHom = R := by
  by_cases ht : R = ⊤
  · subst R
    exact map_top_of_surjective _ a.surjective
  apply odd_fixes_two (fun R => R ∈ localCComponents S ∧ R ≠ ⊤) P Q
    (fun _ h => hc _ h.1 h.2) a ha _ ⟨hr,ht⟩
  intro B hb
  refine ⟨local_map_automorphism hb.1 a hS,?_⟩
  intro he
  apply hb.2
  apply map_injective (f := a.toMonoidHom) a.injective
  exact he.trans (map_top_of_surjective a.toMonoidHom a.surjective).symm

/-- An odd Sylow-preserving automorphism fixes every local component of PSL₃(2ⁿ). -/
private theorem linear_odd_local_fixed
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 PSL(3,F)) (a : MulAut PSL(3,F))
    (ha : Odd (orderOf a)) (hS : (S : Subgroup PSL(3,F)).map a.toMonoidHom = S)
    (R : Subgroup PSL(3,F)) (hr : R ∈ localCComponents S) : R.map a.toMonoidHom = R := by
  obtain ⟨_,e,_,he⟩ := SolvableSylowControl.exists_aligned_equiv (MulEquiv.refl PSL(3,F))
    S (Matrix.PSL3.LinearThree.unipotentSylow F (by omega) hF)
  change (S : Subgroup PSL(3,F)).map e.toMonoidHom = Matrix.PSL3.LinearThree.unipotent F at he
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  have hl := Chapter1.Section02.localCComponents_map_of_solvable_ker hr e.toMonoidHom
  rw [he] at hl
  have hα : (Matrix.PSL3.LinearThree.unipotent F).map (MulAut.congr e a).toMonoidHom =
      Matrix.PSL3.LinearThree.unipotent F := by
    rw [←he,←map_aut_congr,hS]
  have ho : Odd (orderOf (MulAut.congr e a)) := by
    exact (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective _).symm ▸ ha
  have hh := odd_local_fixed_of_two _ _ (linear_standard_locals hF hn)
    (MulAut.congr e a) ho hα (R.map e.toMonoidHom) hl
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_aut_congr]
  exact hh

omit [Finite G] in
private theorem odd_actor_normalizes_local
    (hcontrol : SolvableSylowControl 2 G)
    (hfixed : ∀ (S : Sylow 2 G) (a : MulAut G), Odd (orderOf a) →
      (S : Subgroup G).map a.toMonoidHom = S →
      ∀ R : Subgroup G, R ∈ localCComponents S → R.map a.toMonoidHom = R)
    {E : Type*} [Group E] [Finite E] (T : Sylow 2 E)
    (C A : Subgroup E) [C.Normal] (e : C ≃* G)
    (hodd : Odd (Nat.card A)) (hsol : Group.IsSolvable (A ⊔ (T : Subgroup E) : Subgroup E))
    {R : Subgroup E} (hr : R ∈ localCComponents T) (hRC : R ≤ C) :
    A ≤ normalizer (R : Set E) := by
  obtain ⟨S,hS,hl⟩ := exists_local_sylow_restriction T hr hRC
    (inferInstance : C.Normal).isSubnormal
  have hc := SolvableSylowControl.of_equiv e hcontrol
  let := hsol
  have hn := hc.normalizes_sylow C (A ⊔ (T : Subgroup E)) S
    (by rw [C.normalizer_eq_top]; exact le_top)
    (by rw [hS]; exact (subgroupOf_map_subtype T C).le.trans inf_le_left |>.trans le_sup_right)
  have hR : R.subgroupOf C ∈ localCComponents S := hl
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  have hm := Chapter1.Section02.localCComponents_map_of_solvable_ker hR e.toMonoidHom
  intro a ha
  let ac : MulAut C := C.normalizerMonoidHom ⟨a,by rw [C.normalizer_eq_top]; exact mem_top a⟩
  have hs : (S : Subgroup C).map ac.toMonoidHom = S := by
    apply map_injective C.subtype_injective
    have heq : ((S : Subgroup C).map ac.toMonoidHom).map C.subtype =
        ((S : Subgroup C).map C.subtype).map (MulAut.conj a).toMonoidHom := by
      rw [map_map,map_map]
      rfl
    rw [heq]
    exact mem_normalizer_iff_map_conj_eq.mp (hn (mem_sup_left ha))
  have hoa : Odd (orderOf a) := by
    exact (orderOf_coe (⟨a,ha⟩ : A)).symm ▸ hodd.of_dvd_nat (orderOf_dvd_natCard (⟨a,ha⟩ : A))
  have hoc : Odd (orderOf ac) := hoa.of_dvd_nat
    ((orderOf_map_dvd C.normalizerMonoidHom _).trans (by
      rw [←orderOf_coe]))
  have ho : Odd (orderOf (MulAut.congr e ac)) := by
    exact (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective _).symm ▸ hoc
  have hs' : ((S : Subgroup C).map e.toMonoidHom).map (MulAut.congr e ac).toMonoidHom =
      (S : Subgroup C).map e.toMonoidHom := by rw [←map_aut_congr,hs]
  have hf := hfixed (S.mapSurjective e.surjective) (MulAut.congr e ac) ho hs'
    ((R.subgroupOf C).map e.toMonoidHom) hm
  have hcr : (R.subgroupOf C).map ac.toMonoidHom = R.subgroupOf C := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_aut_congr]
    exact hf
  apply mem_normalizer_iff_map_conj_eq.mpr
  have heq : ((R.subgroupOf C).map ac.toMonoidHom).map C.subtype =
      ((R.subgroupOf C).map C.subtype).map (MulAut.conj a).toMonoidHom := by
    rw [map_map,map_map]
    rfl
  rw [hcr,map_subgroupOf_eq_of_le hRC] at heq
  exact heq.symm

section Symplectic
open Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem nonsolvable_sylow_cover_eq_top {A : Type*} [Group A] [Finite A]
    (f : A →* Matrix.SpecialLinearGroup (Fin 2) F) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (S : Sylow 2 A) (H : Subgroup A)
    (hSH : (S : Subgroup A) ≤ H) (hH : ¬ Group.IsSolvable H) : H = ⊤ := by
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  let : Group.IsSolvable f.ker := inferInstance
  have him : H.map f = ⊤ := by
    by_contra hne
    let := Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup
      (S.mapSurjective hf) (H.map f) (map_mono hSH) hne
    let := isSolvable_comap_of_solvable_ker f (H.map f)
    exact hH (Group.isSolvable_of_isSolvable_injective
      (f := inclusion (le_comap_map f H)) (inclusion_injective _))
  have hh := congrArg (comap f) him
  simpa only [comap_map_eq, comap_top,
    sup_eq_left.mpr ((hk.le_sylow_of_normal S).trans hSH)] using hh

omit [Finite F] in
private theorem sylow_le_determinantKernel (W : Submodule F (Vector F))
    (S : Sylow 2 (Sp F)) (hS : (S : Subgroup (Sp F)) ≤ stabilizer W) :
    (S : Subgroup (Sp F)) ≤ determinantKernel W := by
  intro t ht
  let x : stabilizer W := ⟨t, hS ht⟩
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_pow_pow_eq_one ⟨t, ht⟩
  have hx : x ^ (2 ^ n) = 1 := Subtype.ext (congrArg (fun y : S => (y : Sp F)) hn)
  have hp : ((determinantCharacter W x : Fˣ) : F) ^ (2 ^ n) = 1 := by
    have he := congrArg (fun u : Fˣ => (u : F)) (congrArg (determinantCharacter W) hx)
    simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using he
  have hc : determinantCharacter W x = 1 := by
    apply Units.ext
    exact (iterateFrobenius_inj F 2 n) (by simpa [iterateFrobenius_def] using hp)
  exact ⟨x, hc, rfl⟩

private theorem local_eq_determinantKernel
    (W : Submodule F (Vector F))
    (f : determinantKernel W →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hcomp : ∀ C : Subgroup (determinantKernel W), C.IsCComponent → C = ⊤)
    (S : Sylow 2 (Sp F)) (B : Subgroup (Sp F))
    (hB : B ∈ localCComponents S) (hpar : B ⊔ (S : Subgroup (Sp F)) ≤ stabilizer W) :
    B = determinantKernel W := by
  let := local_perfect hB
  have hBK : B ≤ determinantKernel W :=
    (le_map_solvableResidual_of_isPerfect B (stabilizer W) (le_sup_left.trans hpar)).trans
      (determinantKernel_solvableResidual_le W)
  have hSK := sylow_le_determinantKernel W S (le_sup_right.trans hpar)
  have hHK : B ⊔ (S : Subgroup (Sp F)) ≤ determinantKernel W := sup_le hBK hSK
  have hne : ¬ Group.IsSolvable ((B ⊔ (S : Subgroup (Sp F))).subgroupOf (determinantKernel W)) := by
    intro hsol
    let := hsol
    let j : B.subgroupOf (B ⊔ (S : Subgroup (Sp F))) →*
        (B ⊔ (S : Subgroup (Sp F))).subgroupOf (determinantKernel W) :=
      { toFun := fun b => ⟨⟨b.val.val, hBK b.property⟩, b.val.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact hB.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := j) (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x => x.val.val) h))))
  have ht := nonsolvable_sylow_cover_eq_top f hf hk (S.subtype hSK)
    ((B ⊔ (S : Subgroup (Sp F))).subgroupOf (determinantKernel W))
    (fun _ hs => (show (S : Subgroup (Sp F)) ≤ B ⊔ (S : Subgroup (Sp F)) from le_sup_right) hs) hne
  have hjoin : B ⊔ (S : Subgroup (Sp F)) = determinantKernel W :=
    le_antisymm hHK (subgroupOf_eq_top.mp ht)
  have hc : (B.subgroupOf (determinantKernel W)).IsCComponent := by
    change (B.subgroupOf (B ⊔ (S : Subgroup (Sp F)))).IsCComponent at hB
    rwa [hjoin] at hB
  exact le_antisymm hBK (subgroupOf_eq_top.mp (hcomp _ hc))


private theorem symplectic_standard_locals {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (B : Subgroup (Sp F)) (hB : B ∈ localCComponents unipotent) (hb : B ≠ ⊤) :
    B = pointLocal ∨ B = planeLocal := by
  have hlarge : 3 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 3 < 2^2)
      (Nat.pow_le_pow_right (by decide) (by omega))
  let : IsSimpleGroup (Sp F) := (MulEquiv.isSimpleGroup_congr EvenProjective.equiv).mpr
    (SimpleQuotients.isSimpleGroup hlarge)
  rcases TwoConjugate.proper_unipotent_overgroup_le_parabolic hF (by omega)
    (B ⊔ unipotent) le_sup_right (proper_local_join hB hb) with hp | hp
  · exact .inl (local_eq_determinantKernel (point F) pointQuotient pointQuotient_surjective
      (IsElementaryAbelian.isPGroup 2 (pointRadical (F := F)))
      (fun C hC => (pointNaturalExtension hF hn).cComponent_eq_top (by omega) hC)
      (unipotentSylow hF (by omega)) B hB hp)
  · exact .inr (local_eq_determinantKernel (plane F) Plane.quotientMap Plane.quotientMap_surjective
      (IsElementaryAbelian.isPGroup 2 (Plane.radical (F := F)))
      (fun C hC => (planeNaturalExtension hF hn).cComponent_eq_top (by omega) hC)
      (unipotentSylow hF (by omega)) B hB hp)

/-- An odd Sylow-preserving automorphism fixes each local component of Sp₄(2ⁿ). -/
private theorem symplectic_odd_local_fixed {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Sp F)) (a : MulAut (Sp F))
    (ha : Odd (orderOf a)) (hS : (S : Subgroup (Sp F)).map a.toMonoidHom = S)
    (R : Subgroup (Sp F)) (hr : R ∈ localCComponents S) : R.map a.toMonoidHom = R := by
  obtain ⟨_,e,_,he⟩ := SolvableSylowControl.exists_aligned_equiv (MulEquiv.refl (Sp F))
    S (unipotentSylow hF (by omega))
  change (S : Subgroup (Sp F)).map e.toMonoidHom = unipotent at he
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  have hl := Chapter1.Section02.localCComponents_map_of_solvable_ker hr e.toMonoidHom
  rw [he] at hl
  have hα : unipotent.map (MulAut.congr e a).toMonoidHom = unipotent := by
    rw [←he,←map_aut_congr,hS]
  have ho : Odd (orderOf (MulAut.congr e a)) :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective _).symm ▸ ha
  have hh := odd_local_fixed_of_two _ _ (symplectic_standard_locals hF hn)
    (MulAut.congr e a) ho hα (R.map e.toMonoidHom) hl
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_aut_congr]
  exact hh
end Symplectic

/-- Transfer intrinsic odd-automorphism control through the original
two-core quotient to every conjugate of the source seed. -/
theorem cartan_normalizes_of_odd_local_model
    {E : Type*} [Group E] [Finite E]
    (hcontrol : SolvableSylowControl 2 E)
    (hfixed : ∀ (S : Sylow 2 E) (a : MulAut E), Odd (orderOf a) →
      (S : Subgroup E).map a.toMonoidHom = S →
      ∀ R : Subgroup E, R ∈ localCComponents S → R.map a.toMonoidHom = R)
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hCn : C.Normal)
    (hKC : K ≤ C.map Y.subtype) (e : (C ⧸ pCore 2 C) ≃* E) :
    A ⊓ Y ≤ normalizer (residual H : Set G) := by
  let := hCn
  let q := QuotientGroup.mk' (pCore 2 Y)
  let S := T.subtype (hH.1.1.2.trans hY.2)
  let Q := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  let Cq := C.map q
  let Aq := (A.subgroupOf Y).map q
  let Kq := (K.subgroupOf Y).map q
  let : Cq.Normal := Subgroup.Normal.map hCn q (QuotientGroup.mk'_surjective _)
  let eC : Cq ≃* E := (cComponentTwoCoreQuotientEquiv hC).symm.trans e
  have hKY := hKH.trans hY.2
  have hTY := hH.1.1.2.trans hY.2
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hl : K.subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTY hKY).mp ⟨hKY,hK⟩
  have hlq : Kq ∈ localCComponents (Q : Subgroup (Y ⧸ pCore 2 Y)) := by
    let := pCore_isNilpotent (p := 2) (G := Y)
    exact Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hl
  have hKq : Kq ≤ Cq := by
    apply map_mono
    change K.comap Y.subtype ≤ C
    have hh := comap_mono (f := Y.subtype) hKC
    simpa only [comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have ho : Odd (Nat.card Aq) := by
    have hoA : Odd (Nat.card A) := by
      rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
      exact OddHall.odd_hall_odd c.left_hall
    have ho' : Odd (Nat.card (A.subgroupOf Y)) := by
      rw [← inf_subgroupOf_right A Y, Nat.card_congr (subgroupOfEquivOfLe (show A ⊓ Y ≤ Y from inf_le_right)).toEquiv]
      exact hoA.of_dvd_nat (card_dvd_of_le (show A ⊓ Y ≤ A from inf_le_left))
    exact ho'.of_dvd_nat (card_map_dvd _ q)
  have hs : Group.IsSolvable (Aq ⊔ (Q : Subgroup (Y ⧸ pCore 2 Y)) : Subgroup _) :=
    h.cartan_sylow_action_isSolvable c hTY q
  have hn : Aq ≤ normalizer (componentOrbit Kq (Q : Subgroup _) : Set _) := by
    apply (le_iInf fun (t : (Q : Subgroup (Y ⧸ pCore 2 Y))) => ?_).trans
      (iInf_normalizer_le_normalizer_iSup _)
    have ht : ((Q : Subgroup (Y ⧸ pCore 2 Y))).map (MulAut.conj (t : Y ⧸ pCore 2 Y)).toMonoidHom = Q :=
      by
        apply mem_normalizer_iff_map_conj_eq.mp
        exact (Q : Subgroup (Y ⧸ pCore 2 Y)).le_normalizer t.property
    have hlocal := local_map_automorphism hlq (MulAut.conj (t : Y ⧸ pCore 2 Y)) ht
    have hle : Kq.map (MulAut.conj (t : Y ⧸ pCore 2 Y)).toMonoidHom ≤ Cq := by
      rintro _ ⟨k,hk,rfl⟩
      exact (inferInstance : Cq.Normal).conj_mem k (hKq hk) t
    exact odd_actor_normalizes_local hcontrol hfixed Q Cq Aq eC ho hs hlocal hle
  have heY : componentOrbit (K.subgroupOf Y) ((T : Subgroup G).subgroupOf Y) =
      (residual H).subgroupOf Y := by
    apply map_injective Y.subtype_injective
    rw [map_componentOrbit,map_subgroupOf_eq_of_le hKY,map_subgroupOf_eq_of_le hTY,
      map_subgroupOf_eq_of_le hRY,horbit]
  have heq : componentOrbit Kq (Q : Subgroup _) =
      ((residual H).subgroupOf Y).map q := by
    rw [←heY,map_componentOrbit]
    rfl
  rw [heq] at hn
  exact (residual_escape_twoCore_iff h.qtke h.sylow_normalizes hH hgen hY.2).mp hn

/-- The full Cartan intersection normalizes the residual in every normal
PSL₃(2ᵐ) containing row, without an escaping-cubic or degree-two premise. -/
theorem cartan_normalizes_of_linear_three_container
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n m : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hCn : C.Normal)
    (hKC : K ≤ C.map Y.subtype) (hm : 1 < m)
    (he : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m)) :
    A ⊓ Y ≤ normalizer (residual H : Set G) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact cartan_normalizes_of_odd_local_model
    (Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le F
      (by omega) hF) (linear_odd_local_fixed hF hm)
    h hH hgen c hKH hK horbit hY C hC hCn hKC e

/-- The full Cartan intersection normalizes the residual in a normal
Sp₄(2ᵐ) containing row, retaining the original seed and full Sylow orbit. -/
theorem cartan_normalizes_of_symplectic_four_container
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n m : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hCn : C.Normal)
    (hKC : K ≤ C.map Y.subtype) (hm : 1 < m)
    (he : ClassicalGroup.IsPSp (C ⧸ pCore 2 C) 2 (2 ^ m)) :
    A ⊓ Y ≤ normalizer (residual H : Set G) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2^2)
      (Nat.pow_le_pow_right (by decide) (by omega))
  open Theory.SpecificGroups.SymplecticFour in
  exact cartan_normalizes_of_odd_local_model
    (solvable_overgroups_of_orthogonal_root_orbits hF (by omega)
      (fun D hs hu => solvable_unipotent_point_orbit_orthogonal hlarge D hs hu))
    (symplectic_odd_local_fixed hF hm)
    h hH hgen c hKH hK horbit hY C hC hCn hKC (e.trans EvenProjective.equiv.symm)

private theorem special_linear_odd_local_fixed
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 SL(3,F)) (a : MulAut SL(3,F))
    (ha : Odd (orderOf a)) (hS : (S : Subgroup SL(3,F)).map a.toMonoidHom = S)
    (R : Subgroup SL(3,F)) (hr : R ∈ localCComponents S) : R.map a.toMonoidHom = R := by
  let q := Matrix.PSL3.projection F
  let b := quotientAut (center SL(3,F)) a
  have hq := Matrix.PSL3.projection_surjective F
  have hk : q.ker ≤ center SL(3,F) := by rw [Matrix.PSL3.projection_ker]
  let : Group.IsSolvable (center SL(3,F)) := Group.isSolvable_of_comm fun x y =>
    Subtype.ext (mem_center_iff.mp y.property (x : SL(3,F)))
  let : Group.IsSolvable q.ker := Group.isSolvable_of_isSolvable_injective (inclusion_injective hk)
  have he : b.toMonoidHom.comp q = q.comp a.toMonoidHom := by
    ext x
    exact quotientAut_apply_mk (center SL(3,F)) a x
  have hs : ((S : Subgroup SL(3,F)).map q).map b.toMonoidHom = (S : Subgroup SL(3,F)).map q := by
    rw [map_map,he,←map_map,hS]
  have hb : Odd (orderOf b) := ha.of_dvd_nat (orderOf_map_dvd (quotientAut (center SL(3,F))) a)
  have hl := Chapter1.Section02.localCComponents_map_of_solvable_ker hr q
  have hm := linear_odd_local_fixed hF hn (S.mapSurjective hq) b hb hs (R.map q) hl
  have heR : (R.map a.toMonoidHom).map q = R.map q := by
    rw [map_map,←he,←map_map]
    exact hm
  let := local_perfect hr
  let : Group.IsPerfect (R.map a.toMonoidHom) := Group.IsPerfect.map _
  exact le_antisymm (le_of_map_le_of_perfect q hk _ _ heR.le)
    (le_of_map_le_of_perfect q hk _ _ heR.ge)

private theorem special_linear_solvable_sylow_control
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) : SolvableSylowControl 2 SL(3,F) := by
  intro S A hsol hSA
  let q := Matrix.PSL3.projection F
  have hq := Matrix.PSL3.projection_surjective F
  let := hsol
  have hb := Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le
    F (by omega) hF (S.mapSurjective hq) (A.map q)
    (Group.isSolvable_of_surjective (q.subgroupMap_surjective A)) (map_mono hSA)
  have hk : q.ker ≤ center SL(3,F) := by rw [Matrix.PSL3.projection_ker]
  rw [← S.normalizer_comap_of_central_kernel q hq hk]
  exact map_le_iff_le_comap.mp hb

/-- The same Cartan normalization holds for the genuine special-linear
central cover. Perfectness lifts invariance through its central projection. -/
theorem cartan_normalizes_of_special_linear_three_container
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n m : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hCn : C.Normal)
    (hKC : K ≤ C.map Y.subtype) (hm : 1 < m)
    (he : Chapter1.Section02.LocalModels.IsSL (C ⧸ pCore 2 C) 3 (2 ^ m)) :
    A ⊓ Y ≤ normalizer (residual H : Set G) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact cartan_normalizes_of_odd_local_model (special_linear_solvable_sylow_control hF hm)
    (special_linear_odd_local_fixed hF hm) h hH hgen c hKH hK horbit hY C hC hCn hKC e

/-- A containing quotient with two-part at least sixteen is normal in the
original local overgroup under Cartan escape. -/
theorem container_normal_of_sixteen_dvd
    {T : Sylow 2 G} {K H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hdiv : 16 ∣ Nat.card (C ⧸ pCore 2 C)) : C.Normal := by
  by_contra hn
  obtain ⟨_,hj | ⟨p,hp,hm,_⟩⟩ := nonnormal_container_models hG hKH hTH hK horbit
    hY hescape C hC hKC hn
  · rw [Nat.card_congr hj.some.toEquiv,Janko1.card_model] at hdiv
    norm_num at hdiv
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have h8 : 8 ∣ Nat.card PSL(2,F) := by
      rw [←Nat.card_congr e.toEquiv]
      exact (by decide : 8 ∣ 16).trans hdiv
    have hmod := Theory.PSL2.mod_eight_of_eight_dvd_psl_card (hF ▸ hp.2.1) h8
    rw [hF] at hmod
    have hsmall := hp.2.2.2
    omega

/-- Escape excludes all three classical rank-two rows. Relative
normality is derived from the original nonnormal-component catalogue; no
cubic, degree-two, or invariant-module hypothesis is added. -/
theorem not_classical_rankTwo_container
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n m : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : 1 < m) :
    ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
      Chapter1.Section02.LocalModels.IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
      ClassicalGroup.IsPSp (C ⧸ pCore 2 C) 2 (2 ^ m)) := by
  rintro (he | he | he)
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    have hd : 16 ∣ Nat.card (C ⧸ pCore 2 C) := by
      rw [Nat.card_congr e.toEquiv]
      apply dvd_trans _ (card_subgroup_dvd_card (Matrix.PSL3.LinearThree.unipotent F))
      rw [Matrix.PSL3.LinearThree.card_unipotent F,hF,←pow_mul]
      exact pow_dvd_pow 2 (by omega : 4 ≤ m * 3)
    have hn := container_normal_of_sixteen_dvd h.qtke hKH hH.1.1.2 hK horbit hY hescape C hC hKC hd
    exact hescape (cartan_normalizes_of_linear_three_container h hH hgen c hKH hK horbit hY
      C hC hn hKC hm ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩)
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    have hd : 16 ∣ Nat.card (C ⧸ pCore 2 C) := by
      rw [Nat.card_congr e.toEquiv]
      apply dvd_trans _ (card_subgroup_dvd_card (Matrix.PSL3.LinearThree.unipotentSL F))
      rw [Matrix.PSL3.LinearThree.card_unipotentSL F,hF,←pow_mul]
      exact pow_dvd_pow 2 (by omega : 4 ≤ m * 3)
    have hn := container_normal_of_sixteen_dvd h.qtke hKH hH.1.1.2 hK horbit hY hescape C hC hKC hd
    exact hescape (cartan_normalizes_of_special_linear_three_container h hH hgen c hKH hK horbit hY
      C hC hn hKC hm ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩)
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let a := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
    have hd : 16 ∣ Nat.card (C ⧸ pCore 2 C) := by
      rw [Nat.card_congr a.toEquiv]
      apply dvd_trans _ (card_subgroup_dvd_card (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)))
      rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,hF,←pow_mul]
      exact pow_dvd_pow 2 (by omega : 4 ≤ m * 4)
    have hn := container_normal_of_sixteen_dvd h.qtke hKH hH.1.1.2 hK horbit hY hescape C hC hKC hd
    exact hescape (cartan_normalizes_of_symplectic_four_container h hH hgen c hKH hK horbit hY
      C hC hn hKC hm ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The original escape selects its genuine seed and containing component
with the projective/special linear-three and symplectic-four rows removed. The whole
normal Sylow orbit and its strict enlargement of the residual are retained. -/
theorem localCartan_escape_seed_parabolic_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        ∀ m : ℕ, 1 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          Chapter1.Section02.LocalModels.IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          ClassicalGroup.IsPSp (C ⧸ pCore 2 C) 2 (2 ^ m)) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,⟨hC,hKC,hlt,hn⟩,_⟩ :=
    LocalSieve.exists_escape_seed_embedding h.qtke h.sylow_normalizes hH hgen hY hescape
  exact ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,
    fun _ hm => LocalSieve.not_classical_rankTwo_container h hH hgen c hKH hKL hR
      hY hescape C hC hKC hm⟩
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

