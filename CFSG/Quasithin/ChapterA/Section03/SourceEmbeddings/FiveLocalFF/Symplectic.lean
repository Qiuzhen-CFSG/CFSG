module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.CComponents
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement.OvergroupGeometry
public import Theory.SpecificGroups.SymplecticFour.SimpleQuotients
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SL2.SolvableSylowOvergroups
public import CFSG.Quasithin.ChapterA.Section03.Basic
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import GorensteinWalter.PSL2Cardinality

/-!
# Actual local A₅ sections in the symplectic four-space

A proper local C-component at a full Sylow two-subgroup is conjugate to
one of the literal point or plane determinant kernels. Proper Sylow
geometry places the join in a parabolic; perfectness and the two-power
order of Sylow elements put it in the determinant kernel. Its SL₂ quotient
then forces the nonsolvable Sylow overgroup to be the whole kernel.
The unique C-component of the natural extension identifies the original
subgroup. An A₅ quotient by its two-core forces the coefficient field to
have four elements. The smaller two-core is retained throughout.

Source: Aschbacher–Smith A.3.12 and the constrained FF-action argument in
10.2.9, printed pp.47–48 and 751–752 (1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
noncomputable section
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem local_perfect {G : Type*} [Group G] (S : Subgroup G)
    {B : Subgroup G} (hB : B ∈ localCComponents S) : Group.IsPerfect B := by
  let := hB.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective

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
  let := local_perfect (S : Subgroup (Sp F)) hB
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

theorem symplectic_local_placement {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Sp F)) (B : Subgroup (Sp F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤) :
    ∃ g : Sp F, B.map (MulAut.conj g).toMonoidHom = pointLocal ∨
      B.map (MulAut.conj g).toMonoidHom = planeLocal := by
  have hlarge : 3 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 3 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) (by omega))
  let : IsSimpleGroup (Sp F) := (MulEquiv.isSimpleGroup_congr EvenProjective.equiv).mpr
    (SimpleQuotients.isSimpleGroup hlarge)
  have hjoin : B ⊔ (S : Subgroup (Sp F)) ≠ ⊤ := by
    intro ht
    have hc : B.IsCComponent := by
      have hm := hB
      change (B.subgroupOf (B ⊔ (S : Subgroup (Sp F)))).IsCComponent at hm
      rw [ht] at hm
      simpa only [map_subgroupOf_eq_of_le le_top] using hm.map_subtype (.top)
    exact (hc.subnormal.eq_bot_or_top_of_isSimpleGroup inferInstance).elim hc.ne_bot hproper
  obtain ⟨g,hg⟩ := ThreeResidualPlacement.proper_sylow_overgroup_parabolic_cover
    (by omega) S (B ⊔ (S : Subgroup (Sp F))) le_sup_right hjoin
  let a := MulAut.conj g
  let S' := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  have hl : B.map a.toMonoidHom ∈ localCComponents (S' : Subgroup (Sp F)) := by
    exact Chapter1.Section02.localCComponents_map_of_solvable_ker hB a.toMonoidHom
  refine ⟨g, ?_⟩
  rw [Subgroup.map_sup] at hg
  rcases hg with hp | hp
  · left
    exact local_eq_determinantKernel (point F) pointQuotient pointQuotient_surjective
      (IsElementaryAbelian.isPGroup 2 (pointRadical (F := F)))
      (fun C hC => (pointNaturalExtension hF hn).cComponent_eq_top (by omega) hC)
      S' (B.map a.toMonoidHom) hl hp
  · right
    exact local_eq_determinantKernel (plane F) Plane.quotientMap Plane.quotientMap_surjective
      (IsElementaryAbelian.isPGroup 2 (Plane.radical (F := F)))
      (fun C hC => (planeNaturalExtension hF hn).cComponent_eq_top (by omega) hC)
      S' (B.map a.toMonoidHom) hl hp

omit [CharP F 2] in
private theorem field_four_of_local_five {A : Type*} [Group A] [Finite A]
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5))
    (a : (A ⧸ pCore 2 A) ≃* Matrix.SpecialLinearGroup (Fin 2) F) : Nat.card F = 4 := by
  have hc : Nat.card F * (Nat.card F ^ 2 - 1) = 60 := by
    rw [← GorensteinWalter.sl2_card_formula,
      Nat.card_congr (a.symm.trans e).toEquiv, Nat.card_eq_fintype_card]
    decide
  have hpos : 0 < Nat.card F := Nat.card_pos
  have hl : Nat.card F ≤ 4 := by
    by_contra! hb
    have hsq : 24 ≤ Nat.card F ^ 2 - 1 := by
      have hh : 25 ≤ Nat.card F ^ 2 := by nlinarith
      omega
    have hh := Nat.mul_le_mul (show 5 ≤ Nat.card F by omega) hsq
    omega
  interval_cases h : Nat.card F <;> simp_all

theorem symplectic_five_section_placement {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Sp F)) (B : Subgroup (Sp F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    Nat.card F = 4 ∧ ∃ g : Sp F,
      B.map (MulAut.conj g).toMonoidHom = pointLocal ∨
      B.map (MulAut.conj g).toMonoidHom = planeLocal := by
  obtain ⟨g,hg⟩ := symplectic_local_placement hF hn S B hB hproper
  refine ⟨?_,g,hg⟩
  let a := (MulAut.conj g).subgroupMap B
  have hk : IsPGroup 2 a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    exact IsPGroup.of_subsingleton 2 _
  let aq := a.toMonoidHom.quotientPCoreEquivOfSurjective a.surjective hk
  rcases hg with hp | hp
  · have ep : ((B.map (MulAut.conj g).toMonoidHom) ⧸
        pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F := by
      rw [hp]
      exact pointLocalCoreQuotientEquiv hF hn
    exact field_four_of_local_five e (aq.trans ep)
  · have ep : ((B.map (MulAut.conj g).toMonoidHom) ⧸
        pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F := by
      rw [hp]
      exact planeLocalCoreQuotientEquiv hF hn
    exact field_four_of_local_five e (aq.trans ep)
end
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
