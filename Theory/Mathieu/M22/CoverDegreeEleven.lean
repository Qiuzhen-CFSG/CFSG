module
public import Theory.Mathieu.M22.UniversalMultiplier.TwoRankSource.ElementaryKernel
public import Theory.Mathieu.M22.UniversalMultiplier.PrimaryBounds
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PerfectCentralCoverLocalSplitting
public import Theory.SpecificGroups.OddFourRank
public import Theory.Representation.SpecialLinearRestriction
public import Theory.LinearAlgebra.SpecialLinearDeterminantKernel
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The remaining small-degree bound for full M₂₂ covers

Over F₁₁ a perfect cover in degree at most four embeds in SL₄(11).
The exact order of that group and the native multiplier prime bounds force
its central kernel to divide two. Global involution fusion then makes the
preimage of the native hexad elementary sixteen elementary. This contradicts
the two-rank bound for determinant-one degree four in odd characteristic.
The argument retains the full cover; an odd action kernel is removed only
by taking its actual quotient representation.

Source application: Aschbacher--Smith A.1.28, printed p.26, and 4.2.13,
printed p.612. Native M₂₂ lifting uses I.1.3(4) and I.2.2(6), pp.407, 412.
-/

public noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups IsMulCommutative
namespace Sporadic.Mathieu.M22CentralCover
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private theorem sl4_eleven_card :
    Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 11)) = 4139330225184000 := by
  let det : GL (Fin 4) (ZMod 11) →* (ZMod 11)ˣ := Matrix.GeneralLinearGroup.det
  have hg : Nat.card (GL (Fin 4) (ZMod 11)) = 41393302251840000 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  have hi : det.ker.index = 10 := by
    rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr Matrix.GeneralLinearGroup.det_surjective,
      card_top,Nat.card_units,Nat.card_zmod]
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.determinantKernelEquiv (Fin 4) (ZMod 11)).toEquiv]
  have hh := det.ker.card_mul_index
  rw [hi,hg] at hh
  change Nat.card det.ker = _
  omega

private theorem cover_kernel_dvd_two_of_sl4
    {E : Type*} [Group E] [Finite E] (f : Cover E M22)
    (ρ : E →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 11))
    (hf : Function.Injective ρ) : Nat.card f.toMonoidHom.ker ∣ 2 := by
  have hmul : Nat.card f.toMonoidHom.ker * 443520 = Nat.card E := by
    have hh := f.toMonoidHom.ker.card_mul_index
    rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr f.surjective,card_top,m22_order] at hh
    exact hh
  have hd : Nat.card f.toMonoidHom.ker * 443520 ∣ 4139330225184000 := by
    rw [hmul,←sl4_eleven_card]
    exact card_dvd_of_injective ρ hf
  have hk : Nat.card f.toMonoidHom.ker ∣ 9332905450 := by
    apply Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < 443520)
    exact hd
  have h8 : ¬ 8 ∣ Nat.card f.toMonoidHom.ker := fun hh =>
    (by decide : ¬ 8 ∣ 9332905450) (hh.trans hk)
  have h12 := M22UniversalMultiplier.kernel_card_dvd_twelve_of_not_eight f h8
  exact (show Nat.gcd 12 9332905450 = 2 by decide) ▸ Nat.dvd_gcd h12 hk

private theorem cover_has_elementary_sixteen
    {E : Type*} [Group E] [Finite E] (f : Cover E M22)
    (hk : Nat.card f.toMonoidHom.ker ∣ 2) :
    ∃ A : Subgroup E, IsElementaryAbelian 2 A ∧ 16 ≤ Nat.card A := by
  let : IsMulCommutative f.toMonoidHom.ker :=
    ⟨⟨fun x y => Subtype.ext (mem_center_iff.mp (f.ker_le_center y.property) x)⟩⟩
  let : IsElementaryAbelian 2 f.toMonoidHom.ker := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard x).trans hk)) }
  let B := m22HexadPointwiseKernel m22Hexad123
  let : IsElementaryAbelian 2 B := m22HexadPointwiseKernel_elementaryAbelian m22Hexad123_mem
  let A := B.comap f.toMonoidHom
  have hs (x : A) : x ^ 2 = 1 := by
    apply Subtype.ext
    apply M22UniversalMultiplier.TwoRankSource.square_eq_one_of_elementary_kernel f
    exact congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 B) (f.toMonoidHom.subgroupComap B x))
  let : IsElementaryAbelian 2 A := {
    toIsMulCommutative := ⟨⟨fun x y =>
      (Commute.of_orderOf_dvd_two (fun z => orderOf_dvd_of_pow_eq_one (hs z)) x y).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  refine ⟨A,inferInstance,?_⟩
  have hd := Nat.card_le_card_of_surjective (f.toMonoidHom.subgroupComap B)
    (f.toMonoidHom.subgroupComap_surjective_of_surjective B f.surjective)
  rwa [m22HexadPointwiseKernel_card m22Hexad123_mem] at hd

/-- A full perfect M₂₂ cover has no faithful degree at most four representation over F₁₁. -/
theorem faithful_degree_ge_five_eleven
    {E V : Type*} [Group E] [Finite E]
    [AddCommGroup V] [Module (ZMod 11) V] [FiniteDimensional (ZMod 11) V]
    (f : Cover E M22) (ρ : Representation (ZMod 11) E V)
    (hf : Function.Injective ρ) : 5 ≤ Module.finrank (ZMod 11) V := by
  classical
  by_contra! hd
  have hd4 : Module.finrank (ZMod 11) V ≤ 4 := by omega
  let W := Fin (4 - Module.finrank (ZMod 11) V) → ZMod 11
  let τ : Representation (ZMod 11) E (V × W) := ρ.prod (1 : Representation (ZMod 11) E W)
  have hτ : Function.Injective τ := by
    intro a b he
    apply hf
    ext v
    exact congrArg (fun u : Module.End (ZMod 11) (V × W) => (u (v,0)).1) he
  have hdim : Module.finrank (ZMod 11) (V × W) = 4 := by
    rw [Module.finrank_prod]
    simp only [W,Module.finrank_pi,Fintype.card_fin]
    omega
  let := f.isPerfect
  obtain ⟨a,_,ha,_⟩ := Representation.exists_specialLinear_restriction τ hτ
    (Representation.det_eq_one_of_perfect τ) hdim
  obtain ⟨A,hA,h16⟩ := cover_has_elementary_sixteen f (cover_kernel_dvd_two_of_sl4 f a ha)
  let := hA
  have h8 := Theory.SpecificGroups.OddFourRank.elementary_card_le_eight
    ((Matrix.SpecialLinearGroup.toGL.comp a).comp A.subtype)
    (Matrix.SpecialLinearGroup.toGL_injective.comp (ha.comp A.subtype_injective))
    (by decide : (2 : ZMod 11) ≠ 0)
    (fun x => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) x)
    (fun x => Matrix.SpecialLinearGroup.coeToGL_det (a x))
  omega

/-- An odd kernel suffices for the degree-five bound in characteristic eleven. -/
theorem degree_ge_five_eleven_of_odd_kernel
    {E V : Type*} [Group E] [Finite E] [IsQuasisimple E]
    [AddCommGroup V] [Module (ZMod 11) V] [FiniteDimensional (ZMod 11) V]
    (e : (E ⧸ center E) ≃* M22)
    (ρ : Representation (ZMod 11) E V) (hkodd : Odd (Nat.card ρ.asGroupHom.ker)) : 5 ≤ Module.finrank (ZMod 11) V := by
  let f : PerfectCentralCovering.Cover E M22 := {
    toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := inferInstance
    ker_le_center := by rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk'] }
  have hk : ρ.asGroupHom.ker ≤ center E := by
    rcases IsQuasisimple.normal_le_center_or_eq_top ρ.asGroupHom.ker with h | h
    · exact h
    have hodd : Odd (Nat.card E) := by simpa only [h,card_top] using hkodd
    have heven : 2 ∣ Nat.card E := (show 2 ∣ Nat.card M22 by rw [m22_order]; decide).trans
      (card_dvd_of_surjective f.toMonoidHom f.surjective)
    exact (hodd.not_two_dvd_nat heven).elim
  have hker : ρ.asGroupHom.ker ≤ f.toMonoidHom.ker := by
    change ρ.asGroupHom.ker ≤ (e.toMonoidHom.comp (QuotientGroup.mk' (center E))).ker
    rwa [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let g := f.quotientKernelSubgroup ρ.asGroupHom.ker hker
  let q := QuotientGroup.quotientKerEquivRange ρ.asGroupHom
  let σ : Representation (ZMod 11) (E ⧸ ρ.asGroupHom.ker) V :=
    (Units.coeHom (Module.End (ZMod 11) V)).comp (ρ.asGroupHom.range.subtype.comp q.toMonoidHom)
  have hσ : Function.Injective σ :=
    Units.val_injective.comp (ρ.asGroupHom.range.subtype_injective.comp q.injective)
  exact faithful_degree_ge_five_eleven g σ hσ

end Sporadic.Mathieu.M22CentralCover
