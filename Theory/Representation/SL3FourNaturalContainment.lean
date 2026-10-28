module
public import Theory.Representation.SL3OddNaturalNormalizer.Index
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.GroupTheory.QuasithinBasic
public import Theory.GroupTheory.PResidual.Quotient

/-!
# Rank-two ambient actions containing the natural SL₃(4) layer

A binary operator normalizing the marked natural SL₃ action is semilinear.
Over the field of four elements its coefficient group has order two.
A linear overgroup larger than SL₃ has all three determinants, hence is
GL₃(4); the independent diagonal units then give cubic rank at least three.
Thus an ambient group of cubic rank at most two has its entire linear kernel
in the specified SL₃ layer, which contains the actual two-residual.

This is the single natural-module, field-four case of Aschbacher--Smith
A.3.19, printed p.54, used in13.7.6, printed p.940. The action, subgroup
marking, ambient rank bound, and residual all refer to the supplied group.
-/

@[expose] public section
noncomputable section
open Subgroup Matrix Theory.GroupTheory
namespace Representation.SL3FourNaturalContainment
variable {F : Type*} [Field F] [Finite F]

private def diagonalUnits : (Fin 3 → Fˣ) →* GL (Fin 3) F where
  toFun u := ⟨Matrix.diagonal (fun i => (u i : F)),
    Matrix.diagonal (fun i => ((u i)⁻¹ : F)),
    by simp [Matrix.diagonal_mul_diagonal],
    by simp [Matrix.diagonal_mul_diagonal]⟩
  map_one' := by apply Units.ext; simp
  map_mul' u v := by apply Units.ext; simp [Matrix.diagonal_mul_diagonal]

omit [Finite F] in
private theorem diagonalUnits_injective : Function.Injective (diagonalUnits (F := F)) := by
  intro x y h
  funext i
  apply Units.ext
  have hh := congrArg (fun A : GL (Fin 3) F => A.val i i) h
  change Matrix.diagonal (fun j => (x j : F)) i i =
    Matrix.diagonal (fun j => (y j : F)) i i at hh
  simpa only [Matrix.diagonal_apply_eq] using hh

/-- Three independent diagonal units give cubic rank three in GL₃(4). -/
theorem three_le_generalLinear_rank (hF : Nat.card F = 4) :
    3 ≤ primeRank 3 (GL (Fin 3) F) := by
  have hc : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  apply primeRank_ge_of_elementary_embedding
    (A := Fin 3 → Fˣ) (p := 3) (e := 3) ?_ ?_ diagonalUnits diagonalUnits_injective
  · intro a
    funext i
    change a i ^ 3 = 1
    simpa only [hc] using (pow_card_eq_one' (x := a i))
  · rw [Nat.card_fun, Nat.card_fin, hc]

/-- A cubic-rank-two linear overgroup of SL₃(4) is the determinant kernel itself. -/
theorem linear_overgroup_eq_det_kernel (hF : Nat.card F = 4)
    (D : Subgroup (GL (Fin 3) F))
    (hSL : (GeneralLinearGroup.det : GL (Fin 3) F →* Fˣ).ker ≤ D)
    (hr : primeRank 3 D ≤ 2) : D = GeneralLinearGroup.det.ker := by
  let δ : GL (Fin 3) F →* Fˣ := GeneralLinearGroup.det
  have hc : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have hd : Nat.card (D.map δ) ∣ 3 := by
    simpa only [hc] using (D.map δ).card_subgroup_dvd_card
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · apply le_antisymm _ hSL
    exact (Subgroup.map_eq_bot_iff D).mp (Subgroup.card_eq_one.mp h1)
  · have ht : D.map δ = ⊤ := (D.map δ).eq_top_of_card_eq (h3.trans hc.symm)
    have he : D = ⊤ := by
      have hm := Subgroup.comap_map_eq_self hSL
      rw [ht, comap_top] at hm
      exact hm.symm
    have hb : primeRank 3 (GL (Fin 3) F) ≤ 2 := by
      rw [he, primeRank_equiv 3 Subgroup.topEquiv] at hr
      exact hr
    have hh := three_le_generalLinear_rank hF
    omega

variable {H : Type*} [Group H] [Finite H] [Algebra (ZMod 2) F]
open Representation.SL3OddNaturalNormalizer

/-- A faithful natural marking places the actual ambient two-residual in SL₃(4). -/
theorem pResidual_le_of_natural (hF : Nat.card F = 4)
    (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (ρ : Representation (ZMod 2) H (Fin 3 → F)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Fin 3 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    (hr : primeRank 3 H ≤ 2) : pResidual 2 H ≤ L := by
  let hsemi := normalizer_semilinear L e ρ hnat
  let φ := fieldAction ρ hsemi
  have hL : L ≤ φ.ker := by
    intro g hg
    apply (fieldAction_eq_one_iff ρ hsemi g).mpr
    intro c v
    change ρ (⟨g, hg⟩ : L) (c • v) = c • ρ (⟨g, hg⟩ : L) v
    rw [hnat, hnat, Matrix.mulVec_smul]
  let τ : Representation F φ.ker (Fin 3 → F) := {
    toFun g := {
      toFun := ρ (g : H)
      map_add' := (ρ (g : H)).map_add
      map_smul' := by
        intro c v
        exact (fieldAction_eq_one_iff ρ hsemi g).mp g.property c v }
    map_one' := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun ρ.map_one v
    map_mul' g h := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun (ρ.map_mul g h) v }
  let μ : φ.ker →* GL (Fin 3) F :=
    GeneralLinearGroup.toLin.symm.toMonoidHom.comp τ.asGroupHom
  have hμ (g : φ.ker) (v : Fin 3 → F) : (μ g).val.mulVec v = ρ (g : H) v := by
    change (GeneralLinearGroup.toLin (μ g) : Module.End F (Fin 3 → F)) v = _
    have he : GeneralLinearGroup.toLin (μ g) = τ.asGroupHom g :=
      GeneralLinearGroup.toLin.apply_symm_apply _
    rw [he]
    rfl
  have hμinj : Function.Injective μ := by
    intro a b hab
    apply Subtype.ext
    apply hfaith
    apply LinearMap.ext
    intro v
    rw [← hμ a v, ← hμ b v, hab]
  have hSL : (GeneralLinearGroup.det : GL (Fin 3) F →* Fˣ).ker ≤ μ.range := by
    intro A hA
    let a : SpecialLinearGroup (Fin 3) F := ⟨A.val, congrArg Units.val hA⟩
    refine ⟨⟨e.symm a, hL (e.symm a).property⟩, ?_⟩
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    exact (hμ _ v).trans (by rw [hnat, e.apply_symm_apply]; rfl)
  have hrμ : primeRank 3 μ.range ≤ 2 := by
    rw [← primeRank_equiv 3 (MonoidHom.ofInjective hμinj)]
    exact (primeRank_le_of_injective 3 φ.ker.subtype φ.ker.subtype_injective).trans hr
  have hdet := linear_overgroup_eq_det_kernel hF μ.range hSL hrμ
  have hk : φ.ker ≤ L := by
    intro g hg
    let x : φ.ker := ⟨g, hg⟩
    have hd : GeneralLinearGroup.det (μ x) = 1 := by
      have hx : μ x ∈ μ.range := ⟨x,rfl⟩
      rwa [hdet] at hx
    let a : SpecialLinearGroup (Fin 3) F := ⟨(μ x).val, congrArg Units.val hd⟩
    have he : g = (e.symm a : L) := by
      apply hfaith
      apply LinearMap.ext
      intro v
      rw [hnat, e.apply_symm_apply]
      exact (hμ x v).symm
    rw [he]
    exact (e.symm a).property
  have ha : IsPGroup 2 (F ≃+* F) := IsPGroup.of_card (n := 1)
    (binaryFieldAut_card (m := 2) (by simpa using hF))
  exact (pResidual_le_ker_of_isPGroup 2 φ ha).trans hk

end Representation.SL3FourNaturalContainment
