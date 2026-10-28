module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianOrthogonal
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianHypotheses

/-!
# The seed and actor kernel in the orthogonal branch of 12.9.4

In the surviving six-dimensional action, the original seed image exhausts
the isotropic intersection: both have dimension three. G.10's dimension
identity gives rank two for the literal quotient of the actor by the
conjugate-center image. That image fixes the seed because the original
conjugator normalizes it.

The full centered-transvection action maps onto the annihilator of the
marked line in the dual three-space. This image has order four, equal to
the original relative quotient, so the conjugate-center image is exactly
the actor kernel on the seed. All maps and relative subgroups are the
ones constructed from the original flag. The minimal-parabolic radical
comparison and the final orthogonal contradiction remain to be proved.

Source: Aschbacher--Smith 12.8.11--13 and 12.9.4,
printed pp.854--856,859--860.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- In the surviving six-space, the original seed exhausts E-hat.
This uses its dimension three and the actual nondegenerate commutator form. -/
theorem nonabelian_caseFive_seed_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B₀ : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B₀) :
    n = 4 ∧ hatSpace F (F.E g) = hatSpace F V ∧
      finrank (ZMod 2) (hatSpace F (F.E g)) = 3 := by
  have hn4 := nonabelian_degree_four_of_hat_rank_le_six h hn earlier F hne h5.1.le
  have hle := seed_hat_le_intersection h F g hgP
  have hdim := nonabelian_seed_hat_finrank h F hne
  obtain ⟨hX,B,v,hg10,_⟩ := nonabelian_g10_hypothesis h earlier F hne g hgP hgH
  let := hX
  have hb := B.twice_finrank_le_of_isotropic hg10.nondegenerate _ hg10.isotropic
  have hd := h5.1
  have hl := Submodule.finrank_mono hle
  have he : finrank (ZMod 2) (hatSpace F (F.E g)) = 3 := by omega
  refine ⟨hn4,?_,he⟩
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

/-- The original quotient X-dot / Z(U)^g-dot has rank exactly two in the
orthogonal branch. The center image is nontrivial by the ambient argument. -/
theorem nonabelian_caseFive_actor_quotient
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B₀ : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B₀) :
    ∃ hX : IsElementaryAbelian 2 (F.terminalDot (F.X g)),
    let := hX
    Group.rank ((F.terminalDot (F.X g)) ⧸
      (F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) = 2 ∧
      F.terminalDot (conjugate F.ZU g) ≠ ⊥ := by
  obtain ⟨hX,B,v,hg10,_⟩ := nonabelian_g10_hypothesis h earlier F hne g hgP hgH
  let := hX
  have hd := (nonabelian_caseFive_seed_intersection h hn earlier F hne g hgP hgH B₀ h5).2.2
  have hr := hg10.dimension
  rw [hd,h5.1] at hr
  exact ⟨hX,by omega,(nonabelian_caseFive_center h hn earlier F hne g hgP hgH B₀ h5).2⟩

/-- The actual conjugate center fixes E-hat in the orthogonal row, since
E-hat is the unchanged natural seed and the source conjugator normalizes V. -/
theorem nonabelian_caseFive_center_fixes_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B₀ : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B₀) :
    ∀ a ∈ F.terminalDot (conjugate F.ZU g), ∀ v ∈ hatSpace F (F.E g),
      F.terminalRepresentation a v = v := by
  have he := (nonabelian_caseFive_seed_intersection h hn earlier F hne g hgP hgH B₀ h5).2.1
  have hc := F.conjugate_center_centralizes_seed g
    (F.P_le_seed_normalizer L h.chosen.normalizes hgP)
  rintro _ ⟨a,ha,rfl⟩ v hv
  rw [he] at hv
  obtain ⟨b,hb,hbv⟩ := (show v.toMul ∈ hatImage F V from hv)
  apply Additive.toMul.injective
  rw [F.terminalRepresentation_apply_mk,←hbv,F.terminalHatAction_apply_mk]
  apply congrArg (QuotientGroup.mk' (center F.U))
  apply Subtype.ext
  change (a:G) * (b:G) * (a:G)⁻¹ = b
  have hab : (b:G) * (a:G) = (a:G) * (b:G) := hc ha b hb
  rw [←hab,mul_inv_cancel_right]

private theorem transvection_kernel
    {D U : Type*} [Group D] [Finite D] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (B : LinearMap.BilinForm (ZMod 2) U)
    (v : U) (W : Submodule (ZMod 2) U) (X : Subgroup D)
    [IsElementaryAbelian 2 X] (Z : Subgroup X)
    (h : ChapterG.Section10.Hypothesis ρ B v W X Z)
    (hd : finrank (ZMod 2) W = 3) (hz : Nat.card (X ⧸ Z) = 4)
    (hfix : ∀ x ∈ Z, ∀ w ∈ W, ρ (x:D) w = w) :
    ∀ x : X, x ∈ Z ↔ ∀ w ∈ W, ρ (x:D) w = w := by
  let vW : W := ⟨v,h.point_mem⟩
  let A := (Submodule.span (ZMod 2) {vW}).dualAnnihilator
  obtain ⟨l,hl⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) h.point_ne_zero
  let f (x : X) : Module.Dual (ZMod 2) W :=
    l.comp (((ρ x).comp W.subtype) - W.subtype)
  have feval (x : X) (w : W) : f x w = l (ρ x w - w) := rfl
  have act (x : X) (w : W) : ρ x w = (w:U) + f x w • v := by
    obtain ⟨φ,_,hφ⟩ := h.transvections x
    have he : f x w = φ w := by
      rw [feval,hφ,add_sub_cancel_left,map_smul,hl,smul_eq_mul,mul_one]
    rw [he]
    exact hφ w
  have fpoint (x : X) : f x vW = 0 := by
    rw [feval,h.fixes_point x.property,sub_self,map_zero]
  have fmem (x : X) : f x ∈ A := by
    apply (Submodule.mem_dualAnnihilator _).mpr
    rintro w hw
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul,fpoint,smul_zero]
  let r : X →* Multiplicative A :=
    { toFun := fun x => Multiplicative.ofAdd ⟨f x,fmem x⟩
      map_one' := by
        apply Subtype.ext
        ext w
        change f 1 w = 0
        rw [feval,show ((1:X):D) = 1 from rfl,map_one,Module.End.one_apply,sub_self,map_zero]
      map_mul' := by
        intro x y
        apply Subtype.ext
        ext w
        change f (x*y) w = f x w + f y w
        rw [feval,show ((x*y:X):D) = (x:D)*(y:D) from rfl,map_mul,Module.End.mul_apply,
          act y w,map_add,map_smul,h.fixes_point x.property,act x w]
        have he : ((w:U) + f x w • v + f y w • v) - w = f x w • v + f y w • v := by abel
        rw [he,map_add,map_smul,map_smul,hl]
        simp only [smul_eq_mul,mul_one] }
  have rker (x : X) : x ∈ r.ker ↔ ∀ w ∈ W, ρ (x:D) w = w := by
    change (⟨f x,fmem x⟩ : A) = 0 ↔ _
    rw [Subtype.ext_iff]
    constructor
    · intro he w hw
      rw [act x ⟨w,hw⟩,show f x ⟨w,hw⟩ = 0 from LinearMap.congr_fun he _,zero_smul,add_zero]
    · intro he
      ext w
      rw [feval,he w w.property,sub_self,map_zero]
      rfl
  have ronto : Function.Surjective r := by
    intro φ
    have hφ : φ.toAdd.val vW = 0 :=
      ((Submodule.mem_dualAnnihilator _).mp φ.toAdd.property) vW (Submodule.mem_span_singleton_self _)
    obtain ⟨x,hx⟩ := h.full_transvections φ.toAdd.val hφ
    refine ⟨x,?_⟩
    apply Subtype.ext
    ext w
    change f x w = φ.toAdd.val w
    rw [feval,hx,add_sub_cancel_left,map_smul,hl,smul_eq_mul,mul_one]
  have hdim : finrank (ZMod 2) A = 2 := by
    have hd' := Subspace.finrank_add_finrank_dualAnnihilator_eq (Submodule.span (ZMod 2) {vW})
    have hvW : vW ≠ 0 := fun he => h.point_ne_zero (congrArg Subtype.val he)
    rw [finrank_span_singleton hvW,hd] at hd'
    change 1 + finrank (ZMod 2) A = 3 at hd'
    omega
  have hcard : Nat.card (Multiplicative A) = 4 := by
    rw [Nat.card_congr Multiplicative.toAdd,Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod,hdim]
    rfl
  have hri : r.ker.index = 4 := by
    rw [Subgroup.index_ker (G := X) (G' := Multiplicative A) r, MonoidHom.range_eq_top.mpr ronto, Subgroup.card_top]
    exact hcard
  have hZi : Z.index = 4 := by rwa [Subgroup.index_eq_card]
  have hZker : Z ≤ r.ker := fun x hx => (rker x).mpr (hfix x hx)
  have heq : Z = r.ker := by
    apply eq_of_le_of_card_ge hZker
    have hZ := Z.card_mul_index
    have hr := r.ker.card_mul_index
    rw [hZi] at hZ
    rw [hri] at hr
    omega
  intro x
  rw [heq]
  exact rker x

/-- In the orthogonal row the smaller actor is exactly the kernel on the
original seed. The full centered-transvection action has order four, equal
to the literal relative quotient, so no additional kernel can occur. -/
theorem nonabelian_caseFive_center_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B₀ : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B₀) :
    ∀ x : F.terminalDot (F.X g),
      x ∈ (F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)) ↔
        ∀ v ∈ hatSpace F V, F.terminalRepresentation x v = v := by
  obtain ⟨hX,B,v,hg10,_⟩ := nonabelian_g10_hypothesis h earlier F hne g hgP hgH
  let := hX
  obtain ⟨_,he,hd⟩ := nonabelian_caseFive_seed_intersection h hn earlier F hne g hgP hgH B₀ h5
  have hr := nonabelian_transvection_geometry h earlier F hne g hgP hgH
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hbal⟩ := hr
  rw [hd,h5.1] at hbal
  let Q := (F.terminalDot (F.X g)) ⧸
    (F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.quotient _
  have hdimQ : finrank (ZMod 2) (Additive Q) = 2 := by
    change 3 + finrank (ZMod 2) (Additive Q) = 6 - 1 at hbal
    omega
  have hcard : Nat.card Q = 4 := by
    rw [Nat.card_congr Additive.ofMul,Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod,hdimQ]
    rfl
  have hh := transvection_kernel F.terminalRepresentation B v (hatSpace F (F.E g))
    (F.terminalDot (F.X g))
    ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) hg10 hd hcard
    (fun x hx => nonabelian_caseFive_center_fixes_intersection h hn earlier F hne g hgP hgH B₀ h5 x hx)
  rwa [he] at hh

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
