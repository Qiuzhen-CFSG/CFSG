module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.NaturalDual

/-!
# Sylow-fixed generators determine the natural-dual centralizer

A generating subspace of the natural-plus-dual module has nonzero projection
onto both summands. If a Sylow subgroup fixes that subspace, its projections
are the two one-dimensional Sylow-fixed lines. Any actor fixing the seed
therefore fixes both lines, even when the seed is only their diagonal.
This proves the centralizer alignment without the false stronger assertion
that the seed contains the entire Sylow-fixed plane.

Source: Aschbacher--Smith, 15.2.23(b), printed p.1117; B.5.1(6).
-/

set_option backward.isDefEq.respectTransparency false

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open BinaryNaturalDual (CoordinateSpace naturalDualRepresentation naturalDualRepresentation_apply)
open BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open ChapterB.QuasisimpleSource

private theorem binary_span_nonzero {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {x v : V} (hv : v ∈ Submodule.span (ZMod 2) {x}) (hne : v ≠ 0) : v = x := by
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
  have ha : a ≠ 0 := by intro h; exact hne (by rw [h,zero_smul])
  have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha
  rw [ha1,one_smul]

/-- Pointwise centralization of a Sylow-fixed generating seed is equivalent
to centralizing the complete fixed plane in the actual natural-dual model. -/
theorem naturalDual_seedCentralizer {n : ℕ} (hn : 2 ≤ n)
    (P : Sylow 2 (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))
    (Z : Submodule (ZMod 2) (CoordinateSpace n))
    (hZ : Z ≤ fixedSpace (NaturalDualCentralizer.slAction n) P)
    (hgen : (⨆ g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
      Z.map (NaturalDualCentralizer.slAction n g)) = ⊤) :
    subspaceKernel (NaturalDualCentralizer.slAction n) Z ⊤ =
      subspaceKernel (NaturalDualCentralizer.slAction n) (fixedSpace (NaturalDualCentralizer.slAction n) P) ⊤ := by
  obtain ⟨x,f,hx,hf,_,hfix⟩ := NaturalDualCentralizer.exists_fixed_pair hn P
  have hfirst : ∃ z ∈ Z, z.1 ≠ 0 := by
    by_contra! hzero
    let K : Submodule (ZMod 2) (CoordinateSpace n) :=
      (LinearMap.fst (ZMod 2) (Space n) (Module.Dual (ZMod 2) (Space n))).ker
    have hle : (⨆ g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
        Z.map (NaturalDualCentralizer.slAction n g)) ≤ K := by
      apply iSup_le
      rintro g _ ⟨z,hz,rfl⟩
      change (NaturalDualCentralizer.slAction n g z).1 = 0
      rw [NaturalDualCentralizer.action_apply, naturalDualRepresentation_apply]
      simp only [hzero z hz, map_zero]
    rw [hgen] at hle
    exact hx (hle (show (x,0) ∈ (⊤ : Submodule (ZMod 2) (CoordinateSpace n)) from trivial))
  have hsecond : ∃ z ∈ Z, z.2 ≠ 0 := by
    by_contra! hzero
    let K : Submodule (ZMod 2) (CoordinateSpace n) :=
      (LinearMap.snd (ZMod 2) (Space n) (Module.Dual (ZMod 2) (Space n))).ker
    have hle : (⨆ g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
        Z.map (NaturalDualCentralizer.slAction n g)) ≤ K := by
      apply iSup_le
      rintro g _ ⟨z,hz,rfl⟩
      change (NaturalDualCentralizer.slAction n g z).2 = 0
      rw [NaturalDualCentralizer.action_apply, naturalDualRepresentation_apply]
      simp only [hzero z hz, map_zero]
    rw [hgen] at hle
    exact hf (hle (show (0,f) ∈ (⊤ : Submodule (ZMod 2) (CoordinateSpace n)) from trivial))
  apply le_antisymm
  · intro g hg
    obtain ⟨v,hv,hv0⟩ := hfirst
    obtain ⟨w,hw,hw0⟩ := hsecond
    have hvfix := hZ hv
    have hwfix := hZ hw
    rw [hfix] at hvfix hwfix
    have hvx : v.1 = x := binary_span_nonzero hvfix.1 hv0
    have hwf : w.2 = f := binary_span_nonzero hwfix.2 hw0
    have hgx := congrArg Prod.fst (hg.2 v hv)
    have hgf := congrArg Prod.snd (hg.2 w hw)
    rw [NaturalDualCentralizer.action_apply, naturalDualRepresentation_apply] at hgx hgf
    rw [hvx] at hgx
    rw [hwf] at hgf
    change slEquivLinear n g x = x at hgx
    change (slEquivLinear n g).symm.dualMap f = f at hgf
    refine ⟨mem_top _, ?_⟩
    intro u hu
    rw [hfix] at hu
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hu.1
    obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp hu.2
    rw [NaturalDualCentralizer.action_apply, naturalDualRepresentation_apply]
    apply Prod.ext
    · change slEquivLinear n g u.1 = u.1
      rw [← ha, map_smul, hgx]
    · change (slEquivLinear n g).symm.dualMap u.2 = u.2
      rw [← hb, map_smul, hgf]
  · intro g hg
    exact ⟨hg.1, fun z hz => hg.2 z (hZ hz)⟩

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open ChapterB.QuasisimpleSource

/-- Transport the generating-seed centralizer calculation through the one
specified action equivalence, retaining the original Sylow subgroup. -/
theorem naturalDual_seedCentralizer_transport
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} {n : ℕ} (hn : 2 ≤ n)
    (e : ActionEquiv ρ (NaturalDualCentralizer.slAction n)) (P : Sylow 2 D)
    (Z : Submodule (ZMod 2) W) (hZ : Z ≤ fixedSpace ρ P)
    (hgen : (⨆ g : D, Z.map (ρ g)) = ⊤) :
    subspaceKernel ρ Z ⊤ = subspaceKernel ρ (fixedSpace ρ P) ⊤ := by
  let S := P.mapSurjective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.surjective
  let Z' := Z.map e.linearEquiv.toLinearMap
  have hz : Z' ≤ fixedSpace (NaturalDualCentralizer.slAction n) S := by
    change Z' ≤ fixedSpace (NaturalDualCentralizer.slAction n) ((P : Subgroup D).map e.groupEquiv.toMonoidHom)
    rw [← fixedSpace_map_equivariant ρ (NaturalDualCentralizer.slAction n)
      e.groupEquiv.toMonoidHom e.linearEquiv e.intertwines P]
    exact Submodule.map_mono hZ
  have hgen' : (⨆ g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
      Z'.map (NaturalDualCentralizer.slAction n g)) = ⊤ := by
    apply top_unique
    intro w _
    obtain ⟨v,rfl⟩ := e.linearEquiv.surjective w
    have hv : v ∈ ⨆ g : D, Z.map (ρ g) := hgen ▸ Submodule.mem_top
    refine Submodule.iSup_induction (fun g : D => Z.map (ρ g))
      (motive := fun v => e.linearEquiv v ∈ ⨆ g, Z'.map (NaturalDualCentralizer.slAction n g)) hv ?_ ?_ ?_
    · rintro g _ ⟨z,hz,rfl⟩
      exact (le_iSup (fun g => Z'.map (NaturalDualCentralizer.slAction n g)) (e.groupEquiv g))
        ⟨e.linearEquiv z, ⟨z,hz,rfl⟩, (e.intertwines g z).symm⟩
    · simp
    · intro x y hx hy
      simpa only [map_add] using
        (⨆ g, Z'.map (NaturalDualCentralizer.slAction n g)).add_mem hx hy
  have hmodel := naturalDual_seedCentralizer hn S Z' hz hgen'
  apply le_antisymm
  · intro g hg
    have hg' : e.groupEquiv g ∈ subspaceKernel (NaturalDualCentralizer.slAction n) Z' ⊤ := by
      refine ⟨mem_top _, ?_⟩
      rintro _ ⟨z,hz,rfl⟩
      exact (e.intertwines g z).symm.trans (congrArg e.linearEquiv (hg.2 z hz))
    rw [hmodel] at hg'
    refine ⟨mem_top _, ?_⟩
    intro v hv
    apply e.linearEquiv.injective
    rw [e.intertwines]
    apply hg'.2
    change e.linearEquiv v ∈ fixedSpace (NaturalDualCentralizer.slAction n)
      ((P : Subgroup D).map e.groupEquiv.toMonoidHom)
    rw [← fixedSpace_map_equivariant ρ (NaturalDualCentralizer.slAction n)
      e.groupEquiv.toMonoidHom e.linearEquiv e.intertwines P]
    exact ⟨v,hv,rfl⟩
  · intro g hg
    exact ⟨hg.1, fun z hz => hg.2 z (hZ hz)⟩

/-- A cubic-rank-two subgroup cannot fix a generating Sylow-fixed seed in
natural plus dual. The centralizer alignment is proved, not a premise. -/
theorem naturalDual_not_le_seedCentralizer
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hnat : IsNaturalPlusDual ρ n) (P : Sylow 2 D)
    (Z : Submodule (ZMod 2) W) (hZ : Z ≤ fixedSpace ρ P)
    (hgen : (⨆ g : D, Z.map (ρ g)) = ⊤)
    (A : Subgroup D) (hr : 2 ≤ primeRank 3 A) :
    ¬ A ≤ subspaceKernel ρ Z ⊤ := by
  intro hA
  obtain ⟨e⟩ := hnat
  rw [naturalDual_seedCentralizer_transport (by omega) e P Z hZ hgen] at hA
  have hb := (primeRank_mono 3 hA).trans
    (naturalDual_fixedCentralizer_threeRank hn ⟨e⟩ P)
  omega

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open ChapterB.QuasisimpleSource Section01

/-- Literal natural-dual exclusion from generation by U∩ZS. Sylow fixation
and K-centralization of that seed follow from the ambient source action.
The B.2.14 generation premise is the remaining recognition input. -/
theorem false_of_naturalDual_generated_on_U
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {M Mc V H ZS X : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : PlaneUniquenessPreceding hsource H ZS)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    [IsElementaryAbelian 2 (U X ZS)]
    (σ : Representation (ZMod 2) (X ⧸ pCore 2 X) (Additive (U X ZS)))
    (hσ : ∀ (x : X) (u : Additive (U X ZS)),
      ((σ (QuotientGroup.mk' (pCore 2 X) x) u).toMul : G) =
        (x : G) * (u.toMul : G) * (x : G)⁻¹)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hnat : IsNaturalPlusDual σ n)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype ≤ planeSylow T ZS)
    (hgen :
      let Z := AddSubgroup.toZModSubmodule 2 (ZS.subgroupOf (U X ZS)).toAddSubgroup
      (⨆ g : X ⧸ pCore 2 X, Z.map (σ g)) = ⊤) : False := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let P := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let Z := AddSubgroup.toZModSubmodule 2 (ZS.subgroupOf (U X ZS)).toAddSubgroup
  have hfix (x : X) (hc : (x : G) ∈ centralizer (ZS : Set G))
      (u : Additive (U X ZS)) (hu : u ∈ Z) : σ (q x) u = u := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hσ]
    have hh : (u.toMul : G) * (x : G) = (x : G) * (u.toMul : G) := hc _ hu
    rw [← hh, mul_inv_cancel_right]
  have hZ : Z ≤ fixedSpace σ P := by
    intro u hu p
    obtain ⟨x,hx,he⟩ := p.property
    change σ (p : X ⧸ pCore 2 X) u = u
    rw [← he]
    exact hfix x (hS (mem_map_of_mem X.subtype hx)).2 u hu
  let A := (((pResidual 2 H).map H.subtype).subgroupOf X).map q
  have hr : 2 ≤ primeRank 3 A := by
    rw [Theory.GroupTheory.ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup),
      primeRank_equiv 3 (subgroupOfEquivOfLe hKX)]
    exact K_threeRank_ge_two d hpair
  apply naturalDual_not_le_seedCentralizer hn hnat P Z hZ hgen A hr
  rintro _ ⟨x,hx,rfl⟩
  exact ⟨mem_top _, hfix x (d.residual_centralizes hx)⟩

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
