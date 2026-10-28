module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Alternatives.Orthogonal.Seed
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Alternatives.Orthogonal.Parabolic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Alternatives.CentralCover
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.LocalControl
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Preparation.LocalSetup

/-!
# Excluding the orthogonal quotient in 15.3.24

Assume the actual action on `U_L = [W_L,L]` has an orthogonal quotient
by its component-fixed space. Sylow averaging writes each actual central
seed as `z = u c`, with `c` centralizing `L` and `u` centralizing `S ∩ L`.
The orthogonal plane-parabolic calculation, transported to the quotient's
own alternating-group marking, shows that `Y₊` fixes the projection of `u`.

Each displacement then lies in the component-fixed binary kernel. The
existing central-cover argument kills this displacement homomorphism because
`Y₊` is two-perfect. Hence `Y₊` fixes `u`, and therefore `z`, contradicting
the genuine nontrivial commutator `[Z,Y₊]`.

The inputs are the earlier elementarity, Sylow arrangement, `Y₊ ≤ L`,
`O₂(L) ≤ R ≤ C_G(V)`, the actual PSL₄(2) quotient and its plane-parabolic
marking, and the nontrivial seed action. Elementarity of `U_L` follows from
`Alternatives.commutator_elementary`. Neither FF-input data, module alternatives,
a split orthogonal cover nor a specialized fixation premise is assumed.
`source_exclusion` supplies the adapter from `Preparation.Earlier`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.24,
printed p.1129; B.2.13–14, printed p.78; B.4.2(10) and B.5.1(1)(i),
printed pp.86 and 99. This proves the orthogonal branch exclusion, not the
construction of the remaining B.5.1 alternatives.
-/

public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives.Orthogonal

open Representation.BinaryOffender
open BinaryLinear.OuterCyclic
open RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization

variable {G : Type*} [Group G] [Finite G] (d : LocalData G) (L : Subgroup G)
  [IsElementaryAbelian 2 (d.componentSpan L)]
  [IsElementaryAbelian 2 (spanCommutator d L)]

/-- The actual component commutator representation cannot have the orthogonal
fixed-space quotient. All local and parabolic inputs are explicit. -/
theorem not_orthogonalQuotient
    (hcore : L.pCoreIn 2 ≤ d.R) (hR : d.R ≤ centralizer (d.V : Set G))
    (hS : Chapter1.IsSylowIn 2 (d.S ⊓ L) L) (hYL : d.Yplus ≤ L)
    (model : (L ⧸ pCore 2 L) ≃* Projective 4) (p : PlaneParabolic d L model)
    (hact : ⁅d.Z, d.Yplus⁆ ≠ ⊥) :
    ¬ Nonempty (OrthogonalQuotient (coreRepresentation d L hcore hR) ⊤) := by
  rintro ⟨h⟩
  let ρ := coreRepresentation d L hcore hR
  let π := QuotientGroup.mk' (pCore 2 L)
  let m : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 8) :=
    Subgroup.topEquiv.symm.trans h.model
  let e := model.trans (projectiveEquivLinear (by decide : 0 < 4))
  obtain ⟨S, hSl⟩ := hS
  let Q := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  have hpar (l : L) (hl : (l : G) ∈ d.M) : e (π l) ∈ BinaryLinear.parabolic p.plane := by
    have hm : l ∈ (d.M ⊓ L).subgroupOf L := ⟨hl, l.property⟩
    rw [p.intersection] at hm
    exact hm
  have hQ : ∀ q ∈ (Q : Subgroup (L ⧸ pCore 2 L)), e q ∈ BinaryLinear.parabolic p.plane := by
    rintro q ⟨l, hl, rfl⟩
    have hlSL : (l : G) ∈ d.S ⊓ L := hSl ▸ mem_map_of_mem L.subtype hl
    exact hpar l (d.sylow_le hlSL.1.1)
  have hY : IsPPerfect 2 (d.Yplus.subgroupOf L) :=
    (RankOneConfiguration.EightGeometry.yplus_isPPerfect d).of_surjective
      (subgroupOfEquivOfLe hYL).symm.toMonoidHom (subgroupOfEquivOfLe hYL).symm.surjective
  apply hact
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro z hz y hy
  obtain ⟨u, c, hc, hzc, huS⟩ := seed_decomposition d L ⟨S, hSl⟩ z hz
  have huQ : ∀ q ∈ (Q : Subgroup (L ⧸ pCore 2 L)),
      BinaryPermutation.naturalRepresentation (Fin 8) (m q).val
        (h.projection (Additive.ofMul u)) = h.projection (Additive.ofMul u) := by
    rintro q ⟨l, hl, rfl⟩
    have hlSL : (l : G) ∈ d.S ⊓ L := hSl ▸ mem_map_of_mem L.subtype hl
    have huf : ρ (π l) (Additive.ofMul u) = Additive.ofMul u := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (coreRepresentation_apply d L hcore hR l _).trans
        (mul_inv_eq_iff_eq_mul.mpr (huS l hlSL))
    have he := h.equivariant ⟨π l, mem_top _⟩ (Additive.ofMul u)
    change h.projection (ρ (π l) (Additive.ofMul u)) =
      BinaryPermutation.naturalRepresentation (Fin 8) (m (π l)).val
        (h.projection (Additive.ofMul u)) at he
    exact he.symm.trans (congrArg h.projection huf)
  have hgeom := Parabolic.plane_fixed_of_sylow e m p.plane p.dimension Q hQ
    (h.projection (Additive.ofMul u)) huQ
  have huY : ∀ a : d.Yplus.subgroupOf L, ρ (π a.val) (Additive.ofMul u) = Additive.ofMul u := by
    apply fixed_of_displacement_fixed (ρ.comp π) (d.Yplus.subgroupOf L) hY
    intro a
    have hh : ρ (π a.val) (Additive.ofMul u) - Additive.ofMul u ∈ fixedSpace ρ ⊤ := by
      rw [← h.projection_ker]
      change h.projection (ρ (π a.val) (Additive.ofMul u) - Additive.ofMul u) = 0
      rw [map_sub]
      have he := h.equivariant ⟨π a.val, mem_top _⟩ (Additive.ofMul u)
      change h.projection (ρ (π a.val) (Additive.ofMul u)) =
        BinaryPermutation.naturalRepresentation (Fin 8) (m (π a.val)).val
          (h.projection (Additive.ofMul u)) at he
      rw [he, hgeom (π a.val) (hpar a.val
        (RankOneConfiguration.EightGeometry.yplus_le_M d a.property)), sub_self]
    intro b
    exact hh ⟨π b.val, mem_top _⟩
  have hu := congrArg (fun w : Additive (spanCommutator d L) => (w.toMul : G))
    (huY ⟨⟨y, hYL hy⟩, hy⟩)
  have hu' : y * (u : G) = u * y := mul_inv_eq_iff_eq_mul.mp hu
  have hc' : y * (c : G) = c * y := hc y (hYL hy)
  rw [hzc]
  calc
    y * ((u : G) * c) = (y * u) * c := (mul_assoc _ _ _).symm
    _ = ((u : G) * y) * c := by rw [hu']
    _ = (u : G) * (y * c) := mul_assoc _ _ _
    _ = (u : G) * (c * y) := by rw [hc']
    _ = ((u : G) * c) * y := (mul_assoc _ _ _).symm

/-- The exclusion under the precise earlier component preparation outputs. -/
theorem source_exclusion {I : Subgroup G} (c : ComponentWitness d I)
    (earlier : Preparation.Earlier d c)
    [IsElementaryAbelian 2 (d.componentSpan c.L)]
    [IsElementaryAbelian 2 (spanCommutator d c.L)]
    (model : (c.L ⧸ pCore 2 c.L) ≃* Projective 4) (p : PlaneParabolic d c.L model)
    (hR : d.R ≤ centralizer (d.V : Set G)) (hact : ⁅d.Z, d.Yplus⁆ ≠ ⊥) :
    ¬ Nonempty (OrthogonalQuotient (coreRepresentation d c.L earlier.core_le_R hR) ⊤) :=
  not_orthogonalQuotient d c.L earlier.core_le_R hR earlier.sylow_component
    earlier.yplus_le model p hact

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives.Orthogonal

end
