module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.OddDegree.SeedFixed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.OddDegree.CubicMatrix

/-!
# The scalar cubic obstruction and odd source degree

Transfer the fixed-point-free action of the actual D₃ on V through its
original natural coordinates. The three-dimensional cubic calculation makes
every element of D₃ scalar in that exact SL₃ quotient. Consequently [L,D₃]
lies in V. Coprime action on P then contradicts P not being contained in V.
This proves odd degree with no scalar, fixed-space or parity callback.

Source: Aschbacher--Smith, printed p.774, “Assume n is even”. The preceding
input record is constructed by common-core; the source argument does not
identify the independent fields marking P and V.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Polynomial Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {h : G}
    (d : OrthogonalInput D S m f H X A h)
include d


/-- The original cubic subgroup has scalar image in the supplied SL₃ marking. -/
theorem source_cubic_scalar (C : Subgroup G) (hC : Nat.card C = 3)
    (hCA : C ≤ oddCartanPart A) (x : C) :
    ∃ a : S.field.Carrier,
      ((Coordinates.sl3 m).quotientMap
        (inclusion (hCA.trans (d.oddCartan_le.trans (d.cartan.1.trans inf_le_left))) x)).val =
          a • (1 : Matrix (Fin 3) (Fin 3) S.field.Carrier) := by
  let c := Coordinates.sl3 m
  let hCL : C ≤ L := hCA.trans (d.oddCartan_le.trans (d.cartan.1.trans inf_le_left))
  let g : Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier := c.quotientMap (inclusion hCL x)
  change ∃ a, g.val = a • (1 : Matrix (Fin 3) (Fin 3) S.field.Carrier)
  by_cases hx : x = 1
  · refine ⟨1,?_⟩
    simp [g,hx]
  have hp : x^3 = 1 := by simpa only [hC] using pow_card_eq_one' (x := x)
  apply sl3_cubic_scalar_of_fixed_free g
  · change (c.quotientMap.comp (inclusion hCL) x)^3 = 1
    rw [← map_pow,hp,map_one]
  · intro w hw
    obtain ⟨v,hv⟩ := c.projection_surjective (Multiplicative.ofAdd w)
    have hi : Function.Injective c.projection := by
      apply c.projection.ker_eq_bot_iff.mp
      apply bot_unique
      intro v hv
      apply Subtype.ext
      exact d.seed_fixed.le ⟨v.property,(c.projection_eq_one_iff v).mp hv⟩
    have he := c.projection_component_conjugation (inclusion hCL x) v
    have hfix : V.normalizerMonoidHom (inclusion D.normalizes (inclusion hCL x)) v = v := by
      apply hi
      apply Multiplicative.toAdd.injective
      rw [he,hv]
      exact hw
    have hxv : Commute (x : G) (v : G) := by
      have he' := congrArg Subtype.val hfix
      exact mul_inv_eq_iff_eq_mul.mp he'
    have hvc : (v : G) ∈ centralizer (C : Set G) := by
      intro y hy
      obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp
        (mem_zpowers_of_prime_card hC hx (g' := (⟨y,hy⟩ : C)))
      have hyn : (x : G)^n = y := congrArg Subtype.val hn
      rw [←hyn]
      exact (hxv.zpow_left n).eq
    have hv1 : v = 1 := Subtype.ext ((source_cubic_seed_fixed_eq_bot d C hC hCA).le ⟨v.property,hvc⟩)
    have hp1 : c.projection v = 1 := by rw [hv1,map_one]
    rw [hv] at hp1
    exact hp1

/-- The scalar image centralizes L/V for the literal cubic subgroup. -/
theorem source_cubic_commutator_le_seed (C : Subgroup G) (hC : Nat.card C = 3)
    (hCA : C ≤ oddCartanPart A) : ⁅L,C⁆ ≤ V := by
  let c := Coordinates.sl3 m
  have hCL : C ≤ L := hCA.trans (d.oddCartan_le.trans (d.cartan.1.trans inf_le_left))
  apply commutator_le.mpr
  intro l hl x hx
  let l' : L := ⟨l,hl⟩
  let x' : L := inclusion hCL ⟨x,hx⟩
  have hcomm : Commute (c.quotientMap l') (c.quotientMap x') := by
    obtain ⟨a,ha⟩ := source_cubic_scalar d C hC hCA ⟨x,hx⟩
    apply Subtype.ext
    change (c.quotientMap l').val * (c.quotientMap x').val =
      (c.quotientMap x').val * (c.quotientMap l').val
    rw [ha,Matrix.mul_smul,Matrix.smul_mul,mul_one,one_mul]
  have he : c.quotientMap ⁅l',x'⁆ = 1 := by
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.eq
  have hc : ⁅l',x'⁆ ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply c.groupEquiv.injective
    exact he.trans c.groupEquiv.map_one.symm
  rw [←d.seed_core]
  exact mem_map_of_mem L.subtype hc

/-- The even-degree cubic subgroup contradicts the actual common-core geometry. -/
theorem source_degree_odd : Odd S.field.degree := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  obtain ⟨C,hC,hCA,_⟩ := source_cubic_subgroup d heven
  exact source_cubic_contradiction_of_scalar d C hC hCA
    (source_cubic_commutator_le_seed d C hC hCA)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
