module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.ChosenInputs
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry

/-!
# Earlier geometry for the even critical-distance argument

The flag is matched to the original point, plane and three-space on the literal
chosen quotient. Its invariance gives T ≤ G₁. The preceding point-parabolic
factorization retains O₂(L), and its Cartan kernel is taken on the actual V₁.
Odd order of the Cartan and two-power order of T show that an element of LT
centralizing V₁ lies in L₁T. No equality with the full point normalizer is used.

The G₁-closure of L₁ centralizes V₁. In the strict branch, containment of K in M
would make L₁ and K comparable relative C-components of M₁, forcing equality.
These conclusions supply the original amalgam's LocalInputs and SourceSetup.

The flag, parabolic factorization, Cartan kernel, and relative components are
explicit preceding source conclusions. Their producers are the marked flag and
Cartan branch of qt-d-1222-natural-local-geometry and the component branch of
qt-d-1222-natural-shadow-reduction. This module does not prove those earlier
conclusions or the quadratic line alternatives.
Source: Aschbacher--Smith, §11.1, 11.4.1--2 and 11.5.8, printed pp.760--784.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

/-- The Sylow fixes the original field line. -/
theorem sylow_le_point_normalizer {c : LocalGeometry.Coordinates D E.input.field}
    (f : LocalGeometry.InvariantFlag c)
    (hp : c.binarySubspace (f.space 0) = E.point) : (T : Subgroup G) ≤ E.G₁ := by
  simpa only [LocalGeometry.InvariantFlag.Vi, LocalGeometry.Coordinates.preimage,
    hp, Geometry.G₁, Geometry.V₁] using f.invariant 0

/-- Centralization survives normal closure under the line normalizer. -/
theorem K_centralizes (hfix : E.L₁ ≤ centralizer (E.V₁ : Set G)) :
    E.K ≤ centralizer (E.V₁ : Set G) :=
  conjugateSpanBy_le hfix (normalizer_le_normalizer_centralizer E.V₁)

/-- Relative component comparability gives the escape needed by F.7. -/
theorem strict_component_escapes
    (hLi : Source.ComponentIn E.M₁ E.L₁)
    (hK : Source.ComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K) : ¬ E.K ≤ E.M := by
  intro hm
  have hKM : E.K ≤ E.M₁ := le_inf hm E.K_le_G₁
  have he := hLi.2.eq_of_le
    (hK.2.subgroupOf_of_le hKM (show E.M₁ ≤ E.G₁ from inf_le_right))
    (comap_mono hlt.le)
  have he' := congrArg (map E.M₁.subtype) he
  rw [map_subgroupOf_eq_of_le hLi.1, map_subgroupOf_eq_of_le hKM] at he'
  exact hlt.ne he'

open scoped Pointwise in
/-- The odd Cartan contributes no extra elements to C_LT(V₁), even when its
full point stabilizer is larger than L₁T. -/
theorem point_centralizer_bound
    (hT : (T : Subgroup G) ≤ E.G₁)
    (hfix : E.L₁ ≤ centralizer (E.V₁ : Set G))
    (hsplit : L ⊓ E.G₁ = (E.L₁ ⊔ L.pCoreIn 2) ⊔ E.X)
    (hodd : Odd (Nat.card E.X))
    (hker : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁ ⊔ L.pCoreIn 2) :
    LT E ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁ ⊔ (T : Subgroup G) := by
  let A := E.L₁ ⊔ L.pCoreIn 2
  have hcore : L.pCoreIn 2 ≤ (LT E).pCoreIn 2 := by
    let : (L.subgroupOf (LT E)).Normal := normal_subgroupOf_of_le_normalizer
      (sup_le L.le_normalizer D.sylow_normalizes_component)
    exact pCoreAmbient_mono_of_isSubnormalIn L (LT E) 2 le_sup_left
      (show (L.subgroupOf (LT E)).Normal from inferInstance).isSubnormal
  have hcoreT : L.pCoreIn 2 ≤ (T : Subgroup G) := hcore.trans (by
    have hh := pCoreIn_le_sylow (LT E)
      (T.subtype (show (T : Subgroup G) ≤ LT E from le_sup_right))
    rw [Sylow.coe_subtype,
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ LT E from le_sup_right)] at hh
    exact hh)
  have hAf : A ≤ centralizer (E.V₁ : Set G) :=
    sup_le hfix ((hcore.trans D.core_centralizes).trans (centralizer_le E.V₁_le))
  have hAT : A ≤ E.L₁ ⊔ (T : Subgroup G) := sup_le le_sup_left (hcoreT.trans le_sup_right)
  have hXN : E.X ≤ E.G₁ := (le_sup_right.trans hsplit.ge).trans inf_le_right
  have hXA₀ : E.X ≤ normalizer (E.L₁ : Set G) :=
    ((le_sup_right.trans hsplit.ge).trans (L ⊓ E.G₁).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have hXQ : E.X ≤ normalizer (L.pCoreIn 2 : Set G) :=
    ((le_sup_right.trans hsplit.ge).trans inf_le_left).trans
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  have hXA : E.X ≤ normalizer (A : Set G) :=
    (le_inf hXA₀ hXQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  intro g hg
  have hgprod : g ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left L T D.sylow_normalizes_component]
    exact hg.1
  obtain ⟨l, hl, t, ht, rfl⟩ := hgprod
  have hlN : l ∈ E.G₁ := by
    have hh := E.G₁.mul_mem (Subgroup.centralizer_le_normalizer _ hg.2) (E.G₁.inv_mem (hT ht))
    simpa only [mul_inv_cancel_right] using hh
  have hlprod : l ∈ (A : Set G) * (E.X : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A E.X hXA, ← hsplit]
    exact ⟨hl, hlN⟩
  obtain ⟨a, ha, x, hx, rfl⟩ := hlprod
  have hxt : x * t ∈ centralizer (E.V₁ : Set G) := by
    have hh := (centralizer (E.V₁ : Set G)).mul_mem
      ((centralizer (E.V₁ : Set G)).inv_mem (hAf ha)) hg.2
    simpa only [mul_assoc, inv_mul_cancel_left] using hh
  let xN : E.G₁ := ⟨x, hXN hx⟩
  let tN : E.G₁ := ⟨t, hT ht⟩
  let ρ := E.V₁.normalizerMonoidHom
  have hprod : ρ xN * ρ tN = 1 := by
    rw [← map_mul]
    change xN * tN ∈ ρ.ker
    rw [normalizerMonoidHom_ker]
    exact hxt
  have hxp : (ρ xN) ^ Nat.card E.X = 1 := by
    let j : E.X →* E.G₁ := inclusion hXN
    have hh := congrArg (fun z : E.X => ρ (j z)) (pow_card_eq_one' (x := (⟨x, hx⟩ : E.X)))
    simp only [map_pow, map_one] at hh
    have hj : j ⟨x, hx⟩ = xN := Subtype.ext (coe_inclusion hXN _)
    rw [hj] at hh
    exact hh
  obtain ⟨n, hn⟩ := T.isPGroup' (⟨t, ht⟩ : T)
  have htp : (ρ tN) ^ (2 ^ n) = 1 := by
    let j : T →* E.G₁ := inclusion hT
    have hh := congrArg (fun z : T => ρ (j z)) hn
    simp only [map_pow, map_one] at hh
    have hj : j ⟨t, ht⟩ = tN := Subtype.ext (coe_inclusion hT _)
    rw [hj] at hh
    exact hh
  have hxp' : (ρ xN) ^ (2 ^ n) = 1 := by
    rw [eq_inv_of_mul_eq_one_left hprod, inv_pow, htp, inv_one]
  have hx1 : ρ xN = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_right.pow_right n)
      (orderOf_dvd_of_pow_eq_one hxp) (orderOf_dvd_of_pow_eq_one hxp'))
  have hxC : x ∈ centralizer (E.V₁ : Set G) := by
    change xN ∈ ρ.ker at hx1
    rw [normalizerMonoidHom_ker] at hx1
    exact hx1
  exact (E.L₁ ⊔ (T : Subgroup G)).mul_mem
    (hAT (A.mul_mem ha (hker ⟨hx, hxC⟩))) (mem_sup_right ht)

/-- Match all three field subspaces to the original closure data. The equalities
are on the actual quotient, before taking ambient preimages. -/
structure FlagMatch {c : LocalGeometry.Coordinates D E.input.field}
    (f : LocalGeometry.InvariantFlag c) : Prop where
  point : c.binarySubspace (f.space 0) = E.point
  plane : c.binarySubspace (f.space 1) = E.plane
  threeSpace : c.binarySubspace (f.space 2) = E.threeSpace

/-- A field line is the preimage of a one-dimensional subspace through the
original marked quotient. Under 11.4.1's C_V(L)=1 this is an actual line of V. -/
@[expose] def IsFieldLine (c : LocalGeometry.Coordinates D E.input.field) (A : Subgroup G) : Prop :=
  ∃ U : Submodule E.input.field.Carrier c.Space,
    Module.finrank E.input.field.Carrier U = 1 ∧ c.preimage U = A

namespace FlagMatch
variable {E} {c : LocalGeometry.Coordinates D E.input.field}
  {f : LocalGeometry.InvariantFlag c} (hm : FlagMatch E f)
include hm

theorem point_eq : f.Vi 0 = E.V₁ := congrArg D.centralQuotientPreimage hm.point

theorem plane_eq : f.Vi 1 = E.V₂ := congrArg D.centralQuotientPreimage hm.plane

theorem threeSpace_eq : f.Vi 2 = E.V₃ := congrArg D.centralQuotientPreimage hm.threeSpace

theorem point_isFieldLine : IsFieldLine E c E.V₁ :=
  ⟨f.space 0, f.dimension 0, hm.point_eq⟩

theorem firstResidual_eq : f.Li 0 = E.L₁ := by
  change Closure.residualIn (L ⊓ normalizer (f.Vi 0 : Set G)) = E.L₁
  rw [hm.point_eq]
  rfl

theorem firstRadical_eq : f.Ri 0 = E.R₁ := by
  change (f.Li 0 ⊔ (T : Subgroup G)).pCoreIn 2 = E.R₁
  rw [hm.firstResidual_eq]
  rfl
end FlagMatch

/-- Discharge the F.7 local inputs from the preceding flag and marked parabolic
conclusions. The solvable residual and the possible two-core kernel are both
retained in the point-normalizer decomposition. -/
theorem localInputs_of_flag {c : LocalGeometry.Coordinates D E.input.field}
    (f : LocalGeometry.InvariantFlag c) (hm : FlagMatch E f)
    (hfix : E.L₁ ≤ centralizer (E.V₁ : Set G))
    (hsplit : L ⊓ E.G₁ = (E.L₁ ⊔ L.pCoreIn 2) ⊔ E.X)
    (hcartan : LocalGeometry.IsCartan T L E.X)
    (hker : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁ ⊔ L.pCoreIn 2) :
    LocalInputs E := by
  have hT := sylow_le_point_normalizer E f hm.point
  exact localInputs_of_point_geometry E hT
    (point_centralizer_bound E hT hfix hsplit hcartan.odd hker)
    (K_centralizes E hfix)

/-- The actual F.7 setup in the strict relative-component branch. Its earlier
flag and quotient-action inputs are explicit; none contains K=L₁ or parity. -/
@[expose] def sourceSetup_of_flag {c : LocalGeometry.Coordinates D E.input.field}
    (f : LocalGeometry.InvariantFlag c) (hm : FlagMatch E f)
    (hfix : E.L₁ ≤ centralizer (E.V₁ : Set G))
    (hsplit : L ⊓ E.G₁ = (E.L₁ ⊔ L.pCoreIn 2) ⊔ E.X)
    (hcartan : LocalGeometry.IsCartan T L E.X)
    (hker : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁ ⊔ L.pCoreIn 2)
    (hLi : Source.ComponentIn E.M₁ E.L₁)
    (hK : Source.ComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K) :
    ChapterF.Section07.Track.SourceSetup (family E) :=
  sourceSetup E (localInputs_of_flag E f hm hfix hsplit hcartan hker)
    (strict_component_escapes E hLi hK hlt)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even
