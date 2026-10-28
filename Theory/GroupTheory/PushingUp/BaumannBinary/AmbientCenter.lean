module
public import Theory.GroupTheory.PResidual.SylowCenterMovement
public import Theory.GroupTheory.PushingUp.BaumannBinary.ActionKernel
public import Theory.GroupTheory.ConjugateSpanNormalClosure
public import Theory.GroupTheory.SylowCenterFixedSpan
public import Theory.GroupTheory.PResidual.TwiceOddPrime
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# Ambient Sylow centers above a binary Baumann closure

For a normal subgroup X with a marked SL₂(2) quotient, the actual
Baumann Sylow-center closure is elementary and has action kernel O₂(X).
Its embedded image is the Sylow-center span of X, hence normal in the
ambient finite group. The odd residual of the faithful action has order
three, so coprime movement forces every ambient Sylow omega-center to
act nontrivially on X.

The field is arbitrary of cardinality two, and the original quotient map
is retained. Source: DGS, Groups and Graphs (1985), 6.5, printed p.121.
The source closure premises are discharged in the literal application
DGS85/LocalStructure/BinaryCenterExclusion.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
public noncomputable section
namespace Theory.GroupTheory.BaumannBinary
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- A marked SL₂(2) Baumann closure cannot centralize an ambient Sylow omega-center. -/
theorem ambient_sylow_omega_noncentral_two
    (X : Subgroup G) [X.Normal] (P : Sylow 2 X) (T : Sylow 2 G)
    (hc : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (hP : NoCharacteristicNormal (P : Subgroup X))
    (q : X →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 X) (hF : Nat.card F = 2) :
    ¬ omegaCenterIn (T : Subgroup G) ≤ centralizer (X : Set G) := by
  let Vi := centerClosure (P : Subgroup X)
  let : IsElementaryAbelian 2 Vi := (centerClosure_reduced P hc).elementary
  let V := Vi.map X.subtype
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  have hV : V = AmalgamGraph.sylowCenterSpan X := by
    rw [AmalgamGraph.sylowCenterSpan_eq_conjugateSpan X X le_rfl
      (fun _ => map_subtype_le _) P]
    change (normalClosure (omegaCenterIn (P : Subgroup X) : Set X)).map X.subtype = _
    rw [map_normalClosure_eq_conjugateSpanBy_range,
      NilesRankOneKernel.omegaCenterIn_map_injective _ X.subtype_injective,range_subtype]
  let : V.Normal := by
    rw [hV]
    apply normalizer_eq_top_iff.mp
    apply top_unique
    intro g _
    rw [mem_normalizer_iff_map_conj_eq]
    change (AmalgamGraph.sylowCenterSpan X).map (MulAut.conj g).toMonoidHom = _
    rw [←AmalgamGraph.sylowCenterSpan_map]
    congr 1
    exact mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (X : Set G) from
      X.normalizer_eq_top.symm ▸ mem_top g)
  have hker : q.ker = (centralizer (V : Set G)).subgroupOf X := by
    rw [hk,←centerClosure_centralizer P hc hP q hq hk (n := 1) (by decide)
      (by simpa only [pow_one] using hF)]
    ext x
    constructor
    · intro hx v hv
      obtain ⟨w,hw,rfl⟩ := hv
      exact congrArg Subtype.val (hx w hw)
    · intro hx v hv
      exact Subtype.ext (hx v (mem_map_of_mem X.subtype hv))
  have hcard : Nat.card SL(2,F) = 2*3 := by
    rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,hF]
    decide
  have hr : Nat.card (pResidual 2 SL(2,F)) = 3 :=
    card_twoResidual_of_card_twice_odd_prime (by decide : Odd 3) hcard
  apply sylow_omega_not_centralizes_of_odd_residual_action T X V q hq hker
  · rw [hr]; decide
  · intro he
    rw [he,card_bot] at hr
    omega
end Theory.GroupTheory.BaumannBinary
