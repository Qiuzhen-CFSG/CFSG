module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoOppositeAction
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Elementary D in the central b=2 branch

The Frattini subgroup of D is the Frattini image of its residual R.
Relative normality of D makes this subgroup normal in a full vertex Sylow.
The opposite natural fixed spaces separate R from Z once the earlier
local center vanishes. A nontrivial normal subgroup of a finite two-group
meets its central involutions, which belong to Z. Thus Phi(D)=1.

This is the central branch of DGS 10.4(a), not the noncentral D=Z
identity. A nonzero residual remains possible, as required by 10.10.
Source: DGS, *Groups and Graphs* (1985), 10.4, printed p.156.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G]

private theorem normal_two_subgroup_eq_bot (S A : Subgroup G) [Finite S]
    (hp : IsPGroup 2 S) (hle : A ≤ S) (hn : S ≤ normalizer (A : Set G))
    (hd : Disjoint A (omegaCenterIn S)) : A = ⊥ := by
  let N := A.subgroupOf S
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hle).mpr hn
  let : Fact (IsPGroup 2 S) := ⟨hp⟩
  by_contra hA
  have hN : Nontrivial N := (nontrivial_iff_ne_bot N).mpr (by
    intro he
    apply hA
    rw [←map_subgroupOf_eq_of_le hle]
    change N.map S.subtype = ⊥
    rw [he,Subgroup.map_bot])
  obtain ⟨C,_,hCN,hcard,hCS⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) N hN
  have hC : C = ⊥ := by
    apply bot_unique
    intro x hx
    have hxA : (x : G) ∈ A := hCN hx
    have hxZ : (x : G) ∈ omegaCenterIn S := by
      apply (mem_omegaCenterIn_iff _ _).mpr
      refine ⟨x.property,?_,?_⟩
      · intro y hy
        exact congrArg S.subtype ((mem_center_iff.mp (hCS hx)) ⟨y,hy⟩)
      · have he : (⟨x,hx⟩ : C) ^ 2 = 1 := by
          rw [←hcard]
          exact pow_card_eq_one'
        exact congrArg (S.subtype.comp C.subtype) he
    exact Subtype.ext (disjoint_def.mp hd hxA hxZ)
  simp [hC] at hcard

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (hb : b (family P) = 2) {t v m w z : Vertex (family P)}
    (d : BTwoOppositeGeometry (family P) t v m w z)
    (T : Sylow 2 (stabilizer (family P) v))
    (hT : (T : Subgroup (stabilizer (family P) v)).map (stabilizer (family P) v).subtype ≤ d.actor)
    (hdis : Disjoint d.residual (Z (family P) v))

include h hS hb d T hT hdis

/-- The central branch of 10.4(a): the literal D has trivial Frattini
subgroup, using the earlier trivial local center through residual separation. -/
theorem BTwoOppositeGeometry.frattini_eq_bot :
    frattini (D (family P) m t) = ⊥ := by
  let := finite_endpoints h
  let A := (frattini (D (family P) m t)).map (D (family P) m t).subtype
  let S := (T : Subgroup (stabilizer (family P) v)).map (stabilizer (family P) v).subtype
  let : Finite S := Finite.of_injective
    (inclusion (map_subtype_le _)) (inclusion_injective _)
  have hAR : A ≤ d.residual := by
    rw [show A = (frattini (D (family P) m t)).map (D (family P) m t).subtype from rfl,
      d.frattini_residual h hS hb]
    exact map_subtype_le _
  have hAS : A ≤ S := (map_subtype_le _).trans
    (d.separated.trans (pCoreIn_le_sylow _ T))
  have hn : S ≤ normalizer (A : Set G) :=
    (hT.trans (d.normalized h hS hb)).trans
      (normalizer_le_normalizer_characteristic_image _ (frattini _))
  have hZ : omegaCenterIn S ≤ Z (family P) v :=
    le_iSup (fun R : Sylow 2 (stabilizer (family P) v) =>
      omegaCenterIn ((R : Subgroup (stabilizer (family P) v)).map
        (stabilizer (family P) v).subtype)) T
  have ha := normal_two_subgroup_eq_bot S A (T.isPGroup'.map _) hAS hn
    (hdis.mono hAR hZ)
  exact (map_eq_bot_iff_of_injective _ (D (family P) m t).subtype_injective).mp ha

/-- The actual D subgroup is elementary abelian; no equality D=Z is asserted. -/
theorem BTwoOppositeGeometry.elementary : IsElementaryAbelian 2 (D (family P) m t) := by
  let := finite_endpoints h
  let : Finite (D (family P) m t) := Finite.of_injective
    (inclusion (d.separated.trans (Q_le_stabilizer (family P) v))) (inclusion_injective _)
  let : Fact (IsPGroup 2 (D (family P) m t)) :=
    ⟨(isPGroup_pCoreIn 2 (stabilizer (family P) v)).to_le d.separated⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
    (d.frattini_eq_bot h hS hb T hT hdis)

omit h hS hb d T hT hdis

/-- The literal triple intersection in 10.4(c). Its identification with
C_Q(W) is proved separately, retaining the actual opposite conjugator. -/
def centralResidual (F : Bool → Subgroup G) (m t w z : Vertex F) : Subgroup G :=
  (D F m t ⊓ Q F w) ⊓ Q F z

variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The marked natural center action and vanishing earlier local center
supply all central D calculations. The opposite lift is constructed. -/
theorem BTwoCenterActionData.central_D_structure (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (hb : b (family P) = 2) {v m w t : Vertex (family P)}
    (c : BTwoCenterActionData (family P) v m w k W)
    (hω : omegaCenterIn c.actor = ⊥)
    (ht : (graph (family P)).Adj v t) (hne : t ≠ m) :
    ∃ g : c.actor, (g : G) • m = t ∧
      D (family P) m t ≤ Q (family P) v ∧
      c.actor ≤ normalizer (D (family P) m t : Set G) ∧
      IsElementaryAbelian 2 (D (family P) m t) ∧
      D (family P) m t = Z (family P) v ⊔
        centralResidual (family P) m t w ((g : G) • w) ∧
      Disjoint (centralResidual (family P) m t w ((g : G) • w)) (Z (family P) v) ∧
      centralResidual (family P) m t w ((g : G) • w) ≤
        centralizer ((Z (family P) w ⊔ Z (family P) ((g : G) • w) : Subgroup G) : Set G) := by
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,hd,hker⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  have hdis : Disjoint d.residual (Z (family P) v) := disjoint_iff.mpr
    (bot_unique (hker.trans hω.le))
  have hT : (c.sylow : Subgroup (stabilizer (family P) v)).map
      (stabilizer (family P) v).subtype ≤ d.actor := hd.symm ▸ c.sylow_le_actor
  exact ⟨g,hg,d.separated,hd ▸ d.normalized h hS hb,
    d.elementary h hS hb c.sylow hT hdis,d.decomposition h hS hb,
    hdis,d.residual_centralizes h⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
