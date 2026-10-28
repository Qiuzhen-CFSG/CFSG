module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalFrattini
public import Theory.Representation.SL2.NaturalCentralCommutator

/-!
# The nonbinary exceptional alpha core has exponent four

The literal alpha-core quotient is a sum of natural modules; its central
Frattini subgroup is the natural center. Nonbinary natural commutator
vanishing makes the core abelian. Its fourth powers are trivial because
its squares lie in the elementary Frattini subgroup. The already proved
non-elementarity then supplies an actual element of order four.

This isolates the remaining exponent obstruction in DGS (10.9), printed
p.163, where the source invokes (5.17), p.117. It does not yet prove the
nonbinary case impossible. The original full-endpoint application is in
BTwoExceptionalNonbinarySource.
-/

public noncomputable section
open Matrix Subgroup Representation Representation.RankOne.QuadraticRecognition
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local instance nonbinaryAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

/-- The actual natural center has equivariant coordinates at its original field marking. -/
theorem BTwoCenterActionData.center_natural_coordinates
    {v m w : Vertex F} (c : BTwoCenterActionData F v m w k W)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    ∃ e : W ≃ₗ[ZMod 2] (Fin 2 → k),
      ∀ g x, e (c.representation g x) = g.val *ᵥ e x := by
  let : Finite W := Finite.of_injective E E.injective
  obtain ⟨n,e,he⟩ := sl2_natural_copies c.representation c.imageSylow c.quadratic
    c.generated c.fixed_bot
  have hc := (Nat.card_congr E.toEquiv).symm.trans (Nat.card_congr e.toEquiv)
  simp only [Nat.card_fun,Nat.card_fin] at hc
  have hk : 1 < Nat.card k := by
    let := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hn : n = 1 := by
    rw [←pow_mul] at hc
    have hh := Nat.pow_right_injective hk hc
    omega
  subst n
  refine ⟨e.trans (LinearEquiv.funUnique (Fin 1) (ZMod 2) (Fin 2 → k)),?_⟩
  intro g x
  exact he g x 0

/-- In the hypothetical nonbinary exceptional branch the actual alpha core is abelian. -/
theorem BTwoCenterActionData.exceptional_nonbinary_core_commutative
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K))
    (hD : D F m t = Z F v) (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (hk : 2 < Nat.card k) : IsMulCommutative (Q F v) := by
  classical
  obtain ⟨hN,hE,σ,d,_,_,n,e,he⟩ := c.linear_core_natural_copies h hB hSyl hb hactor
    hcentral ht hne hcomm hnot eβ
  let := hN
  let := hE
  obtain ⟨eZ,heZ⟩ := c.center_natural_coordinates E
  let f := e.toAddEquiv.toMultiplicative.toMonoidHom.comp d.coordinates
  have hf : Function.Surjective f := e.toAddEquiv.toMultiplicative.surjective.comp d.onto
  have hker (x : Q F v) : x ∈ f.ker ↔ (x : G) ∈ Z F v := by
    change e.toAddEquiv.toMultiplicative (d.coordinates x) = 1 ↔ _
    rw [←e.toAddEquiv.toMultiplicative.map_one,e.toAddEquiv.toMultiplicative.injective.eq_iff,
      d.coordinates_eq_one_iff,hD]
  have hcz : f.ker ≤ center (Q F v) := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (graph_Q_centralizes_Z h v y.property x ((hker x).mp hx)).symm
  let j : f.ker →* Z F v := {
    toFun x := ⟨((x : Q F v) : G),(hker x).mp x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y heq
    apply Subtype.ext; apply Subtype.ext
    exact congrArg (fun z : Z F v => (z : G)) heq
  have hω := c.omega_eq_bot_of_central_neighbor h hB hSyl hactor hcentral
  have hci : Function.Injective c.coordinates.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [c.coordinates.kernel_eq,hω,bot_subgroupOf]
  let z := eZ.toAddEquiv.toMultiplicative.toMonoidHom.comp (c.coordinates.coordinates.comp j)
  have hzi : Function.Injective z := eZ.toAddEquiv.toMultiplicative.injective.comp (hci.comp hj)
  have hex : ∃ a : k, a ≠ 0 ∧ a ≠ 1 := by
    by_contra! hn
    have hc : Nat.card k ≤ 2 := by
      let := Fintype.ofFinite k
      rw [Nat.card_eq_fintype_card]
      calc
        Fintype.card k = (Finset.univ : Finset k).card := rfl
        _ ≤ ({0,1} : Finset k).card := Finset.card_le_card (by
          intro x _
          by_cases hx : x = 0
          · simp [hx]
          · simp [hn x hx])
        _ ≤ 2 := by simp
    omega
  obtain ⟨a,ha0,ha1⟩ := hex
  apply Representation.SL2.commutative_of_natural_central_extension a ha0 ha1 f hf hcz z hzi
    c.quotient c.onto c.coreConjugation
  · intro g x
    change e (d.coordinates (c.coreConjugation g x)).toAdd = _
    have hh : (d.coordinates (c.coreConjugation g x)).toAdd =
        σ (c.quotient g) (d.coordinates x).toAdd := d.equivariant g x
    rw [hh]
    funext i
    exact he (c.quotient g) (d.coordinates x).toAdd i
  · intro g x y hxy
    change eZ (c.coordinates.coordinates (j y)).toAdd =
      (c.quotient g).val *ᵥ eZ (c.coordinates.coordinates (j x)).toAdd
    rw [←heZ]
    congr 1
    have hjy : j y = ⟨(g : G) * (j x : G) * (g : G)⁻¹,
        (mem_normalizer_iff.mp (c.coordinates.normalized g.property) (j x)).mp (j x).property⟩ := by
      apply Subtype.ext
      exact (congrArg (fun q : Q F v => (q : G)) hxy).symm
    rw [hjy]
    exact c.coordinates.equivariant g (j x)

/-- The remaining nonbinary obstruction is an abelian core of exponent exactly four. -/
theorem BTwoCenterActionData.exceptional_nonbinary_core_exponent_four
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K))
    (hD : D F m t = Z F v) (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (hk : 2 < Nat.card k) : IsMulCommutative (Q F v) ∧
      (frattini (Q F v)).map (Q F v).subtype = Z F v ∧
      (∀ x : Q F v, x ^ 4 = 1) ∧ ∃ x : Q F v, orderOf x = 4 := by
  let := finite_endpoints h
  let : Finite (Q F v) := Finite.of_injective
    (inclusion (Q_le_stabilizer F v)) (inclusion_injective _)
  let : Fact (IsPGroup 2 (Q F v)) := ⟨isPGroup_pCoreIn 2 (stabilizer F v)⟩
  let := graph_Z_elementary h v
  have hm := c.exceptional_nonbinary_core_commutative h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ hD E hk
  let := hm
  have hphi := c.exceptional_linear_frattini h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ hD E
  have hfour (x : Q F v) : x ^ 4 = 1 := by
    have hx : ((x : G)^2) ∈ Z F v := by
      rw [←hphi]
      exact mem_map_of_mem (Q F v).subtype (pth_power_mem_frattini_of_isPGroup (p := 2) x)
    have hs := elemPow_eq_one_of_isElementaryAbelian (p := 2) ((x : G)^2) hx
    apply Subtype.ext
    change (x : G)^4 = 1
    simpa only [←pow_mul] using hs
  refine ⟨hm,hphi,hfour,?_⟩
  have hnelem := c.exceptional_linear_core_not_elementary h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ hD E
  have hsq : ∃ x : Q F v, x^2 ≠ 1 := by
    by_contra! hh
    exact hnelem { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hh }
  obtain ⟨x,hx⟩ := hsq
  exact ⟨x,orderOf_eq_prime_pow (p := 2) (n := 1) hx (hfour x)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
