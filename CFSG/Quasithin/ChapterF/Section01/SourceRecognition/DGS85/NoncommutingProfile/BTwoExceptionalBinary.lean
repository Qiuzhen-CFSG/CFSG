module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalNonbinary
public import Theory.Representation.SL2.NaturalAbelianExponent

/-!
# The exceptional alpha field is binary

The nonbinary branch already makes the literal alpha core abelian, while
its center and quotient are marked natural modules. Conjugation then descends
through the actual alpha-core kernel. The two-root exponent obstruction
forces every square to be trivial, contradicting the proved non-elementarity.
Thus q_alpha = 2, without assuming an exceptional model or a field equality.

Source: DGS, Groups and Graphs (1985), (5.17), p.117, and the proof of
(10.9), p.163. This proves the exponent step directly from the marked natural
layers; recognition and path parameters remain separate obligations.
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
local instance binaryAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

/-- The actual exceptional alpha field has exactly two elements. -/
theorem BTwoCenterActionData.exceptional_linear_alpha_field_binary
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
    (hD : D F m t = Z F v) (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) : Nat.card k = 2 := by
  classical
  have hc : 1 < Nat.card k := by
    let := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  by_contra htwo
  have hk : 2 < Nat.card k := by omega
  let hm := c.exceptional_nonbinary_core_commutative h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ hD E hk
  let := hm
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
  have hZQ : Z F v ≤ Q F v := fun _ hx =>
    ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h v).1 hx)).1
  have hjs : Function.Surjective j := by
    intro y
    refine ⟨⟨⟨y,hZQ y.property⟩,(hker _).mpr y.property⟩,rfl⟩
  have hzs : Function.Surjective z := eZ.toAddEquiv.toMultiplicative.surjective.comp
    (c.coordinates.onto.comp hjs)
  have hkill : c.quotient.ker ≤ c.coreConjugation.ker := by
    intro a ha
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (a : G)*(x : G)*(a : G)⁻¹ = (x : G)
    have haQ' : a ∈ (Q F v).subgroupOf c.actor := c.kernel ▸ ha
    have haQ : (a : G) ∈ Q F v := haQ'
    have hh := congrArg Subtype.val (mul_comm (⟨a,haQ⟩ : Q F v) x)
    change (a : G)*(x : G)=(x : G)*(a : G) at hh
    rw [hh,mul_inv_cancel_right]
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
  apply c.exceptional_linear_core_not_elementary h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ hD E
  refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
  apply Representation.SL2.square_eq_one_of_natural_abelian_extension a ha0 ha1 f hf z ⟨hzi,hzs⟩
    c.quotient c.onto c.coreConjugation hkill
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

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
