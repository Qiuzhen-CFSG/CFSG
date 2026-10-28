module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.SplitSeed.FixedSpace
public import Theory.Representation.PSL3Two.ParabolicFixedFree
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.SymmetricModels
public import Theory.GroupTheory.SylowNormalGenerationFrattini

/-!
# Fixed-point control through the line parabolic

Let Q ≤ W_K be normalized by the full preimage in K of the marked line
parabolic, and suppose a component Sylow fixes Q pointwise and its image
contains R. That Sylow image lies in the parabolic and normally generates
it, using the actual S₄ identification. The faithful plus action therefore
makes the entire parabolic fix Q.

For q ∈ Q, odd-orbit averaging gives a ∈ [W_K,K] with exactly the same
conjugation on K as q. The parabolic fixes a, so doubled-natural fixed-point
freeness forces a = 1. Thus K centralizes Q. The proof takes place in W_K;
no placement of Q inside [W_K,K] is assumed.

The source seed application is assembled in Placement.lean from the
literal Baumann lift and the marked moving condition. The model calculation
in ParabolicFixedFree is used only as a theorem about the specified matrices,
not as a later source marking or containment theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 13.6.20, printed p.931. The averaging argument is the
standard odd-orbit product, also used in the checked proof of 13.6.11.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.SplitSeed.Placement.FixedControl
open BinaryLinearThree Matrix.PSL3Two

private theorem sylow_le_parabolic (S : Sylow 2 BinaryLinearThree.Group) (hR : R ≤ (S : Subgroup _)) :
    (S : Subgroup _) ≤ lineParabolicSL := by
  have hcS : Nat.card S = 8 := by
    rw [S.card_eq_multiplicity, card_SL]
    decide +kernel
  have hcR : Nat.card (R.subgroupOf (S : Subgroup _)) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hR).toEquiv).trans card_R
  have hi : (R.subgroupOf (S : Subgroup _)).index = 2 := by
    have h := (R.subgroupOf (S : Subgroup _)).index_mul_card
    rw [hcR, hcS] at h
    omega
  let : (R.subgroupOf (S : Subgroup _)).Normal := normal_of_index_eq_two hi
  have hn := (normal_subgroupOf_iff_le_normalizer hR).mp inferInstance
  rwa [CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.normalizer_radical] at hn

private theorem parabolic_involutions_generate :
    closure {g : lineParabolicSL | g ^ 2 = 1} = ⊤ := by
  let e := MarkedAutomorphisms.lineEquivSymmetric
  apply top_unique
  intro g _
  have hh : (⊤ : Subgroup (Equiv.Perm (Fin 4))) ≤
      (closure {g : lineParabolicSL | g ^ 2 = 1}).comap e.symm.toMonoidHom := by
    rw [← symmetric_involutions_generate (Fin 4), closure_le]
    intro x hx
    apply Subgroup.subset_closure
    change e.symm x ^ 2 = 1
    rw [← map_pow, hx, map_one]
  simpa using hh (mem_top (e g))

private theorem fixed_of_sylow_normal_generation
    {H A : Type*} [Group H] [Group A] [Finite H]
    (hgen : closure {g : H | g ^ 2 = 1} = ⊤)
    (ρ : H →* MulAut A) (Q : Subgroup A)
    (hn : ∀ g : H, ∀ q ∈ Q, ρ g q ∈ Q)
    (S : Sylow 2 H) (hS : ∀ g ∈ S, ∀ q ∈ Q, ρ g q = q) :
    ∀ g : H, ∀ q ∈ Q, ρ g q = q := by
  let F : Subgroup H :=
    { carrier := {g | ∀ q ∈ Q, ρ g q = q}
      one_mem' := by simp
      mul_mem' := by
        intro g h hg hh q hq
        rw [map_mul, MulAut.mul_apply, hh q hq, hg q hq]
      inv_mem' := by
        intro g hg q hq
        apply (ρ g).injective
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply, hg q hq] }
  let : F.Normal := ⟨by
    intro n hnF g q hq
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply,
      hnF _ (hn g⁻¹ q hq), ← MulAut.mul_apply, ← map_mul, mul_inv_cancel,
      map_one, MulAut.one_apply]⟩
  have hle : normalClosure (S : Set H) ≤ F := normalClosure_le_normal hS
  rw [normalClosure_sylow_eq_top_of_involutions S hgen] at hle
  intro g
  exact hle (mem_top g)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.SplitSeed.Placement.FixedControl

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.SplitSeed.Placement
open ComponentSelection A5Module
variable {G : Type*} [Group G] [Finite G] {K L T : Subgroup G} {z v : G}

/-- A subgroup of W_K normalized by the line-parabolic preimage and fixed
by the indicated Sylow is centralized by K. This does not require the
subgroup to lie in U_K. -/
theorem fixed_control
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hK : K ≤ Gv v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (d : DoubledCoordinates K L T z v hK hL hz)
    (P : Sylow 2 K)
    (hR : BinaryLinearThree.R ≤
      ((P.mapSurjective d.actionMap_surjective) : Subgroup BinaryLinearThree.Group))
    (Q : Subgroup G) (hQW : Q ≤ WK K L T z v)
    (hn : (Matrix.PSL3Two.lineParabolicSL.comap d.actionMap).map K.subtype ≤
      normalizer (Q : Set G))
    (hfix : ∀ k : K, k ∈ P → ∀ q ∈ Q, (k : G) * q * (k : G)⁻¹ = q) :
    Q ≤ centralizer (K : Set G) := by
  let W₀ := WK K L T z v
  let ρ : BinaryLinearThree.Group →* MulAut W₀ :=
    (plusAction K L T z v hL hz).comp (modelEmbedding d)
  have hρ (k : K) (w : W₀) :
      (ρ (d.actionMap k) w : G) = (k : G) * (w : G) * (k : G)⁻¹ := by
    change (plusAction K L T z v hL hz (modelEmbedding d (d.actionMap k)) w : G) = _
    rw [modelEmbedding_actionMap]
    rfl
  let P₀ := Matrix.PSL3Two.lineParabolicSL
  let S := P.mapSurjective d.actionMap_surjective
  have hSP : (S : Subgroup BinaryLinearThree.Group) ≤ P₀ :=
    FixedControl.sylow_le_parabolic S hR
  let τ := ρ.comp P₀.subtype
  have hnorm : ∀ g : P₀, ∀ q ∈ Q.subgroupOf W₀, τ g q ∈ Q.subgroupOf W₀ := by
    intro g q hq
    obtain ⟨k, hk⟩ := d.actionMap_surjective g
    have hkN : (k : G) ∈ normalizer (Q : Set G) :=
      hn (mem_map.mpr ⟨k, show d.actionMap k ∈ P₀ from hk ▸ g.property, rfl⟩)
    change (ρ (g : BinaryLinearThree.Group) q : G) ∈ Q
    rw [← hk, hρ]
    exact (mem_normalizer_iff.mp hkN _).mp hq
  have hsfix : ∀ g ∈ S.subtype hSP, ∀ q ∈ Q.subgroupOf W₀, τ g q = q := by
    intro g hg q hq
    obtain ⟨k, hk, he⟩ := hg
    change d.actionMap k = (g : BinaryLinearThree.Group) at he
    apply Subtype.ext
    change (ρ (g : BinaryLinearThree.Group) q : G) = (q : G)
    rw [← he, hρ]
    exact hfix k hk q hq
  have hPfix := FixedControl.fixed_of_sylow_normal_generation
    FixedControl.parabolic_involutions_generate τ (Q.subgroupOf W₀)
    hnorm (S.subtype hSP) hsfix
  have hkfix (k : K) (hk : d.actionMap k ∈ P₀) (q : G) (hq : q ∈ Q) :
      (k : G) * q * (k : G)⁻¹ = q := by
    have h := congrArg (fun w : W₀ => (w : G))
      (hPfix ⟨d.actionMap k, hk⟩ ⟨q, hQW hq⟩ hq)
    exact (hρ k ⟨q, hQW hq⟩).symm.trans h
  intro q hq
  obtain ⟨a, ha, _, he⟩ :=
    Theory.GroupAction.exists_conjugating_element_of_elementary_displacement
      K (UK K L T z v) W₀
      ((K_le_plusActor K L T v).trans (plusActor_normalizes_WK K L T z v hL hz))
      P ⟨q, hQW hq⟩ (fun k hk => hfix k hk q hq) (fun k => by
        rw [UK, commutator_comm]
        exact commutator_mem_commutator k.property (hQW hq))
  have haP (k : K) (hk : d.actionMap k ∈ P₀) :
      (k : G) * a * (k : G)⁻¹ = a := by
    have hqk : q * (k : G) = (k : G) * q :=
      (mul_inv_eq_iff_eq_mul.mp (hkfix k hk q hq)).symm
    have hak : a * (k : G) * a⁻¹ = (k : G) := by
      rw [he k, hqk, mul_inv_cancel_right]
    exact mul_inv_eq_iff_eq_mul.mpr (mul_inv_eq_iff_eq_mul.mp hak).symm
  have ha0 : (d.moduleEquiv ⟨a, ha⟩).toAdd = 0 := by
    apply BinaryLinearThree.ParabolicFixedFree.doubled_fixed_eq_zero
    intro g hg
    obtain ⟨k, rfl⟩ := d.actionMap_surjective g
    have hk : d.actionMap k ∈ P₀ := (map_subtype_le _) hg
    have heq := d.equivariant k ⟨a, ha⟩
    have hka : conjugationAction _ _ (K_normalizes_UK K L T z v hL hz) k ⟨a, ha⟩ =
        (⟨a, ha⟩ : UK K L T z v) := Subtype.ext (haP k hk)
    rw [hka] at heq
    exact congrArg Multiplicative.toAdd heq.symm
  have ha1 : a = 1 := by
    have h : d.moduleEquiv (⟨a, ha⟩ : UK K L T z v) = d.moduleEquiv 1 := by
      rw [map_one]
      exact congrArg Multiplicative.ofAdd ha0
    exact congrArg Subtype.val (d.moduleEquiv.injective h)
  apply mem_centralizer_iff.mpr
  intro k hk
  have h := he ⟨k, hk⟩
  rw [ha1, one_mul, inv_one, mul_one] at h
  exact (mul_inv_eq_iff_eq_mul.mp h.symm).symm

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.SplitSeed.Placement
