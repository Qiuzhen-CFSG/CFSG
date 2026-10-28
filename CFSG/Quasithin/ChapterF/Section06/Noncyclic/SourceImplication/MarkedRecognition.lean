module
public import Theory.GroupAction.MarkedCubicRecognition
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.ThreeClass

/-!
# The marked three-group branch of F.6.16

F.6.6 supplies the actual internal complement L T, and coprime orders
make its intersection trivial. The cross-core involutions have distinct
opposite actions on the two cubic residuals. Consequently they generate
T of order four, giving its marked E₄ coordinates. The class bound and
A.1.24 identify L; evaluation on chosen cubic generators retains its
markings. Equivariance reconstructs the ambient group as the fixed
semidirect product, including the literal residual and complement maps.
The elementary model then identifies the ambient group with S₃ × S₃.

The final theorem proves the entire three-group disjunction with only
the authorized universal A.1.31(1) input and the three-group hypothesis
in addition to the original source assumptions. Proving that L is a
three-group and discharging A.1.31(1) remain with the parent assembly.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
F.6.16, printed p.308 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Noncyclic.MarkedRecognition
open MarkedCubicRecognition
universe u v
variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

abbrev residualLine (H : Subgroup G) : Subgroup (pResidual 2 G) :=
  ((pResidual 2 H).map H.subtype).subgroupOf (pResidual 2 G)

/-- Coordinates retain the residual lines, the full complement, and its literal
conjugation action in the original ambient group. -/
structure MarkedModel (G₁ G₂ : Subgroup G) (M : Type v) [Group M]
    (ρ : Four →* MulAut M) (U V : Subgroup M) where
  residualEquiv : M ≃* pResidual 2 G
  complementEquiv : Four ≃* (G₁ ⊓ G₂ : Subgroup G)
  ambientEquiv : (M ⋊[ρ] Four) ≃* G
  left_line : U.map residualEquiv.toMonoidHom = residualLine G₁
  right_line : V.map residualEquiv.toMonoidHom = residualLine G₂
  equivariant : ∀ t z, residualEquiv (ρ t z) =
    MulAut.conjNormal (complementEquiv t : G) (residualEquiv z)
  residual_apply : ∀ z, ambientEquiv (SemidirectProduct.inl z) = (residualEquiv z : G)
  complement_apply : ∀ t, ambientEquiv (SemidirectProduct.inr t) = (complementEquiv t : G)
  complement_generate : zpowers (complementEquiv first) ⊔ zpowers (complementEquiv second) = ⊤

/-- F.6.6 and coprime orders give the actual internal complement. -/
theorem residual_complement (h : IsGoldschmidtTriple G₁ G₂)
    (hL : IsPGroup 3 (pResidual 2 G)) :
    (pResidual 2 G).IsComplement' (G₁ ⊓ G₂) := by
  obtain ⟨T, hT⟩ := h.intersection_sylow
  apply isComplement'_of_disjoint_and_mul_eq_univ
    (hL.disjoint_of_coprime (hT ▸ T.isPGroup') (by decide))
  exact h.twoResidual_mul_intersection

/-- The actual marked involutions generate the Sylow four-group. -/
theorem exists_marked_complement (h : IsGoldschmidtTriple G₁ G₂)
    (hcore : pCore 2 G = ⊥) (hL : IsPGroup 3 (pResidual 2 G))
    (hnot : ¬ Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* C2)) :
    ∃ d : Four ≃* (G₁ ⊓ G₂ : Subgroup G),
      MarkedCubicClassTwo.CubicMarking (residualLine G₁) (residualLine G₂)
        (MulAut.conjNormal (d first : G)) (MulAut.conjNormal (d second : G)) ∧
      zpowers (d first) ⊔ zpowers (d second) = ⊤ := by
  obtain ⟨_, _, ⟨eT⟩⟩ :=
    (h.odd_residual_small_sylow hcore (odd_residual_of_three hL)).resolve_left hnot
  have hcard : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 4 := by
    rw [Nat.card_congr eT.toEquiv]
    simp
  obtain ⟨t₁, t₂, ht₁, ht₂, ho₁, ho₂, hc, hm⟩ :=
    exists_residual_cubic_marking h hcore hL hnot
  let x : (G₁ ⊓ G₂ : Subgroup G) := ⟨t₁, ht₁⟩
  let y : (G₁ ⊓ G₂ : Subgroup G) := ⟨t₂, ht₂⟩
  have hx : x ^ 2 = 1 := Subtype.ext (ho₁ ▸ pow_orderOf_eq_one t₁)
  have hy : y ^ 2 = 1 := Subtype.ext (ho₂ ▸ pow_orderOf_eq_one t₂)
  have hx1 : x ≠ 1 := by
    intro he
    have he' : t₁ = 1 := congrArg Subtype.val he
    rw [he', orderOf_one] at ho₁
    contradiction
  have hy1 : y ≠ 1 := by
    intro he
    have he' : t₂ = 1 := congrArg Subtype.val he
    rw [he', orderOf_one] at ho₂
    contradiction
  have hxy : x ≠ y := by
    intro he
    apply (marked_actions_distinct hm).2.2
    exact congrArg (fun t : G => (MulAut.conjNormal t : MulAut (pResidual 2 G)))
      (congrArg Subtype.val he)
  obtain ⟨d, hd₁, hd₂, hdgen⟩ := exists_four_equiv hcard x y hx hy
    (show Commute x y from Subtype.ext hc.eq) hx1 hy1 hxy
  refine ⟨d, ?_, ?_⟩
  · simpa only [hd₁, hd₂] using hm
  · simpa only [hd₁, hd₂] using hdgen

private theorem assemble_model {M : Type v} [Group M]
    (h : IsGoldschmidtTriple G₁ G₂) (hL : IsPGroup 3 (pResidual 2 G))
    (ρ : Four →* MulAut M) (U V : Subgroup M)
    (eM : M ≃* pResidual 2 G) (d : Four ≃* (G₁ ⊓ G₂ : Subgroup G))
    (hU : U.map eM.toMonoidHom = residualLine G₁)
    (hV : V.map eM.toMonoidHom = residualLine G₂)
    (hf : ∀ z, eM (ρ first z) = MulAut.conjNormal (d first : G) (eM z))
    (hs : ∀ z, eM (ρ second z) = MulAut.conjNormal (d second : G) (eM z))
    (hgen : zpowers (d first) ⊔ zpowers (d second) = ⊤) :
    Nonempty (MarkedModel G₁ G₂ M ρ U V) := by
  obtain ⟨e, heL, heT⟩ := exists_internal_extension (pResidual 2 G) (G₁ ⊓ G₂)
    (residual_complement h hL) ρ eM d hf hs
  refine ⟨⟨eM, d, e, hU, hV, ?_, heL, heT, hgen⟩⟩
  exact four_equivariant ρ (MulAut.conjNormal.comp (G₁ ⊓ G₂).subtype)
    eM d.toMonoidHom hf hs

variable {Ghat : Type u} [Group Ghat] [Finite Ghat] {K : GroupClass.{u}}

/-- The full marked identifications in the four-group branch. Only the
original SQTK cover, A.1.31(1), and the three-group branch are inputs. -/
theorem marked_models_of_cover
    (source : SectionCentralizerInput.{u,u})
    (hhat : IsSQTK K Ghat) (e : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat))
    (h : IsGoldschmidtTriple G₁ G₂) (hL : IsPGroup 3 (pResidual 2 G))
    (hn : ¬ IsCyclic (pCore 3 G))
    (hnot : ¬ Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* C2)) :
    Nonempty (MarkedModel G₁ G₂ Nine nineAction
      (MonoidHom.inl C3 C3).range (MonoidHom.inr C3 C3).range) ∨
    Nonempty (MarkedModel G₁ G₂ (HeisenbergPrime 3) heisenbergAction
      leftAxis.range rightAxis.range) := by
  have hcore : pCore 2 G = ⊥ := le_bot_iff.mp
    (twoCore_le_primeToThreeCore.trans_eq (primeToThreeCore_eq_bot_of_quotient e))
  obtain ⟨d, hm, hgen⟩ := exists_marked_complement h hcore hL hnot
  rcases residual_models_of_cover source hhat e h hcore hL hn hnot with hE | hH
  · obtain ⟨eM, hU, hV, hf, hs⟩ := exists_nine_equiv hm hE.1
    apply Or.inl
    apply assemble_model h hL nineAction _ _ eM d hU hV _ _ hgen
    · simpa only [nineAction, fourHom_first] using hf
    · simpa only [nineAction, fourHom_second] using hs
  · obtain ⟨hcard, _, ⟨j⟩⟩ := hH
    have hpow (z : pResidual 2 G) : z ^ 3 = 1 := by
      apply j.injective
      rw [map_pow, map_one]
      exact HeisenbergPrime.pow_prime (by decide) _
    obtain ⟨eM, hU, hV, hf, hs, _⟩ := exists_heisenberg_equiv hm hcard hpow
      (residual_class_two_of_cover source hhat e h hcore hL hn hnot)
    apply Or.inr
    apply assemble_model h hL heisenbergAction _ _ eM d hU hV _ _ hgen
    · simpa only [heisenbergAction_first] using hf
    · simpa only [heisenbergAction_second] using hs

/-- The complete three-group disjunction of F.6.16. The other source branch
(the proof that the residual is a three-group) remains with the parent. -/
theorem three_group_alternatives_of_cover
    (source : SectionCentralizerInput.{u,u})
    (hhat : IsSQTK K Ghat) (e : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat))
    (h : IsGoldschmidtTriple G₁ G₂) (hL : IsPGroup 3 (pResidual 2 G))
    (hn : ¬ IsCyclic (pCore 3 G)) :
    (Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* C2) ∧
      (pCore 2 G₁).map G₁.subtype = ⊥ ∧ (pCore 2 G₂).map G₂.subtype = ⊥) ∨
    Nonempty (G ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
    Nonempty (G ≃* HeisenbergExtension) := by
  classical
  by_cases htwo : Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* C2)
  · apply Or.inl
    have hc : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 2 := by
      rw [Nat.card_congr htwo.some.toEquiv]
      simp [C2]
    exact ⟨htwo, cores_eq_bot_of_intersection_card_two h hc,
      cores_eq_bot_of_intersection_card_two h.symm (by simpa only [inf_comm] using hc)⟩
  · rcases marked_models_of_cover source hhat e h hL hn htwo with hE | hH
    · obtain ⟨m⟩ := hE
      obtain ⟨s⟩ := nineExtension_equiv_symmetric_product
      exact Or.inr (Or.inl ⟨m.ambientEquiv.symm.trans s⟩)
    · obtain ⟨m⟩ := hH
      exact Or.inr (Or.inr ⟨m.ambientEquiv.symm⟩)

end CFSG.Quasithin.ChapterF.Noncyclic.MarkedRecognition
