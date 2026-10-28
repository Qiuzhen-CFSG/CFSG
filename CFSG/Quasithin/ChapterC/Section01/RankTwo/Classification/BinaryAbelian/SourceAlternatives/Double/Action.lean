module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.Reduction
public import Theory.Representation.PSL3Two.DoubledOffenders

/-!
# The actual doubled-natural action and its simultaneously marked offender

Conjugation on the elementary commutator core descends to its centralizer
quotient. Injective two-copy coordinates identify this faithful representation
with a subgroup of the full doubled linear group. Normality of the component
puts the image in the diagonal component's normalizer.

MS3 supplies a maximum elementary subgroup of the actual radical with nontrivial
image. The maximum-elementary counting theorem makes this image an offender on
the commutator core itself. Its centralizer kernel lies in the ambient two-core,
so intersection with a Sylow commutes with passing to the action image. A single
component conjugator therefore marks both the component Sylow and its unique
common-axis offender, which lies in the image of the original radical.

The original-group consumer is `MarkedMS.LinearThree.AbelianSourceDouble.Action`.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.34(2),
printed p.137; the maximum-elementary counting argument is B.2.4, pp.75–76.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open BinaryLinearThree BinaryLinearThree.DoubledOffenders
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterC.BinaryMS
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}

/-- Literal conjugation coordinates, with the component Sylow and the offender
in the radical image marked by the same component conjugator. -/
structure DoubledCoreAction (h : Input κ L R) (q : AbelianCore.NaturalQuotient h 2)
    (P : Sylow 2 J) where
  coordinates : commutatorCore L ≃* Multiplicative (Vector × Vector)
  actor : J →* D
  equivariant : ∀ (j : J) (x y : commutatorCore L),
    (y : J) = j * (x : J) * j⁻¹ →
      (coordinates y).toAdd = τ (actor j) (coordinates x).toAdd
  component : ∀ l : L, actor l = δ (q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l))
  frame : Matrix.PSL3Two.SL
  componentSylow : ((P : Subgroup J) ⊓ L).map actor =
    (Matrix.PSL3Two.borelSL.map (MulAut.conj frame).toMonoidHom).map δ
  offender_le : ((BinaryLinearThree.R.map (MulAut.conj frame).toMonoidHom).map δ) ≤ R.map actor
  unique_offender : ∀ E : Subgroup D,
    E ≤ (P : Subgroup J).map actor → IsOffender τ E →
      E = (BinaryLinearThree.R.map (MulAut.conj frame).toMonoidHom).map δ

private theorem marked_sylow (H : Subgroup D) (hCH : δ.range ≤ H) (hHN : H ≤ N)
    (P : Sylow 2 H) : ∃ g : Matrix.PSL3Two.SL,
      (P : Subgroup H).map H.subtype ⊓ δ.range =
        (Matrix.PSL3Two.borelSL.map (MulAut.conj g).toMonoidHom).map δ ∧
      ∀ E : Subgroup D, E ≤ (P : Subgroup H).map H.subtype → IsOffender τ E →
        E = (BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom).map δ := by
  obtain ⟨Q, hQ⟩ := sylow_component_intersection H hCH hHN P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Matrix.PSL3Two.SL
    Matrix.PSL3Two.SourceFlag.flagSylow Q
  have hQg : (Q : Subgroup Matrix.PSL3Two.SL) =
      Matrix.PSL3Two.borelSL.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  refine ⟨g, hQ.symm.trans (congrArg (map δ) hQg), ?_⟩
  intro E hES hE
  have hEC : E ≤ δ.range := offender_le_component hE
    (hES.trans ((map_subtype_le _).trans hHN))
  have hEQ : E.comap δ ≤ (Q : Subgroup Matrix.PSL3Two.SL) := by
    intro a ha
    have hh : δ a ∈ (Q : Subgroup Matrix.PSL3Two.SL).map δ := by
      rw [hQ]
      exact ⟨hES ha, ⟨a, rfl⟩⟩
    obtain ⟨b, hb, hba⟩ := hh
    exact δ_injective hba ▸ hb
  rw [hQg] at hEQ
  have he := (offender_borel_conjugate_iff g _ hEQ).mp (offender_comap hE hEC)
  rw [← map_comap_eq_self hEC, he]

/-- The actual two-copy core action has a simultaneously marked Sylow and
unique offender. No action, offender-existence or classification premise remains
beyond the specified natural quotient coordinates. -/
theorem Input.exists_doubledCoreAction (h : Input κ L R)
    (hc : IsMulCommutative (commutatorCore L))
    (q : AbelianCore.NaturalQuotient h 2) (hi : Function.Injective q.projection)
    (P : Sylow 2 J) (hRP : R ≤ (P : Subgroup J)) : Nonempty (DoubledCoreAction h q P) := by
  classical
  let := h.component_normal
  let := h.abelianCore_elementary_of_naturalQuotient hc q
  let V := commutatorCore L
  let C := centralizer (V : Set J)
  let π := QuotientGroup.mk' C
  have hπ : π.ker = C := QuotientGroup.ker_mk' _
  let ρ := NormalElementaryQuotient.representation V π (QuotientGroup.mk'_surjective C) hπ
  let c : V ≃* Multiplicative (Vector × Vector) :=
    (MulEquiv.ofBijective q.projection ⟨hi, q.surjective⟩).trans
      (LinearEquiv.finTwoArrow (ZMod 2) Vector).toAddEquiv.toMultiplicative
  let b : Additive V ≃ₗ[ZMod 2] (Vector × Vector) :=
    LinearEquiv.ofBijective (c.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) c.bijective
  let f : (J ⧸ C) →* D :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv b).toMonoidHom.comp ρ.asGroupHom
  have hf : Function.Injective f := by
    apply (LinearMap.GeneralLinearGroup.congrLinearEquiv b).injective.comp
    intro x y he
    exact NormalElementaryQuotient.representation_injective V π _ hπ (congrArg Units.val he)
  have hfb (g : J ⧸ C) (v : Additive V) : b (ρ g v) = τ (f g) (b v) := by
    change b (ρ g v) = b (ρ g (b.symm (b v)))
    rw [b.symm_apply_apply]
  let a : J →* D := f.comp π
  have ha (j : J) (x y : V) (he : (y : J) = j * (x : J) * j⁻¹) :
      (c y).toAdd = τ (a j) (c x).toAdd := by
    have hy : Additive.ofMul y = ρ (π j) (Additive.ofMul x) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact he.trans (NormalElementaryQuotient.representation_apply V π _ hπ j _).symm
    change b (Additive.ofMul y) = τ (f (π j)) (b (Additive.ofMul x))
    rw [hy, hfb]
  have hcomp (l : L) : a l = δ (q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨x, rfl⟩ := b.surjective v
    change τ (f (π l)) (b x) = _
    rw [← hfb]
    have hy : ρ (π l) x = Additive.ofMul (h.coreConjugate l x.toMul) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change ((ρ (π l) x).toMul : J) = (h.coreConjugate l x.toMul : J)
      rw [h.coreConjugate_val]
      exact NormalElementaryQuotient.representation_apply V π _ hπ l x
    rw [hy]
    exact Prod.ext (q.equivariant l x.toMul 0) (q.equivariant l x.toMul 1)
  have hLC : L.map a = δ.range := by
    apply le_antisymm
    · rintro _ ⟨l, hl, rfl⟩
      exact ⟨_, (hcomp ⟨l, hl⟩).symm⟩
    · rintro _ ⟨g, rfl⟩
      obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (q.quotientEquiv.symm g)
      refine ⟨l, l.property, ?_⟩
      rw [hcomp, hl, MulEquiv.apply_symm_apply]
  have hAN : a.range ≤ N := by
    change a.range ≤ normalizer (δ.range : Set D)
    rw [← hLC]
    intro d hd
    obtain ⟨j, rfl⟩ := hd
    exact L.le_normalizer_map a (mem_map_of_mem a
      (show j ∈ normalizer (L : Set J) by rw [normalizer_eq_top]; trivial))
  have hker : a.ker = C := by
    exact (MonoidHom.ker_comp_of_injective π f hf).trans hπ
  have hkP : a.ker ≤ (P : Subgroup J) := by
    rw [hker]
    exact (h.abelianCore_centralizer_le_twoCore_of_twoCopies q).trans
      (pCore_isPGroup.le_sylow_of_normal P)
  have hinter : ((P : Subgroup J) ⊓ L).map a = (P : Subgroup J).map a ⊓ δ.range := by
    rw [← hLC]
    apply le_antisymm (map_inf_le _ _ _)
    rintro _ ⟨⟨s, hs, rfl⟩, l, hl, he⟩
    have hls : l * s⁻¹ ∈ a.ker := by
      change a (l * s⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    have hlP : l ∈ (P : Subgroup J) := by
      have hh := (P : Subgroup J).mul_mem (hkP hls) hs
      simpa only [inv_mul_cancel_right] using hh
    exact ⟨l, ⟨hlP, hl⟩, he⟩
  let P' : Sylow 2 a.range := P.mapSurjective (f := a.rangeRestrict) a.rangeRestrict_surjective
  have hP' : (P' : Subgroup a.range).map a.range.subtype = (P : Subgroup J).map a := by
    rw [Sylow.coe_mapSurjective, map_map]
    rfl
  obtain ⟨g, hg, hu⟩ := marked_sylow a.range (hLC ▸ map_le_range a L) hAN P'
  rw [hP'] at hg hu
  obtain ⟨E, hE, hEn⟩ := h.exists_maxElementary_not_le_core
  have hEC : ¬ E ≤ π.ker := by
    intro he
    apply hEn
    exact (hπ ▸ he).trans (h.abelianCore_centralizer_le_twoCore_of_twoCopies q)
  have hEF : IsOffender ρ (E.map π) :=
    NormalElementaryQuotient.maxElementary_isOffender V π _ hπ R E
      ((commutator_le_left _ _).trans h.radical.twoCore_le) hE hEC
  have hEa : IsOffender τ (E.map a) := by
    rw [show E.map a = (E.map π).map f from (map_map _ _ _).symm]
    exact hEF.map_equivariant ρ τ f hf b hfb
  have hEaR : E.map a ≤ R.map a := map_mono hE.1
  have heq := hu (E.map a) (hEaR.trans (map_mono hRP)) hEa
  exact ⟨⟨c, a, ha, hcomp, g, hinter.trans hg, heq ▸ hEaR, hu⟩⟩

end CFSG.Quasithin.ChapterC.BinaryMS
