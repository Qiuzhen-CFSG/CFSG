module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
import all CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.NaturalAction.FixedKernel
public import Theory.Representation.BinaryPermutation.FiveTensorNormalizer
public import Theory.Representation.BinaryPermutationMulAction
public import Mathlib.Algebra.Module.ZMod
public import Theory.GroupTheory.PCoreLocalSetup


/-!
# Quotient-centralizing automorphisms of an alternating-five block

An automorphism acting trivially on L/O₂(L) commutes with the marked A₅
representation on U(L)/C_U(L). The deleted five-letter binary module has
scalar commutant F₂, so this induced module automorphism is the identity.
The proved vanishing of C_U(L) then makes the automorphism fix U(L) itself.
The ambient application uses conjugation by a subgroup normalizing L;
normality of L in the whole ambient group is unnecessary.

This internal extension imports the automorphism construction privately as
well as publicly, to identify its actor with the literal core quotient map;
its implementation remains private to the chapter.

This is the module-centralizer consequence of the natural A₅ block structure
in Aschbacher–Smith C.1.13(c), printed pp.124–125. The literal commutator
criterion supplies the residual-fixation step in the ordinary diagonal
recognition argument.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC

private theorem natural_commuting_eq_one
    (f : MulAut (Multiplicative (BinaryPermutation.natural (Fin 5))))
    (hf : ∀ g : alternatingGroup (Fin 5), ∀ v,
      f (BinaryPermutation.naturalMulAction (Fin 5) g v) =
        BinaryPermutation.naturalMulAction (Fin 5) g (f v)) : f = 1 := by
  let e := (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)).toAddEquiv
  let a := AddEquiv.toMultiplicative.symm f
  let F := e.trans (a.trans e.symm)
  have he (g : Equiv.Perm (Fin 5)) (v : BinaryPermutation.core (Fin 5)) :
      e (BinaryPermutation.coreRepresentation (Fin 5) g v) =
        BinaryPermutation.naturalRepresentation (Fin 5) g (e v) :=
    BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide) g v
  have hF : ∀ g : alternatingGroup (Fin 5), ∀ v,
      F (BinaryPermutation.alternatingCoreRepresentation (Fin 5) g v) =
        BinaryPermutation.alternatingCoreRepresentation (Fin 5) g (F v) := by
    intro g v
    apply e.injective
    change e (e.symm (a (e (BinaryPermutation.coreRepresentation (Fin 5) g v)))) =
      e (BinaryPermutation.coreRepresentation (Fin 5) g (e.symm (a (e v))))
    rw [e.apply_symm_apply, he, he, e.apply_symm_apply]
    exact congrArg Multiplicative.toAdd (hf g (Multiplicative.ofAdd (e v)))
  obtain ⟨c,hc⟩ := BinaryPermutation.FiveTensorNormalizer.core_commuting_scalar
    (F.toAddMonoidHom.toZModLinearMap 2) hF
  have hid : ∀ v, F v = v := by
    have hb : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hb c with hz | ho
    · have hn : Nontrivial (BinaryPermutation.core (Fin 5)) := Module.nontrivial_of_finrank_pos
        (by rw [BinaryPermutation.finrank_core]; decide)
      obtain ⟨v,hv⟩ := exists_ne (0 : BinaryPermutation.core (Fin 5))
      have hzero : F v = F 0 := by simpa [hz] using hc v
      exact (hv (F.injective hzero)).elim
    · intro v
      simpa [ho] using hc v
  apply MulEquiv.ext
  intro v
  obtain ⟨w,hw⟩ := e.surjective v.toAdd
  have hh := congrArg e (hid w)
  change e (e.symm (a (e w))) = e w at hh
  rw [e.apply_symm_apply,hw] at hh
  exact congrArg Multiplicative.ofAdd hh

variable {L : Type*} [Group L]

/-- An automorphism trivial on the core quotient fixes the entire A₅ block layer. -/
theorem IsAlternatingBlock.automorphism_fixes_blockU_of_core_displacement
    (h : IsAlternatingBlock L 5) (α : MulAut L)
    (hd : ∀ x, α x * x⁻¹ ∈ pCore 2 L) :
    ∀ u ∈ blockU L, α u = u := by
  obtain ⟨r,⟨m⟩,hr⟩ := h.2.2
  have hr' : r = (BinaryPermutation.naturalMulAction (Fin 5)).comp
      (alternatingGroup (Fin 5)).subtype := by
    apply MonoidHom.ext
    intro g
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    exact hr g v
  subst r
  have hqa : m.quotientAction α = 1 := by
    apply MulEquiv.ext
    intro g
    obtain ⟨x,rfl⟩ := m.actor_surjective g
    rw [m.quotientAction_actor]
    change m.quotientIso (QuotientGroup.mk' (pCore 2 L) (α x)) =
      m.quotientIso (QuotientGroup.mk' (pCore 2 L) x)
    congr 1
    exact QuotientGroup.eq_iff_div_mem.mpr (by simpa only [div_eq_mul_inv] using hd x)
  have hma : m.moduleAction α = 1 := by
    apply natural_commuting_eq_one
    intro g v
    have hh := m.actions_compatible α g v
    rw [hqa] at hh
    exact hh
  have hi : Function.Injective (QuotientGroup.mk' (blockFixed L)) :=
    (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk',h.blockFixed_eq_bot])
  intro u hu
  have hh := m.moduleAction_mk α ⟨u,hu⟩
  rw [hma] at hh
  have he := hi (m.moduleIso.injective hh.symm)
  exact congrArg Subtype.val he

variable {G : Type*} [Group G]

/-- A normalizing subgroup centralizing the core quotient centralizes the block layer. -/
theorem IsAlternatingBlock.quotient_centralizer_le_blockU_centralizer
    {K Y : Subgroup G} (hK : IsAlternatingBlock K 5)
    (hYK : Y ≤ normalizer (K : Set G)) (hc : ⁅Y,K⁆ ≤ K.pCoreIn 2) :
    Y ≤ centralizer ((blockU K).map K.subtype : Set G) := by
  intro y hy u hu
  obtain ⟨v,hv,rfl⟩ := hu
  let α := K.normalizerMonoidHom ⟨y,hYK hy⟩
  have hd (x : K) : α x * x⁻¹ ∈ pCore 2 K := by
    have hx := hc (commutator_mem_commutator hy x.property)
    obtain ⟨z,hz,he⟩ := hx
    exact (Subtype.ext he : z = α x * x⁻¹) ▸ hz
  have he := congrArg (fun z : K => (z : G))
    (hK.automorphism_fixes_blockU_of_core_displacement α hd v hv)
  change y * (v : G) * y⁻¹ = (v : G) at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

end CFSG.Quasithin.ChapterC
