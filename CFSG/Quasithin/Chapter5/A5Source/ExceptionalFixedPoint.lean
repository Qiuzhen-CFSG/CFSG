module
public import Theory.Representation.BinaryAlternatingFiveFixedPoint
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.ChosenSimpleAction
public import Theory.GroupTheory.DisjointConjugateCenter
public import Stellmacher.OmegaOneCenterMap
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups

/-!
# The exceptional field-four module from its source central point

A chosen Irr⁺ subgroup has a faithful irreducible action on its original
central quotient. A nonzero Borel fixed point identifies that quotient with
the orthogonal A₅ module by the five-point orbit map. The existing projective
splitting theorem then identifies the entire chosen subgroup, preserving
its actual L/O₂(L) marking and ambient conjugation action.

The Sylow-normalizer application maps the literal normalizer onto the
normalizer of its quotient Sylow. The source application constructs a
nontrivial point of V ∩ Ω₁(Z(T)); the Cartan centralizes it, and C_Z(L)=1
makes it noncentral. No module coordinates or classification conclusion is
an input. The earlier geometric assertions that the Cartan centralizes Z
and C_Z(L)=1 remain explicit, as does the original chosen T-invariance.

This proves the selected-module inference in the n=2 branch of 5.1.19,
using 5.1.18 and 5.1.14(3), rather than the full whole-layer assertion of
5.1.14(4). It feeds the original module target in 12.2.2(3d) and 13.3.2(3).
Source: Aschbacher--Smith, printed pp.638--644,795,885.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter5.A5Source
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- A point-stabilizer fixed vector on the original central quotient
constructs the full orthogonal A₅ conjugation model. -/
theorem chosen_model_of_point_fixed_quotient
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (v : D.chosenCentralQuotient) (hv0 : v ≠ 0)
    (i : Fin 5)
    (hv : ∀ b : alternatingGroup (Fin 5), b.val i = i →
      D.alternatingFiveCentralAction e b v = v) :
    Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  let σ := D.alternatingFiveCentralAction e
  have hs := D.alternatingFiveCentralAction_faithful_irreducible e
  let : σ.IsIrreducible := hs.2
  have hn : σ ≠ 1 := by
    intro hh
    apply D.centralAction_ne_one
    apply MonoidHom.ext
    intro l
    rw [← D.alternatingFiveCentralAction_mk e l]
    exact DFunLike.congr_fun hh _
  obtain ⟨f⟩ := BinaryAlternatingFiveFixedPoint.equiv_natural_of_point_fixed
    σ v hn hv0 i hv
  apply D.a5_model_of_central_quotient e f.toLinearEquiv
  intro l w
  have hh := Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap
    (e (QuotientGroup.mk' (pCore 2 L) l)) w
  rwa [D.alternatingFiveCentralAction_mk] at hh

include D in
/-- A noncentral point fixed by the literal Sylow normalizer recognizes
the original subgroup through its actual two-core projection. -/
theorem chosen_model_of_sylow_normalizer_fixed_point
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (z : V) (hnoncentral : (z : G) ∉ centralizer (L : Set G))
    (P : Sylow 2 L)
    (hfixed : ∀ l ∈ normalizer (P : Set L), Commute (l : G) (z : G)) :
    Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  let w : D.space := (D.spaceEquiv.symm z).toAdd
  let v : D.chosenCentralQuotient := Submodule.Quotient.mk w
  have hw : (w.val.toMul.val : G) = (z : G) :=
    (D.spaceEquiv_apply w).symm.trans
      (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply z))
  have hfix (l : L) (hl : Commute (l : G) (z : G)) : D.chosenAction l w = w := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (l : G) * (w.val.toMul.val : G) * (l : G)⁻¹ = (w.val.toMul.val : G)
    rw [hw, hl.eq, mul_inv_cancel_right]
  let f : L →* alternatingGroup (Fin 5) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective hf
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer Q
  have hN : (normalizer (P : Set L)).map f = MulAction.stabilizer (alternatingGroup (Fin 5)) i :=
    (P.normalizer_map_surjective f hf).trans hi
  refine chosen_model_of_point_fixed_quotient D e v ?_ i ?_
  · intro hz
    have hz' := (Submodule.Quotient.mk_eq_zero _).mp hz
    apply hnoncentral
    intro l hl
    let l' : L := ⟨l,hl⟩
    have hh : D.chosenAction l' w = w :=
      Subtype.ext (hz' ((subgroupOfEquivOfLe
        (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm l'))
    have h := congrArg (fun x : D.space => (x.val.toMul.val : G)) hh
    change l * (w.val.toMul.val : G) * l⁻¹ = (w.val.toMul.val : G) at h
    rw [hw] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  · intro b hb
    obtain ⟨l,hl,hfl⟩ := hN.ge (show b ∈ MulAction.stabilizer (alternatingGroup (Fin 5)) i from hb)
    change e (QuotientGroup.mk' (pCore 2 L) l) = b at hfl
    rw [←hfl,D.alternatingFiveCentralAction_mk]
    change Submodule.Quotient.mk (D.chosenAction l w) = Submodule.Quotient.mk w
    rw [hfix l (hfixed l hl)]

include D in
/-- The field-four source module conclusion from the Cartan centralization
in 5.1.18 and the centralizer disjointness in 5.1.14(3). The original
Sylow normalizer is generated by its Sylow group and the supplied Cartan. -/
theorem chosen_model_of_source_cartan_centralization
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (P : Sylow 2 L) (hPT : (P : Subgroup L).map L.subtype ≤ (T : Subgroup G))
    (C : Subgroup L) (hgen : normalizer (P : Set L) ≤ (P : Subgroup L) ⊔ C)
    (hC : C.map L.subtype ≤ centralizer
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (L : Set G) = ⊥) :
    Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  have hn := inf_centerIn_ne_bot T.isPGroup' D.ne_bot D.le_sylow hTV
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp hn
  have hzV : (z : G) ∈ V := z.property.1
  have hzcenter := z.property.2
  have hzΩ : (z : G) ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨D.le_sylow hzV, ?_, ?_⟩
    · let := D.elementary
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) hzV
    · intro t ht
      exact hzcenter.2 t ht
  have hnoncentral : (z : G) ∉ centralizer (L : Set G) := by
    intro hc
    have hh : (z : G) ∈ (⊥ : Subgroup G) := hZ ▸ (show
      (z : G) ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
        centralizer (L : Set G) from ⟨hzΩ,hc⟩)
    exact hz1 (Subtype.ext (mem_bot.mp hh))
  apply chosen_model_of_sylow_normalizer_fixed_point D e ⟨z,hzV⟩ hnoncentral P
  have hcentral : (P : Subgroup L) ⊔ C ≤
      (centralizer ({(z : G)} : Set G)).comap L.subtype := by
    apply sup_le
    · intro x hx
      apply mem_centralizer_singleton_iff.mpr
      exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hzΩ).2.2
        x (hPT (mem_map_of_mem L.subtype hx))
    · intro x hx
      apply mem_centralizer_singleton_iff.mpr
      exact (hC (mem_map_of_mem L.subtype hx) z hzΩ).symm
  intro l hl
  exact mem_centralizer_singleton_iff.mp (hcentral (hgen hl))

end CFSG.Quasithin.Chapter5.A5Source
