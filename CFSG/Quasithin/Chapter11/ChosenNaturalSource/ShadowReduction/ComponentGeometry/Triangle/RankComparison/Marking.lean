module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Transitivity
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison.Normalizer

/-!
# The chosen quotient marking on the same conjugate module

The source assertion C_V(L)=1 makes the original central-quotient map
bijective. Composing it with the given action equivalence marks V itself.
Transporting both V and L by the same ambient conjugation preserves the
literal quotient action. The source normalizer inclusion then gives the
full linear-normalizer action on this same conjugate of V.

The two preceding source inputs are explicit: `ComponentGeometry.fixed_trivial`
proves fixed-space vanishing, and
`Hypothesis1223.source_chosen_normalizer_le` in
`Chapter12/Section02/Preliminaries/NormalizerSource.lean` proves the normalizer
inclusion under its original structural premises. Neither input asserts
innerness or either conflicting rank bound.

Source: Aschbacher--Smith, 11.4.1(1--2), printed pp.775--776.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V)
variable {K W : Type*} [Group K] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) K W)
    (m : ActionEquiv D.centralQuotientAction σ)

/-- Once the source fixed space vanishes, the original quotient marking marks V itself. -/
def chosenModelEquiv (hfix : V ⊓ centralizer (L : Set G) = ⊥) : V ≃* Multiplicative W :=
  (MulEquiv.ofBijective D.toCentralQuotient
    ⟨centralQuotient_injective D hfix, D.toCentralQuotient_surjective⟩).trans
      m.linearEquiv.toAddEquiv.toMultiplicative

/-- The lifted marking retains the original L/O₂(L) action, not an abstract actor. -/
theorem chosenModelEquiv_action (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (l : L) (v : V) :
    (chosenModelEquiv D σ m hfix
      ⟨l.val * v.val * l.val⁻¹,
        (mem_normalizer_iff.mp (D.normalizes l.property) v.val).mp v.property⟩).toAdd =
      σ (m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l))
        (chosenModelEquiv D σ m hfix v).toAdd := by
  let w := (D.spaceEquiv.symm v).toAdd
  have hw : (w.val.toMul.val : G) = v.val :=
    (D.spaceEquiv_apply w).symm.trans
      (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v))
  have ha : D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l w)) =
      ⟨l.val * v.val * l.val⁻¹,
        (mem_normalizer_iff.mp (D.normalizes l.property) v.val).mp v.property⟩ := by
    apply Subtype.ext
    rw [D.spaceEquiv_apply]
    change l.val * (w.val.toMul.val : G) * l.val⁻¹ = _
    rw [hw]
  change m.linearEquiv (D.toCentralQuotient _).toAdd =
    σ (m.groupEquiv _) (m.linearEquiv (D.toCentralQuotient v).toAdd)
  rw [← ha,centralQuotient_chosenAction,toAdd_ofAdd,m.intertwines]
  congr 2
  exact congrArg (fun a : V => (D.toCentralQuotient a).toAdd)
    (D.spaceEquiv.apply_symm_apply v)

include D m in
/-- The entire normalizer of the same conjugate acts in the full marked linear normalizer. -/
theorem chosen_conjugate_normalizer (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hN : normalizer (V : Set G) ≤ normalizer (L : Set G)) (g : G) :
    ∃ (e : (V.map (MulAut.conj g).toMonoidHom) ≃* Multiplicative W)
      (β : normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) →* linearNormalizer σ),
      ∀ (n : normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
        (a : V.map (MulAut.conj g).toMonoidHom),
      (e ⟨n.val * a.val * n.val⁻¹,
        (mem_normalizer_iff.mp n.property a.val).mp a.property⟩).toAdd =
        normalizerRepresentation σ (β n) (e a).toAdd := by
  let eV : V ≃* V.map (MulAut.conj g).toMonoidHom := (MulAut.conj g).subgroupMap V
  let eL : L ≃* L.map (MulAut.conj g).toMonoidHom := (MulAut.conj g).subgroupMap L
  let e := eV.symm.trans (chosenModelEquiv D σ m hfix)
  let q : L.map (MulAut.conj g).toMonoidHom →* K :=
    m.groupEquiv.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 L)).comp eL.symm.toMonoidHom)
  have hq : Function.Surjective q :=
    m.groupEquiv.surjective.comp ((QuotientGroup.mk'_surjective _).comp eL.symm.surjective)
  have hLN : L.map (MulAut.conj g).toMonoidHom ≤
      normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
    rw [← map_equiv_normalizer_eq]
    exact map_mono D.normalizes
  have hNN : normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) ≤
      normalizer (L.map (MulAut.conj g).toMonoidHom : Set G) := by
    rw [← map_equiv_normalizer_eq, ← map_equiv_normalizer_eq]
    exact map_mono hN
  have hact (l : L.map (MulAut.conj g).toMonoidHom)
      (a : V.map (MulAut.conj g).toMonoidHom) :
      (e ⟨l.val * a.val * l.val⁻¹,
        (mem_normalizer_iff.mp (hLN l.property) a.val).mp a.property⟩).toAdd =
        σ (q l) (e a).toAdd := by
    obtain ⟨l,rfl⟩ := eL.surjective l
    obtain ⟨a,rfl⟩ := eV.surjective a
    have heq : (⟨(eL l).val * (eV a).val * (eL l).val⁻¹,
        (mem_normalizer_iff.mp (hLN (eL l).property) (eV a).val).mp (eV a).property⟩ :
          V.map (MulAut.conj g).toMonoidHom) =
        eV ⟨l.val * a.val * l.val⁻¹,
          (mem_normalizer_iff.mp (D.normalizes l.property) a.val).mp a.property⟩ := by
      apply Subtype.ext
      change (MulAut.conj g) l.val * (MulAut.conj g) a.val *
        ((MulAut.conj g) l.val)⁻¹ = (MulAut.conj g) (l.val * a.val * l.val⁻¹)
      simp only [map_mul,map_inv]
    rw [heq]
    simpa only [e, q, MulEquiv.trans_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, eV.symm_apply_apply, eL.symm_apply_apply] using
      chosenModelEquiv_action D σ m hfix l a
  obtain ⟨β,hβ,_⟩ := exists_marked_normalizer
    (L.map (MulAut.conj g).toMonoidHom) (V.map (MulAut.conj g).toMonoidHom)
    (normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) hLN le_rfl hNN σ q hq e hact
  exact ⟨e,β,hβ⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison
