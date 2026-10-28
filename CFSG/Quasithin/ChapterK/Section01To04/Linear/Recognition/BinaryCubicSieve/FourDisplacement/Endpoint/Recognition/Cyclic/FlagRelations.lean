module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Recognition.Cyclic.FlagRelations.Certificate

/-!
# The incident-flag presentation of the trace kernel

Modulo point and covector additivity, all incident flags lie in the span of
the fifteen selected flags. Their literal rank-one realizations are linearly
independent. Applying realization to a linear combination in this span proves
that the quotient has no further kernel. Thus the elementary additive relations
generate every relation among the trace-zero rank-one endomorphisms.

Source: Aschbacher–Smith, K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Lemma 4.5 step 2 and Proposition 4.8 step 3A.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Cyclic

private def flagClass (a : Flag) : FreeFlags ⧸ relations :=
  relations.mkQ (Finsupp.single a 1)
private theorem flagClass_add {a b c : Flag} (h : AdditiveTriple a b c) :
    flagClass a + flagClass b = flagClass c := by
  have hr : relation a b c ∈ relations := Submodule.subset_span ⟨a, b, c, h, rfl⟩
  have hz : relations.mkQ (relation a b c) = 0 :=
    (Submodule.Quotient.mk_eq_zero relations).mpr hr
  exact sub_eq_zero.mp (by simpa only [relation, map_sub, map_add, flagClass] using hz)
private def generatorSpan : Submodule (ZMod 2) (FreeFlags ⧸ relations) :=
  Submodule.span (ZMod 2) (Set.range (flagClass ∘ spanningFlag))
private theorem flagClass_mem (a : Flag) : flagClass a ∈ generatorSpan := by
  apply flag_additive_induction (fun a => flagClass a ∈ generatorSpan) _ _ a
  · intro i
    exact Submodule.subset_span ⟨i, rfl⟩
  · intro a b c h ha hb
    rw [← flagClass_add h]
    exact generatorSpan.add_mem ha hb
private theorem mkQ_mem (z : FreeFlags) : relations.mkQ z ∈ generatorSpan := by
  induction z using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using generatorSpan.zero_mem
  | add f g hf hg =>
    rw [map_add]
    exact generatorSpan.add_mem hf hg
  | single a r =>
    rw [← Finsupp.smul_single_one, map_smul]
    exact generatorSpan.smul_mem r (flagClass_mem a)

/-- Every relation among literal rank-one incident flags follows from additivity
in the point or the covector. -/
theorem ker_realization_le_relations : LinearMap.ker realization ≤ relations := by
  intro z hz
  let f := relations.liftQ realization relations_le_ker
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp (mkQ_mem z)
  have he : ∑ i, c i • rankOne (spanningFlag i) = 0 := by
    have h := congrArg f hc
    simpa [f, Function.comp_def, flagClass, LinearMap.mem_ker.mp hz] using h
  have hc0 : ∀ i, c i = 0 :=
    (Fintype.linearIndependent_iff.mp spanningFlag_independent) c he
  apply (Submodule.Quotient.mk_eq_zero relations).mp
  change relations.mkQ z = 0
  rw [← hc]
  simp only [hc0, zero_smul, Finset.sum_const_zero]

/-- The incident-flag presentation has exactly the literal realization kernel. -/
theorem ker_realization_eq_relations : LinearMap.ker realization = relations :=
  le_antisymm ker_realization_le_relations relations_le_ker

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Cyclic
