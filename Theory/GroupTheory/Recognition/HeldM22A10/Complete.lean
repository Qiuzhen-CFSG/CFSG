module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.Complete
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.Complete

/-!
# Held's M22/A10 recognition theorem

For a finite simple group, the specified involution centralizer with elementary
kernel of order sixteen and symmetric-four quotient first splits. Its action
on the kernel gives the two concrete centralizer models. The Mathieu branch
constructs a faithful degree-22 action, and the alternating branch constructs
an alternating-ten overgroup. Each branch identifies the ambient group with
the corresponding concrete group.

This discharges all splitting, model, order, action and fusion inputs from
the original `LocalData` hypotheses.

Source: Huppert--Blackburn, *Finite Groups III*, XII.1.18(b), printed p.314;
D. Held, J. Algebra 8 (1968), 436--449, DOI 10.1016/0021-8693(68)90054-9;
and Held, Illinois J. Math. 13 (1969), 224--240, DOI 10.1215/ijm/1256053756.
-/

namespace Theory.GroupTheory.HeldM22A10

universe u

/-- A finite simple group satisfying Held's original involution-centralizer
hypotheses is isomorphic to M22 or A10. -/
public theorem recognition
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G] (D : LocalData G) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) ∨
      Nonempty (G ≃* alternatingGroup (Fin 10)) := by
  obtain ⟨K, hK⟩ := D.exists_kernel_complement
  rcases LocalModelDichotomy.centralizer_model_dichotomy D K hK with hm22 | ha10
  · obtain ⟨e⟩ := hm22
    exact Or.inl (m22Identification_of_centralizer D e)
  · obtain ⟨e⟩ := ha10
    exact Or.inr (a10Identification_of_centralizer D e)

end Theory.GroupTheory.HeldM22A10
