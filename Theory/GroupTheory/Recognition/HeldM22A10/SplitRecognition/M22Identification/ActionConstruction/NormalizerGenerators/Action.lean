module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.NormalizerGenerators
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.CosetAction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.IndexSubgroup

/-!+# The normalizer generators in the actual degree-22 action

The degree-21 character supplies the element-order spectrum. The independent
Sylow-normalizer argument then constructs the compatible generators required
by `PermutationData`, with the exact left-conjugation convention. Together
with the local subgroup configuration this gives the faithful, even coset
action and all its fixed-point counts, with no additional generator premise.

The character and local configuration remain explicit earlier-source inputs;
their construction belongs to the parent action-construction task.

Source: Janko (1968), Sections 8--9, pp.16--17,
DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction

universe u

/-- Construct the required action from the character and local configuration,
discharging the normalizer-generator premise using the character's spectrum. -/
public theorem nonempty_permutationData_of_character_and_localConfiguration
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hcard : Nat.card G = 443520) (C : Degree21Character G) (L : LocalConfiguration G) :
    Nonempty (PermutationData G) := by
  obtain ⟨ell, m, n, hell, hm, hn, hmell, hnm⟩ :=
    exists_normalizer_generators hcard C.element_orders
  exact ⟨{
    rho := cosetAction (L.X ⊔ L.Y) (L.generated_index C hcard)
    faithful := cosetAction_faithful (L.X ⊔ L.Y) (L.generated_index C hcard)
    even := even_of_simple (by rw [hcard]; decide) _
    order_fixed := cosetAction_order_fixed C (L.X ⊔ L.Y) (L.generated_index C hcard)
    ell := ell
    m := m
    n := n
    ell_order := hell
    m_order := hm
    n_order := hn
    m_conjugates_ell := hmell
    n_conjugates_m := hnm }⟩

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction
