module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Membership
public import Theory.GroupTheory.CComponent.NonsolvableNormalIntersection

/-!
# The first containing component lies in the original action kernel

A proper subnormal subgroup of a C-component is solvable. Hence a normal
subgroup containing a nonsolvable seed in that component contains the
entire component. Apply this to C_G(U) inside N_G(U), with the actual
rank-one residual L₁ as seed. Its PSL₂ quotient supplies nonsolvability.

The arbitrary-U application keeps the literal N_T(U) Sylow hypothesis.
The first flag-normalizer application also retains He membership and
relative normality. A Cartan factor faithful on V₁ consequently meets K
trivially, providing the intersection clause used in the first-index sieve.
The pointwise L₁ action and faithful Cartan input remain preceding facts
from the flag/Cartan producer; the relative-components owner retains the
remaining sieve and source assembly.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.1(i) and proof of 11.1.2 for i=1, printed pp.761--762.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G]

private theorem containing_component_centralizes
    {U A K : Subgroup G}
    (hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hAK : A ≤ K) (hA : ¬ Group.IsSolvable A)
    (hfix : A ≤ centralizer (U : Set G)) : K ≤ centralizer (U : Set G) := by
  let H := normalizer (U : Set G)
  let C := centralizer (U : Set G)
  have hCH : C ≤ H := Subgroup.centralizer_le_normalizer _
  have hAH : A ≤ H := hAK.trans hK.1
  let : (C.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hCH).mpr
      (normalizer_le_normalizer_centralizer _)
  have hA' : ¬ Group.IsSolvable (A.subgroupOf H) := by
    intro hs
    let := hs
    exact hA (Group.isSolvable_of_surjective
      (f := (subgroupOfEquivOfLe hAH).toMonoidHom)
      (subgroupOfEquivOfLe hAH).surjective)
  have hk := hK.2.le_normal_of_nonsolvable_subgroup
    (B := A.subgroupOf H) (C := C.subgroupOf H) hA'
    (comap_mono hAK) (comap_mono hfix)
  intro k h
  exact hk (show (⟨k,hK.1 h⟩ : H) ∈ K.subgroupOf H from h)

variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The component containing L₁ centralizes each source U, not merely its
normalizer quotient. Nonsolvability forces it into the normal action kernel. -/
theorem subspace_containing_component_centralizes
    (U : Subgroup G) (hUV : U ≤ f.Vi 0)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K) : K ≤ centralizer (U : Set G) :=
  containing_component_centralizes hK hLK
    (Chapter1.mem_L_not_isSolvable (flag_mem_local_of_model D S f 0 hm))
    (hfix.trans (centralizer_le hUV))

/-- The arbitrary-U containment theorem, now including its literal action
kernel. The original N_T(U) Sylow condition is unchanged. -/
theorem subspace_exists_unique_centralizing_component_of_model
    (U : Subgroup G) (hU : U ≠ ⊥) (hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G)) :
    ∃ K : Subgroup G, Source.NormalComponentIn (normalizer (U : Set G)) K ∧
      f.Li 0 ≤ K ∧ K ≤ centralizer (U : Set G) ∧
      ∀ J : Subgroup G, Source.ComponentIn (normalizer (U : Set G)) J →
        f.Li 0 ≤ J → J = K := by
  obtain ⟨K,hK,hLK,hu⟩ :=
    subspace_exists_unique_normal_component_of_model D S f U hU hUV hSyl hm hfix
  exact ⟨K,hK,hLK,subspace_containing_component_centralizes D S f U hUV hm hfix hK.1 hLK,hu⟩

/-- At the first flag normalizer the full containing component lies in G₁,
with both relative normality and He membership retained. -/
theorem first_exists_unique_centralizing_component_of_model
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G)) :
    ∃ K : Subgroup G, Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K ∧
      f.Li 0 ≤ K ∧ K ∈ Chapter1.He G ∧ K ≤ centralizer (f.Vi 0 : Set G) ∧
      ∀ J : Subgroup G, Source.ComponentIn (normalizer (f.Vi 0 : Set G)) J →
        f.Li 0 ≤ J → J = K := by
  obtain ⟨K,hK,hLK,hHe,hu⟩ := flag_exists_unique_normal_component_of_model D S f 0 hm
  exact ⟨K,hK,hLK,hHe,
    subspace_containing_component_centralizes D S f (f.Vi 0) le_rfl hm hfix hK.1 hLK,hu⟩

/-- The source Cartan factor faithful on V₁ meets the containing component
trivially. This is the intersection clause in the KX₁ semidirect product. -/
theorem first_component_disjoint_of_faithful_cartan
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X₁ : Subgroup G}
    (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥) : Disjoint K X₁ := by
  apply disjoint_iff.mpr
  rw [inf_comm]
  exact bot_unique ((inf_le_inf_left X₁
    (subspace_containing_component_centralizes D S f (f.Vi 0) le_rfl hm hfix hK hLK)).trans_eq hfaith)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
